#include <iostream>
#include <fstream>
#include <cstring>
#include <string>
#include <vector>
#include <sstream>
#include <algorithm>
#include <iomanip>
#include <cmath>
#include <stack>
#include <map>
#include <set>
#include <cassert>

// ==================== File-based B+ Tree ====================

// Fixed-length string for keys
template<int LEN>
struct FixedString {
    char data[LEN];
    FixedString() { memset(data, 0, LEN); }
    FixedString(const std::string &s) {
        memset(data, 0, LEN);
        strncpy(data, s.c_str(), LEN - 1);
    }
    bool operator<(const FixedString &o) const { return strcmp(data, o.data) < 0; }
    bool operator==(const FixedString &o) const { return strcmp(data, o.data) == 0; }
    bool operator!=(const FixedString &o) const { return strcmp(data, o.data) != 0; }
    bool operator<=(const FixedString &o) const { return strcmp(data, o.data) <= 0; }
    bool operator>(const FixedString &o) const { return strcmp(data, o.data) > 0; }
    bool operator>=(const FixedString &o) const { return strcmp(data, o.data) >= 0; }
    std::string str() const { return std::string(data); }
    bool empty() const { return data[0] == '\0'; }
};

// Block-linked-list based storage for key-value pairs
// Stores (Key, Value) pairs sorted by Key
// Supports insert, erase, find, find_all (for duplicate keys with different values)

template<typename Key, typename Value>
class BlockList {
    static const int BLOCK_SIZE = 316; // tuned for performance
    struct Node {
        int cnt;
        int nxt; // next block position in file
        Key keys[BLOCK_SIZE];
        Value vals[BLOCK_SIZE];
    };

    std::fstream file;
    std::string filename;
    int head; // file position of first block
    int total_blocks;

    struct FileHeader {
        int head;
        int total_blocks;
    };

    void writeHeader() {
        file.seekp(0);
        FileHeader h{head, total_blocks};
        file.write(reinterpret_cast<char*>(&h), sizeof(h));
        file.flush();
    }

    void readHeader() {
        file.seekg(0);
        FileHeader h;
        file.read(reinterpret_cast<char*>(&h), sizeof(h));
        head = h.head;
        total_blocks = h.total_blocks;
    }

    int blockPos(int idx) {
        return sizeof(FileHeader) + idx * sizeof(Node);
    }

    void readNode(int idx, Node &node) {
        file.seekg(blockPos(idx));
        file.read(reinterpret_cast<char*>(&node), sizeof(Node));
    }

    void writeNode(int idx, const Node &node) {
        file.seekp(blockPos(idx));
        file.write(reinterpret_cast<const char*>(&node), sizeof(Node));
    }

    int newBlock() {
        return total_blocks++;
    }

    struct Pair {
        Key key;
        Value val;
        bool operator<(const Pair &o) const {
            if (key < o.key) return true;
            if (o.key < key) return false;
            return val < o.val;
        }
        bool operator==(const Pair &o) const {
            return key == o.key && val == o.val;
        }
    };

public:
    BlockList() : head(-1), total_blocks(0) {}

    void init(const std::string &fname) {
        filename = fname;
        file.open(filename, std::ios::in | std::ios::out | std::ios::binary);
        if (!file.is_open()) {
            // create new file
            file.open(filename, std::ios::out | std::ios::binary);
            file.close();
            file.open(filename, std::ios::in | std::ios::out | std::ios::binary);
            head = -1;
            total_blocks = 0;
            writeHeader();
        } else {
            readHeader();
        }
    }

    ~BlockList() {
        if (file.is_open()) file.close();
    }

    void insert(const Key &key, const Value &val) {
        if (head == -1) {
            // First block
            head = newBlock();
            Node node;
            node.cnt = 1;
            node.nxt = -1;
            node.keys[0] = key;
            node.vals[0] = val;
            writeNode(head, node);
            writeHeader();
            return;
        }

        // Find the right block
        int cur = head, prev = -1;
        Node node;
        while (cur != -1) {
            readNode(cur, node);
            // If this is the last block or key <= last key in block, insert here
            if (node.nxt == -1) break;
            Pair last{node.keys[node.cnt - 1], node.vals[node.cnt - 1]};
            Pair p{key, val};
            if (p < last || p == last) break;
            prev = cur;
            cur = node.nxt;
        }

        // Insert into this block
        readNode(cur, node); // re-read in case
        int pos = 0;
        Pair p{key, val};
        // Binary search for position
        int lo = 0, hi = node.cnt;
        while (lo < hi) {
            int mid = (lo + hi) / 2;
            Pair m{node.keys[mid], node.vals[mid]};
            if (m < p) lo = mid + 1;
            else hi = mid;
        }
        pos = lo;

        // Shift right
        for (int i = node.cnt; i > pos; --i) {
            node.keys[i] = node.keys[i - 1];
            node.vals[i] = node.vals[i - 1];
        }
        node.keys[pos] = key;
        node.vals[pos] = val;
        node.cnt++;

        // Split if too large
        if (node.cnt >= BLOCK_SIZE) {
            int mid = node.cnt / 2;
            int newIdx = newBlock();
            Node newNode;
            newNode.cnt = node.cnt - mid;
            newNode.nxt = node.nxt;
            for (int i = 0; i < newNode.cnt; ++i) {
                newNode.keys[i] = node.keys[mid + i];
                newNode.vals[i] = node.vals[mid + i];
            }
            node.cnt = mid;
            node.nxt = newIdx;
            writeNode(newIdx, newNode);
        }

        writeNode(cur, node);
        writeHeader();
    }

    void erase(const Key &key, const Value &val) {
        if (head == -1) return;

        int cur = head, prev = -1;
        Node node;
        while (cur != -1) {
            readNode(cur, node);
            Pair last{node.keys[node.cnt - 1], node.vals[node.cnt - 1]};
            Pair p{key, val};
            if (node.nxt == -1 || p < last || p == last) break;
            prev = cur;
            cur = node.nxt;
        }

        if (cur == -1) return;
        readNode(cur, node);

        // Binary search
        Pair p{key, val};
        int lo = 0, hi = node.cnt;
        while (lo < hi) {
            int mid = (lo + hi) / 2;
            Pair m{node.keys[mid], node.vals[mid]};
            if (m < p) lo = mid + 1;
            else hi = mid;
        }

        if (lo >= node.cnt) return;
        Pair found{node.keys[lo], node.vals[lo]};
        if (!(found == p)) return;

        // Shift left
        for (int i = lo; i < node.cnt - 1; ++i) {
            node.keys[i] = node.keys[i + 1];
            node.vals[i] = node.vals[i + 1];
        }
        node.cnt--;

        // Merge with next if both are small
        if (node.cnt == 0) {
            if (prev == -1) {
                head = node.nxt;
            } else {
                Node prevNode;
                readNode(prev, prevNode);
                prevNode.nxt = node.nxt;
                writeNode(prev, prevNode);
            }
        } else if (node.nxt != -1) {
            Node nextNode;
            readNode(node.nxt, nextNode);
            if (node.cnt + nextNode.cnt < BLOCK_SIZE * 2 / 3) {
                // Merge
                for (int i = 0; i < nextNode.cnt; ++i) {
                    node.keys[node.cnt + i] = nextNode.keys[i];
                    node.vals[node.cnt + i] = nextNode.vals[i];
                }
                node.cnt += nextNode.cnt;
                node.nxt = nextNode.nxt;
            }
        }

        writeNode(cur, node);
        writeHeader();
    }

    // Find all values with the given key
    std::vector<Value> find(const Key &key) {
        std::vector<Value> result;
        if (head == -1) return result;

        int cur = head;
        Node node;
        bool started = false;
        while (cur != -1) {
            readNode(cur, node);
            if (!started) {
                // Check if key could be in this block
                if (node.nxt != -1 && node.keys[node.cnt - 1] < key) {
                    cur = node.nxt;
                    continue;
                }
                started = true;
            }
            for (int i = 0; i < node.cnt; ++i) {
                if (node.keys[i] == key) {
                    result.push_back(node.vals[i]);
                } else if (key < node.keys[i]) {
                    return result;
                }
            }
            cur = node.nxt;
        }
        return result;
    }

    // Check if a specific (key, val) pair exists
    bool exists(const Key &key, const Value &val) {
        if (head == -1) return false;
        int cur = head;
        Node node;
        Pair p{key, val};
        while (cur != -1) {
            readNode(cur, node);
            if (node.nxt != -1) {
                Pair last{node.keys[node.cnt - 1], node.vals[node.cnt - 1]};
                if (p > last) {
                    cur = node.nxt;
                    continue;
                }
            }
            // Binary search
            int lo = 0, hi = node.cnt;
            while (lo < hi) {
                int mid = (lo + hi) / 2;
                Pair m{node.keys[mid], node.vals[mid]};
                if (m < p) lo = mid + 1;
                else hi = mid;
            }
            if (lo < node.cnt) {
                Pair found{node.keys[lo], node.vals[lo]};
                return found == p;
            }
            return false;
        }
        return false;
    }

    // Get all pairs (for show all books)
    std::vector<std::pair<Key, Value>> getAll() {
        std::vector<std::pair<Key, Value>> result;
        if (head == -1) return result;
        int cur = head;
        Node node;
        while (cur != -1) {
            readNode(cur, node);
            for (int i = 0; i < node.cnt; ++i) {
                result.push_back({node.keys[i], node.vals[i]});
            }
            cur = node.nxt;
        }
        return result;
    }
};

// ==================== Data Types ====================

using String30 = FixedString<32>;
using String20 = FixedString<24>;
using String60 = FixedString<64>;

struct UserInfo {
    String30 userID;
    String30 password;
    String30 username;
    int privilege;
    UserInfo() : privilege(0) {}
};

struct BookInfo {
    String20 isbn;
    String60 bookName;
    String60 author;
    String60 keyword;
    double price;
    int quantity; // stock
    BookInfo() : price(0.0), quantity(0) {}
};

struct FinanceRecord {
    double income;    // from buy
    double expense;   // from import
};

// ==================== File-based sequential storage ====================

class FinanceStorage {
    std::fstream file;
    std::string filename;
    int count;

    struct Header {
        int count;
    };

public:
    FinanceStorage() : count(0) {}

    void init(const std::string &fname) {
        filename = fname;
        file.open(filename, std::ios::in | std::ios::out | std::ios::binary);
        if (!file.is_open()) {
            file.open(filename, std::ios::out | std::ios::binary);
            file.close();
            file.open(filename, std::ios::in | std::ios::out | std::ios::binary);
            count = 0;
            Header h{0};
            file.write(reinterpret_cast<char*>(&h), sizeof(h));
            file.flush();
        } else {
            Header h;
            file.read(reinterpret_cast<char*>(&h), sizeof(h));
            count = h.count;
        }
    }

    ~FinanceStorage() {
        if (file.is_open()) file.close();
    }

    void addRecord(double income, double expense) {
        FinanceRecord rec{income, expense};
        file.seekp(sizeof(Header) + count * sizeof(FinanceRecord));
        file.write(reinterpret_cast<char*>(&rec), sizeof(rec));
        count++;
        file.seekp(0);
        Header h{count};
        file.write(reinterpret_cast<char*>(&h), sizeof(h));
        file.flush();
    }

    int getCount() const { return count; }

    // Get last n records' total income and expense
    std::pair<double, double> getLastN(int n) {
        double totalIncome = 0, totalExpense = 0;
        for (int i = count - n; i < count; ++i) {
            FinanceRecord rec;
            file.seekg(sizeof(Header) + i * sizeof(FinanceRecord));
            file.read(reinterpret_cast<char*>(&rec), sizeof(rec));
            totalIncome += rec.income;
            totalExpense += rec.expense;
        }
        return {totalIncome, totalExpense};
    }
};

// ==================== User storage using BlockList ====================

// We use a BlockList with key=UserID, value=UserInfo
// But since UserID is unique, we store it differently.
// Actually, let's use a file-based random access storage with an index.

class UserStorage {
    std::fstream file;
    std::string filename;
    int count;

    struct Header {
        int count;
    };

    int recordPos(int idx) {
        return sizeof(Header) + idx * sizeof(UserInfo);
    }

public:
    BlockList<String30, int> index; // userID -> index in file

    UserStorage() : count(0) {}

    void init(const std::string &dataFile, const std::string &indexFile) {
        filename = dataFile;
        index.init(indexFile);

        file.open(filename, std::ios::in | std::ios::out | std::ios::binary);
        if (!file.is_open()) {
            file.open(filename, std::ios::out | std::ios::binary);
            file.close();
            file.open(filename, std::ios::in | std::ios::out | std::ios::binary);
            count = 0;
            Header h{0};
            file.write(reinterpret_cast<char*>(&h), sizeof(h));
            file.flush();
        } else {
            Header h;
            file.read(reinterpret_cast<char*>(&h), sizeof(h));
            count = h.count;
        }
    }

    ~UserStorage() {
        if (file.is_open()) file.close();
    }

    bool exists(const std::string &userID) {
        auto res = index.find(String30(userID));
        return !res.empty();
    }

    int addUser(const UserInfo &info) {
        int idx = count++;
        file.seekp(0);
        Header h{count};
        file.write(reinterpret_cast<char*>(&h), sizeof(h));
        file.seekp(recordPos(idx));
        file.write(reinterpret_cast<const char*>(&info), sizeof(UserInfo));
        file.flush();
        index.insert(info.userID, idx);
        return idx;
    }

    bool getUser(const std::string &userID, UserInfo &info) {
        auto res = index.find(String30(userID));
        if (res.empty()) return false;
        file.seekg(recordPos(res[0]));
        file.read(reinterpret_cast<char*>(&info), sizeof(UserInfo));
        return true;
    }

    void updateUser(const std::string &userID, const UserInfo &info) {
        auto res = index.find(String30(userID));
        if (res.empty()) return;
        file.seekp(recordPos(res[0]));
        file.write(reinterpret_cast<const char*>(&info), sizeof(UserInfo));
        file.flush();
    }

    void deleteUser(const std::string &userID) {
        auto res = index.find(String30(userID));
        if (res.empty()) return;
        index.erase(String30(userID), res[0]);
        // Don't actually remove from file, just remove from index
    }
};

// ==================== Book storage ====================

class BookStorage {
    std::fstream file;
    std::string filename;
    int count;

    struct Header {
        int count;
    };

    int recordPos(int idx) {
        return sizeof(Header) + idx * sizeof(BookInfo);
    }

public:
    BlockList<String20, int> isbnIndex;      // isbn -> file index
    BlockList<String60, int> nameIndex;      // name -> file index
    BlockList<String60, int> authorIndex;    // author -> file index
    BlockList<String60, int> keywordIndex;   // single keyword -> file index

    BookStorage() : count(0) {}

    void init(const std::string &dataFile, const std::string &isbnIdx,
              const std::string &nameIdx, const std::string &authorIdx,
              const std::string &kwIdx) {
        filename = dataFile;
        isbnIndex.init(isbnIdx);
        nameIndex.init(nameIdx);
        authorIndex.init(authorIdx);
        keywordIndex.init(kwIdx);

        file.open(filename, std::ios::in | std::ios::out | std::ios::binary);
        if (!file.is_open()) {
            file.open(filename, std::ios::out | std::ios::binary);
            file.close();
            file.open(filename, std::ios::in | std::ios::out | std::ios::binary);
            count = 0;
            Header h{0};
            file.write(reinterpret_cast<char*>(&h), sizeof(h));
            file.flush();
        } else {
            Header h;
            file.read(reinterpret_cast<char*>(&h), sizeof(h));
            count = h.count;
        }
    }

    ~BookStorage() {
        if (file.is_open()) file.close();
    }

    bool existsISBN(const std::string &isbn) {
        auto res = isbnIndex.find(String20(isbn));
        return !res.empty();
    }

    int getBookIdx(const std::string &isbn) {
        auto res = isbnIndex.find(String20(isbn));
        if (res.empty()) return -1;
        return res[0];
    }

    BookInfo getBook(int idx) {
        BookInfo info;
        file.seekg(recordPos(idx));
        file.read(reinterpret_cast<char*>(&info), sizeof(BookInfo));
        return info;
    }

    bool getBookByISBN(const std::string &isbn, BookInfo &info) {
        int idx = getBookIdx(isbn);
        if (idx == -1) return false;
        info = getBook(idx);
        return true;
    }

    void updateBook(int idx, const BookInfo &info) {
        file.seekp(recordPos(idx));
        file.write(reinterpret_cast<const char*>(&info), sizeof(BookInfo));
        file.flush();
    }

    // Parse keywords string into individual keywords
    static std::vector<std::string> parseKeywords(const std::string &kw) {
        std::vector<std::string> result;
        if (kw.empty()) return result;
        std::string cur;
        for (char c : kw) {
            if (c == '|') {
                if (!cur.empty()) result.push_back(cur);
                cur.clear();
            } else {
                cur += c;
            }
        }
        if (!cur.empty()) result.push_back(cur);
        return result;
    }

    int addBook(const BookInfo &info) {
        int idx = count++;
        file.seekp(0);
        Header h{count};
        file.write(reinterpret_cast<char*>(&h), sizeof(h));
        file.seekp(recordPos(idx));
        file.write(reinterpret_cast<const char*>(&info), sizeof(BookInfo));
        file.flush();

        isbnIndex.insert(info.isbn, idx);
        if (!info.bookName.empty())
            nameIndex.insert(info.bookName, idx);
        if (!info.author.empty())
            authorIndex.insert(info.author, idx);

        auto kws = parseKeywords(info.keyword.str());
        for (auto &kw : kws) {
            keywordIndex.insert(String60(kw), idx);
        }

        return idx;
    }

    // Remove old indices and add new ones when modifying a book
    void removeIndices(int idx, const BookInfo &old) {
        isbnIndex.erase(old.isbn, idx);
        if (!old.bookName.empty())
            nameIndex.erase(old.bookName, idx);
        if (!old.author.empty())
            authorIndex.erase(old.author, idx);
        auto kws = parseKeywords(old.keyword.str());
        for (auto &kw : kws) {
            keywordIndex.erase(String60(kw), idx);
        }
    }

    void addIndices(int idx, const BookInfo &info) {
        isbnIndex.insert(info.isbn, idx);
        if (!info.bookName.empty())
            nameIndex.insert(info.bookName, idx);
        if (!info.author.empty())
            authorIndex.insert(info.author, idx);
        auto kws = parseKeywords(info.keyword.str());
        for (auto &kw : kws) {
            keywordIndex.insert(String60(kw), idx);
        }
    }

    std::vector<int> findByName(const std::string &name) {
        return nameIndex.find(String60(name));
    }

    std::vector<int> findByAuthor(const std::string &author) {
        return authorIndex.find(String60(author));
    }

    std::vector<int> findByKeyword(const std::string &keyword) {
        return keywordIndex.find(String60(keyword));
    }

    std::vector<int> findByISBN(const std::string &isbn) {
        return isbnIndex.find(String20(isbn));
    }

    // Get all books sorted by ISBN
    std::vector<BookInfo> getAllBooks() {
        auto pairs = isbnIndex.getAll();
        std::vector<BookInfo> result;
        for (auto &p : pairs) {
            result.push_back(getBook(p.second));
        }
        return result;
    }

    // Get books by indices, sorted by ISBN
    std::vector<BookInfo> getBooksByIndices(const std::vector<int> &indices) {
        std::vector<BookInfo> books;
        for (int idx : indices) {
            books.push_back(getBook(idx));
        }
        std::sort(books.begin(), books.end(), [](const BookInfo &a, const BookInfo &b) {
            return a.isbn < b.isbn;
        });
        return books;
    }
};

// ==================== Validation Helpers ====================

bool isAlphaNumUnderscore(const std::string &s) {
    if (s.empty()) return false;
    for (char c : s) {
        if (!isalnum(c) && c != '_') return false;
    }
    return true;
}

bool isVisible(const std::string &s) {
    if (s.empty()) return false;
    for (unsigned char c : s) {
        if (c <= 32 || c >= 127) return false;
    }
    return true;
}

bool isVisibleNoQuote(const std::string &s) {
    if (s.empty()) return false;
    for (unsigned char c : s) {
        if (c <= 32 || c >= 127 || c == '"') return false;
    }
    return true;
}

bool isDigitsOnly(const std::string &s) {
    if (s.empty()) return false;
    for (char c : s) {
        if (!isdigit(c)) return false;
    }
    return true;
}

bool isValidPrice(const std::string &s) {
    if (s.empty() || s.size() > 13) return false;
    // Must be digits and at most one dot
    int dots = 0;
    bool hasDigit = false;
    for (char c : s) {
        if (c == '.') dots++;
        else if (!isdigit(c)) return false;
        else hasDigit = true;
    }
    if (dots > 1) return false;
    if (!hasDigit) return false;
    // Cannot start or end with dot alone
    if (s[0] == '.' || s.back() == '.') return false;
    return true;
}

bool isValidQuantity(const std::string &s) {
    if (s.empty() || s.size() > 10) return false;
    if (!isDigitsOnly(s)) return false;
    // Value must not exceed 2,147,483,647
    if (s.size() == 10) {
        if (s > "2147483647") return false;
    }
    return true;
}

bool isPositiveInt(const std::string &s) {
    if (!isValidQuantity(s)) return false;
    // Must be > 0
    for (char c : s) {
        if (c != '0') return true;
    }
    return false; // all zeros
}

double parsePrice(const std::string &s) {
    return std::stod(s);
}

bool isPositivePrice(const std::string &s) {
    if (!isValidPrice(s)) return false;
    double v = parsePrice(s);
    return v > 0;
}

// ==================== Command Parser ====================

std::vector<std::string> tokenize(const std::string &line) {
    std::vector<std::string> tokens;
    std::istringstream iss(line);
    std::string token;
    while (iss >> token) {
        tokens.push_back(token);
    }
    return tokens;
}

// ==================== Global State ====================

UserStorage userStore;
BookStorage bookStore;
FinanceStorage financeStore;

struct LoginEntry {
    std::string userID;
    int privilege;
    int selectedBookIdx; // -1 if no book selected
};

std::vector<LoginEntry> loginStack;

int currentPrivilege() {
    if (loginStack.empty()) return 0;
    return loginStack.back().privilege;
}

std::string currentUserID() {
    if (loginStack.empty()) return "";
    return loginStack.back().userID;
}

int& currentSelectedBook() {
    static int dummy = -1;
    if (loginStack.empty()) return dummy;
    return loginStack.back().selectedBookIdx;
}

// ==================== Command Handlers ====================

void printInvalid() {
    std::cout << "Invalid\n";
}

void printBook(const BookInfo &book) {
    std::cout << book.isbn.str() << "\t"
              << book.bookName.str() << "\t"
              << book.author.str() << "\t"
              << book.keyword.str() << "\t"
              << std::fixed << std::setprecision(2) << book.price << "\t"
              << book.quantity << "\n";
}

void cmdSu(const std::vector<std::string> &tokens) {
    // su [UserID] ([Password])?
    if (tokens.size() < 2 || tokens.size() > 3) { printInvalid(); return; }

    std::string userID = tokens[1];
    if (userID.size() > 30 || !isAlphaNumUnderscore(userID)) { printInvalid(); return; }

    UserInfo info;
    if (!userStore.getUser(userID, info)) { printInvalid(); return; }

    if (tokens.size() == 3) {
        std::string password = tokens[2];
        if (password.size() > 30 || !isAlphaNumUnderscore(password)) { printInvalid(); return; }
        if (password != info.password.str()) { printInvalid(); return; }
    } else {
        // Password omitted: current privilege must be higher
        if (currentPrivilege() <= info.privilege) { printInvalid(); return; }
    }

    loginStack.push_back({userID, info.privilege, -1});
}

void cmdLogout(const std::vector<std::string> &tokens) {
    if (tokens.size() != 1) { printInvalid(); return; }
    if (loginStack.empty()) { printInvalid(); return; }
    loginStack.pop_back();
}

void cmdRegister(const std::vector<std::string> &tokens) {
    // register [UserID] [Password] [Username]
    if (tokens.size() != 4) { printInvalid(); return; }

    std::string userID = tokens[1];
    std::string password = tokens[2];
    std::string username = tokens[3];

    if (userID.size() > 30 || !isAlphaNumUnderscore(userID)) { printInvalid(); return; }
    if (password.size() > 30 || !isAlphaNumUnderscore(password)) { printInvalid(); return; }
    if (username.size() > 30 || !isVisible(username)) { printInvalid(); return; }

    if (userStore.exists(userID)) { printInvalid(); return; }

    UserInfo info;
    info.userID = String30(userID);
    info.password = String30(password);
    info.username = String30(username);
    info.privilege = 1;
    userStore.addUser(info);
}

void cmdPasswd(const std::vector<std::string> &tokens) {
    // passwd [UserID] ([CurrentPassword])? [NewPassword]
    if (tokens.size() < 3 || tokens.size() > 4) { printInvalid(); return; }
    if (currentPrivilege() < 1) { printInvalid(); return; }

    std::string userID = tokens[1];
    if (userID.size() > 30 || !isAlphaNumUnderscore(userID)) { printInvalid(); return; }

    UserInfo info;
    if (!userStore.getUser(userID, info)) { printInvalid(); return; }

    if (tokens.size() == 4) {
        std::string currentPwd = tokens[2];
        std::string newPwd = tokens[3];
        if (currentPwd.size() > 30 || !isAlphaNumUnderscore(currentPwd)) { printInvalid(); return; }
        if (newPwd.size() > 30 || !isAlphaNumUnderscore(newPwd)) { printInvalid(); return; }
        if (currentPwd != info.password.str()) { printInvalid(); return; }
        info.password = String30(newPwd);
    } else {
        // 3 tokens: passwd [UserID] [NewPassword]
        // CurrentPassword omitted, must be privilege 7
        if (currentPrivilege() != 7) { printInvalid(); return; }
        std::string newPwd = tokens[2];
        if (newPwd.size() > 30 || !isAlphaNumUnderscore(newPwd)) { printInvalid(); return; }
        info.password = String30(newPwd);
    }

    userStore.updateUser(userID, info);
}

void cmdUseradd(const std::vector<std::string> &tokens) {
    // useradd [UserID] [Password] [Privilege] [Username]
    if (tokens.size() != 5) { printInvalid(); return; }
    if (currentPrivilege() < 3) { printInvalid(); return; }

    std::string userID = tokens[1];
    std::string password = tokens[2];
    std::string privStr = tokens[3];
    std::string username = tokens[4];

    if (userID.size() > 30 || !isAlphaNumUnderscore(userID)) { printInvalid(); return; }
    if (password.size() > 30 || !isAlphaNumUnderscore(password)) { printInvalid(); return; }
    if (privStr.size() != 1 || !isdigit(privStr[0])) { printInvalid(); return; }
    if (username.size() > 30 || !isVisible(username)) { printInvalid(); return; }

    int priv = privStr[0] - '0';
    // Only valid privilege levels: 1, 3, 7
    if (priv != 1 && priv != 3 && priv != 7) { printInvalid(); return; }
    // Must be strictly less than current privilege
    if (priv >= currentPrivilege()) { printInvalid(); return; }

    if (userStore.exists(userID)) { printInvalid(); return; }

    UserInfo info;
    info.userID = String30(userID);
    info.password = String30(password);
    info.username = String30(username);
    info.privilege = priv;
    userStore.addUser(info);
}

void cmdDelete(const std::vector<std::string> &tokens) {
    // delete [UserID]
    if (tokens.size() != 2) { printInvalid(); return; }
    if (currentPrivilege() < 7) { printInvalid(); return; }

    std::string userID = tokens[1];
    if (userID.size() > 30 || !isAlphaNumUnderscore(userID)) { printInvalid(); return; }

    if (!userStore.exists(userID)) { printInvalid(); return; }

    // Check if logged in
    for (auto &entry : loginStack) {
        if (entry.userID == userID) { printInvalid(); return; }
    }

    userStore.deleteUser(userID);
}

void cmdShow(const std::vector<std::string> &tokens) {
    // show (-ISBN=[ISBN] | -name="[BookName]" | -author="[Author]" | -keyword="[Keyword]")?
    if (currentPrivilege() < 1) { printInvalid(); return; }

    if (tokens.size() == 1) {
        // Show all books
        auto books = bookStore.getAllBooks();
        if (books.empty()) {
            std::cout << "\n";
        } else {
            for (auto &book : books) printBook(book);
        }
        return;
    }

    if (tokens.size() != 2) { printInvalid(); return; }

    std::string param = tokens[1];

    if (param.substr(0, 6) == "-ISBN=") {
        std::string isbn = param.substr(6);
        if (isbn.empty() || isbn.size() > 20 || !isVisible(isbn)) { printInvalid(); return; }
        auto indices = bookStore.findByISBN(isbn);
        if (indices.empty()) {
            std::cout << "\n";
        } else {
            auto books = bookStore.getBooksByIndices(indices);
            for (auto &book : books) printBook(book);
        }
    } else if (param.size() > 7 && param.substr(0, 7) == "-name=\"" && param.back() == '"') {
        std::string name = param.substr(7, param.size() - 8);
        if (name.empty() || name.size() > 60 || !isVisibleNoQuote(name)) { printInvalid(); return; }
        auto indices = bookStore.findByName(name);
        if (indices.empty()) {
            std::cout << "\n";
        } else {
            auto books = bookStore.getBooksByIndices(indices);
            for (auto &book : books) printBook(book);
        }
    } else if (param.size() > 9 && param.substr(0, 9) == "-author=\"" && param.back() == '"') {
        std::string author = param.substr(9, param.size() - 10);
        if (author.empty() || author.size() > 60 || !isVisibleNoQuote(author)) { printInvalid(); return; }
        auto indices = bookStore.findByAuthor(author);
        if (indices.empty()) {
            std::cout << "\n";
        } else {
            auto books = bookStore.getBooksByIndices(indices);
            for (auto &book : books) printBook(book);
        }
    } else if (param.size() > 10 && param.substr(0, 10) == "-keyword=\"" && param.back() == '"') {
        std::string keyword = param.substr(10, param.size() - 11);
        if (keyword.empty() || keyword.size() > 60 || !isVisibleNoQuote(keyword)) { printInvalid(); return; }
        // Must be single keyword (no |)
        if (keyword.find('|') != std::string::npos) { printInvalid(); return; }
        auto indices = bookStore.findByKeyword(keyword);
        if (indices.empty()) {
            std::cout << "\n";
        } else {
            auto books = bookStore.getBooksByIndices(indices);
            for (auto &book : books) printBook(book);
        }
    } else {
        printInvalid();
    }
}

void cmdBuy(const std::vector<std::string> &tokens) {
    // buy [ISBN] [Quantity]
    if (tokens.size() != 3) { printInvalid(); return; }
    if (currentPrivilege() < 1) { printInvalid(); return; }

    std::string isbn = tokens[1];
    std::string qtyStr = tokens[2];

    if (isbn.empty() || isbn.size() > 20 || !isVisible(isbn)) { printInvalid(); return; }
    if (!isPositiveInt(qtyStr)) { printInvalid(); return; }

    int qty = std::stoi(qtyStr);

    BookInfo info;
    if (!bookStore.getBookByISBN(isbn, info)) { printInvalid(); return; }

    if (info.quantity < qty) { printInvalid(); return; }

    info.quantity -= qty;
    int idx = bookStore.getBookIdx(isbn);
    bookStore.updateBook(idx, info);

    double total = info.price * qty;
    std::cout << std::fixed << std::setprecision(2) << total << "\n";

    financeStore.addRecord(total, 0);
}

void cmdSelect(const std::vector<std::string> &tokens) {
    // select [ISBN]
    if (tokens.size() != 2) { printInvalid(); return; }
    if (currentPrivilege() < 3) { printInvalid(); return; }

    std::string isbn = tokens[1];
    if (isbn.empty() || isbn.size() > 20 || !isVisible(isbn)) { printInvalid(); return; }

    int idx = bookStore.getBookIdx(isbn);
    if (idx == -1) {
        // Create new book with only ISBN
        BookInfo info;
        info.isbn = String20(isbn);
        idx = bookStore.addBook(info);
    }
    currentSelectedBook() = idx;
}

void cmdModify(const std::vector<std::string> &tokens) {
    // modify (-ISBN=[ISBN] | -name="[BookName]" | -author="[Author]" | -keyword="[Keyword]" | -price=[Price])+
    if (tokens.size() < 2) { printInvalid(); return; }
    if (currentPrivilege() < 3) { printInvalid(); return; }
    if (currentSelectedBook() == -1) { printInvalid(); return; }

    int idx = currentSelectedBook();
    BookInfo old = bookStore.getBook(idx);

    bool hasISBN = false, hasName = false, hasAuthor = false, hasKeyword = false, hasPrice = false;
    std::string newISBN, newName, newAuthor, newKeyword;
    double newPrice = 0;

    for (size_t i = 1; i < tokens.size(); ++i) {
        const std::string &param = tokens[i];

        if (param.substr(0, 6) == "-ISBN=") {
            if (hasISBN) { printInvalid(); return; }
            hasISBN = true;
            newISBN = param.substr(6);
            if (newISBN.empty() || newISBN.size() > 20 || !isVisible(newISBN)) { printInvalid(); return; }
        } else if (param.size() > 7 && param.substr(0, 7) == "-name=\"" && param.back() == '"') {
            if (hasName) { printInvalid(); return; }
            hasName = true;
            newName = param.substr(7, param.size() - 8);
            if (newName.empty() || newName.size() > 60 || !isVisibleNoQuote(newName)) { printInvalid(); return; }
        } else if (param.size() > 9 && param.substr(0, 9) == "-author=\"" && param.back() == '"') {
            if (hasAuthor) { printInvalid(); return; }
            hasAuthor = true;
            newAuthor = param.substr(9, param.size() - 10);
            if (newAuthor.empty() || newAuthor.size() > 60 || !isVisibleNoQuote(newAuthor)) { printInvalid(); return; }
        } else if (param.size() > 10 && param.substr(0, 10) == "-keyword=\"" && param.back() == '"') {
            if (hasKeyword) { printInvalid(); return; }
            hasKeyword = true;
            newKeyword = param.substr(10, param.size() - 11);
            if (newKeyword.empty() || newKeyword.size() > 60 || !isVisibleNoQuote(newKeyword)) { printInvalid(); return; }
            // Check for duplicate segments
            auto kws = BookStorage::parseKeywords(newKeyword);
            std::set<std::string> kwSet(kws.begin(), kws.end());
            if (kwSet.size() != kws.size()) { printInvalid(); return; }
            // Each segment must have length >= 1 (already guaranteed by parseKeywords)
            // But check for empty segments from consecutive |
            for (size_t j = 0; j < newKeyword.size(); ++j) {
                if (newKeyword[j] == '|') {
                    if (j == 0 || j == newKeyword.size() - 1) { printInvalid(); return; }
                    if (newKeyword[j - 1] == '|') { printInvalid(); return; }
                }
            }
        } else if (param.substr(0, 7) == "-price=") {
            if (hasPrice) { printInvalid(); return; }
            hasPrice = true;
            std::string priceStr = param.substr(7);
            if (!isValidPrice(priceStr)) { printInvalid(); return; }
            newPrice = parsePrice(priceStr);
        } else {
            printInvalid(); return;
        }
    }

    // Cannot change ISBN to its original ISBN
    if (hasISBN && newISBN == old.isbn.str()) { printInvalid(); return; }
    // Cannot change ISBN to another existing ISBN
    if (hasISBN && bookStore.existsISBN(newISBN)) { printInvalid(); return; }

    // Remove old indices
    bookStore.removeIndices(idx, old);

    // Apply modifications
    BookInfo updated = old;
    if (hasISBN) updated.isbn = String20(newISBN);
    if (hasName) updated.bookName = String60(newName);
    if (hasAuthor) updated.author = String60(newAuthor);
    if (hasKeyword) updated.keyword = String60(newKeyword);
    if (hasPrice) updated.price = newPrice;

    // Update book data and re-add indices
    bookStore.updateBook(idx, updated);
    bookStore.addIndices(idx, updated);
}

void cmdImport(const std::vector<std::string> &tokens) {
    // import [Quantity] [TotalCost]
    if (tokens.size() != 3) { printInvalid(); return; }
    if (currentPrivilege() < 3) { printInvalid(); return; }
    if (currentSelectedBook() == -1) { printInvalid(); return; }

    std::string qtyStr = tokens[1];
    std::string costStr = tokens[2];

    if (!isPositiveInt(qtyStr)) { printInvalid(); return; }
    if (!isPositivePrice(costStr)) { printInvalid(); return; }

    int qty = std::stoi(qtyStr);
    double cost = parsePrice(costStr);

    int idx = currentSelectedBook();
    BookInfo info = bookStore.getBook(idx);
    info.quantity += qty;
    bookStore.updateBook(idx, info);

    financeStore.addRecord(0, cost);
}

void cmdShowFinance(const std::vector<std::string> &tokens) {
    // show finance ([Count])?
    if (currentPrivilege() < 7) { printInvalid(); return; }

    if (tokens.size() == 2) {
        // show finance - all transactions
        auto [income, expense] = financeStore.getLastN(financeStore.getCount());
        std::cout << "+ " << std::fixed << std::setprecision(2) << income
                  << " - " << std::fixed << std::setprecision(2) << expense << "\n";
    } else if (tokens.size() == 3) {
        std::string countStr = tokens[2];
        if (!isValidQuantity(countStr)) { printInvalid(); return; }
        int count = std::stoi(countStr);
        if (count == 0) {
            std::cout << "\n";
            return;
        }
        if (count > financeStore.getCount()) { printInvalid(); return; }
        auto [income, expense] = financeStore.getLastN(count);
        std::cout << "+ " << std::fixed << std::setprecision(2) << income
                  << " - " << std::fixed << std::setprecision(2) << expense << "\n";
    } else {
        printInvalid();
    }
}

void cmdLog(const std::vector<std::string> &tokens) {
    if (tokens.size() != 1) { printInvalid(); return; }
    if (currentPrivilege() < 7) { printInvalid(); return; }
    std::cout << "\n";
}

void cmdReportFinance(const std::vector<std::string> &tokens) {
    if (tokens.size() != 2) { printInvalid(); return; }
    if (currentPrivilege() < 7) { printInvalid(); return; }
    std::cout << "\n";
}

void cmdReportEmployee(const std::vector<std::string> &tokens) {
    if (tokens.size() != 2) { printInvalid(); return; }
    if (currentPrivilege() < 7) { printInvalid(); return; }
    std::cout << "\n";
}

// ==================== Main ====================

int main() {
    std::ios::sync_with_stdio(false);
    std::cin.tie(nullptr);

    // Initialize storage
    userStore.init("user_data.dat", "user_index.dat");
    bookStore.init("book_data.dat", "book_isbn.dat", "book_name.dat", "book_author.dat", "book_kw.dat");
    financeStore.init("finance.dat");

    // Create root account if it doesn't exist
    if (!userStore.exists("root")) {
        UserInfo root;
        root.userID = String30("root");
        root.password = String30("sjtu");
        root.username = String30("root");
        root.privilege = 7;
        userStore.addUser(root);
    }

    std::string line;
    while (std::getline(std::cin, line)) {
        auto tokens = tokenize(line);
        if (tokens.empty()) continue; // blank line, legal, no output

        const std::string &cmd = tokens[0];

        if (cmd == "quit" || cmd == "exit") {
            if (tokens.size() != 1) { printInvalid(); continue; }
            break;
        } else if (cmd == "su") {
            cmdSu(tokens);
        } else if (cmd == "logout") {
            cmdLogout(tokens);
        } else if (cmd == "register") {
            cmdRegister(tokens);
        } else if (cmd == "passwd") {
            cmdPasswd(tokens);
        } else if (cmd == "useradd") {
            cmdUseradd(tokens);
        } else if (cmd == "delete") {
            cmdDelete(tokens);
        } else if (cmd == "show") {
            if (tokens.size() >= 2 && tokens[1] == "finance") {
                cmdShowFinance(tokens);
            } else {
                cmdShow(tokens);
            }
        } else if (cmd == "buy") {
            cmdBuy(tokens);
        } else if (cmd == "select") {
            cmdSelect(tokens);
        } else if (cmd == "modify") {
            cmdModify(tokens);
        } else if (cmd == "import") {
            cmdImport(tokens);
        } else if (cmd == "log") {
            cmdLog(tokens);
        } else if (cmd == "report") {
            if (tokens.size() >= 2 && tokens[1] == "finance") {
                cmdReportFinance(tokens);
            } else if (tokens.size() >= 2 && tokens[1] == "employee") {
                cmdReportEmployee(tokens);
            } else {
                printInvalid();
            }
        } else {
            printInvalid();
        }
    }

    return 0;
}
