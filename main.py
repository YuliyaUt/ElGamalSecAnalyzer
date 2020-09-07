import math


# Euclid's algorithm
def gcd(a, b):
    if a == 0 or b == 0:
        return 0
    if a < 0:
        a = - a
    if b < 0:
        b = - b
    # s = q * t + r
    s, t = max(a, b), min(a, b)
    r = s % t
    while r != 0:
        s, t = t, r
        r = s % t
    return t


# using Euclid's algorithm
def inverse(a, module):
    a = a % module
    if gcd(a, module) != 1:
        return 0
    n = 1
    s, t = module, a
    q, r = s // t, s % t
    p_prev, p = 0, 1
    while r != 0:
        p_prev, p = p, p * q + p_prev
        s, t = t, r
        q, r = s // t, s % t
        n += 1
    if n % 2 == 0:
        p *= -1
    return p


def baby_step_giant_step(y, g, p):
    # Choose m - size of prebuilt table (meet-in-the-middle)
    m = int(math.sqrt(p-1)) + 1
    # Prebuild table of g^(m*i)
    table = []
    g_m = pow(g, m, p)
    gamma = g_m
    for i in range(m):
        table.append(gamma)
        gamma = (gamma * g_m) % p
    for j in range(m):
        elem = pow(g, j, p) * y % p
        if elem in table:
            # indexing in array begins with 0, so +1
            x = (table.index(elem) + 1) * m - j
            return x % (p-1)
    return 0


def find_factors(n):
    # factors are found by absolute value
    if n < 0:
        n = -n
    remains = n
    filename = "primes.txt"
    f = open(filename)
    p = int(f.readline())
    # factors are stored in dict
    factors = {}
    while p and remains > 1:
        i = 0
        while remains > 1 and remains % p == 0:
            i += 1
            remains = remains // p
        if i > 0:
            factors[p] = i
        p = int(f.readline())
    f.close()
    return factors


def pohlig_hellman_algorithm(y, g, p):
    # h = y, n = p-1, a = g
    h, n, a = y, p-1, g
    # at first going to find log_a(h) by modulo q**k:  q**k || (p-1) for all prime q | (p-1)
    factors = find_factors(n)
    print(factors)
    logarithms = {}
    if 2 in factors.keys():
        k = factors[2]
        h_i, log = h, 0
        b = []
        for i in range(k):
            if pow(h_i, n//(2**(i+1)), p) != 1:
                b_i = 1
            else:
                b_i = 0
            b.append(b_i)
            h_i = h_i * pow(inverse(a, p), (2 ** i) * b_i, p)
            h_i %= p
        for i in range(k):
            log = 2 * log + b[k-1-i]
            log = log % p
        logarithms[2] = log
    for q in factors.keys():
        if q == 2:
            # already done before
            continue
        k = factors[q]
        h_i = h
        c = []              # array with all coefficients of log_a(h) mod (q**k)
        table = {}          # table for c_i calculation
        for j in range(q):
            index = pow(a, (n*j)//q, p)
            table[index] = j
        for i in range(k):
            c_i = table[pow(h_i, n // (q ** (i+1)), p)]
            c.append(c_i)
            h_i = h_i * pow(inverse(a, p), (q ** i) * c_i, p)
            h_i %= p
        log = 0
        for i in range(k):
            log = q * log + c[k-1-i]
        logarithms[q] = log
    x = 0
    # use chinese remainder theorem to find log_a(h) mod (p-1), p-1=n
    for q in factors.keys():
        k = factors[q]
        a_q = q**k
        m_q = n // a_q
        x += logarithms[q] * m_q * inverse(m_q, a_q)
        x %= n
    return x


def pollards_rho_method(y, g, p):
    # a = g, h = y, n = p-1
    a, h, n = g % p, y % p, p-1
    h_sequence = []
    x_sequence = []
    y_sequence = []
    x_i, y_i, h_i = 0, 0, 1
    i = 0
    s_table = {}
    # cycle ends when repeated values(h_i=h_t, x_i!=x_t,...) are found
    # or numbers start to repeat (x_i=x_t,y_i=y_t)
    while 1 == 1:
        h_sequence.append(h_i)
        x_sequence.append(x_i)
        y_sequence.append(y_i)
        i += 1
        # G1
        if 0 <= h_i < p // 3:
            h_i = (h * h_i) % p
            y_i = (y_i + 1) % n
        # G2
        elif p // 3 <= h_i < 2 * p // 3:
            h_i = (h_i * h_i) % p
            x_i = (x_i * 2) % n
            y_i = (y_i * 2) % n
        # G3
        else:
            h_i = (a * h_i) % p
            x_i = (x_i + 1) % n
        tmp, m = i-1, 0
        while tmp and tmp % 2:
            tmp //= 2
            m += 1
        s_table[m] = i-1
        # print("s-table", i, s_table)
        t = -1
        for j in s_table.values():
            if h_sequence[j] == h_i:
                t = j
        if t != -1:
            # found matching value in sequence
            x_dif = (x_i - x_sequence[t]) % n
            y_dif = (y_i - y_sequence[t]) % n
            if not (x_dif and y_dif):
                return 0
            if gcd(y_dif, n) == 1:
                return (- x_dif * inverse(y_dif, n)) % n
            d = gcd(y_dif, n)
            n_0 = n // d
            log_0 = (- x_dif * inverse(y_dif, n_0)) % n_0
            print(x_dif, y_dif, d, n_0, log_0)
            for i in range(d):
                log = log_0 + i * n_0
                if pow(a, log, p) == (h % p):
                    return log % n
    pass


def test():
    y, g, p = 3, 5, 23
    print("x =", baby_step_giant_step(y, g, p))
    y, g, p = 13, 3, 17
    print("x =", baby_step_giant_step(y, g, p))
    print("first polig is", pohlig_hellman_algorithm(3, 5, 23))
    print("second polig is", pohlig_hellman_algorithm(13, 3, 17))
    print("third polig is", pohlig_hellman_algorithm(11, 3, 17))
    print("forth polig is", pohlig_hellman_algorithm(28, 2, 37))
    print(pollards_rho_method(3, 5, 23))
    print(pollards_rho_method(13, 3, 17))
    print(pollards_rho_method(5, 2, 1019))
    print("--------------------y=-1, g=5, p=67453-------------------")
    print("baby-giant:", baby_step_giant_step(-1, 5, 67453))
    print("pohlig-hellman", pohlig_hellman_algorithm(-1, 5, 67453))
    print("rho-method", pollards_rho_method(-1, 5, 67453))
    print("--------------------y=11, g=3, p=59441-------------------")
    print("baby-giant:", baby_step_giant_step(11, 3, 59441))
    print("pohlig-hellman", pohlig_hellman_algorithm(11, 3, 59441))
    print("rho-method", pollards_rho_method(11, 3, 59441))
    print("--------------------y=-1, g=3, p=715827881-------------------")
    print("baby-giant:", baby_step_giant_step(-1, 3, 715827881))
    print("pohlig-hellman", pohlig_hellman_algorithm(-1, 3, 715827881))
    print("rho-method", pollards_rho_method(-1, 3, 715827883))
    print(pow(3, 97612893, 715827883))
    print(pow(3, 184379909, 715827883))
    print("--------------------y=5, g=11, p=477224802150431------------------")
    print("pohlig-hellman", pohlig_hellman_algorithm(5, 11, 477224802150431))
    print("rho-method", pollards_rho_method(5, 11, 477224802150431))


def main():
    # y, g, p = eval(input())
    test()
    return 0


if __name__ == "__main__":
    main()
