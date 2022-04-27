"""
CptS350 Algorithm Design & Analysis
Project Name: Symbolic Graph 
Student Name: Boxiang Lin
File created: 04/09/2022
"""
import typing
from pyeda.inter import *

def is_prime(val:int) -> bool:
    """ [Determines the input val is prime or not]
    Returns: bool
    """ 
    if val < 3: return False  # 2 is prime but we dont included here.
    for num in range(2, val // 2 + 1):
        if val % num == 0:
            return False 
    return True


def encode_bin(num:int, prefix:str=None) -> str:
    """[Encode the binary string to boolean formula]
    Param[0] - binary string
    param[1] - prefix for encode : optional
    Returns: encoded string
    """
    if prefix is None: prefix = 'x'   #default to x
    bin_str = format(num, '05b')
    encoded = []
    for i, c in enumerate(bin_str):
        # follow by Professor Dang's formatting where 1 is the lowest index
        idx = i + 1
        # binary either 1 or 0
        V_idx = prefix
        # if 0, start with ~
        if c == '0':V_idx = '~' + V_idx + str(idx)
        else: V_idx = V_idx + str(idx)
        encoded.append(V_idx) 
    return "&".join(encoded)


def build_edges() -> None:
    """[Collect all edges by definition an edge i->j iff (i+3)%32 == j%32 or (i+8)%32 == j%32]
    Returns: bool formulas in string
    """
    lst_edges = []
    for i in range(0, 32):
        for j in range(0, 32):
            if (i+3)%32 == j%32 or (i+8)%32 == j%32:
                # encode to x and encode to y
                end_X = encode_bin(i, 'x')
                end_Y = encode_bin(j, 'y')
                edge = end_X + '&' + end_Y
                lst_edges.append(edge)
    return '|'.join(lst_edges)

def encode_to_bool(lst:list, prefix:str) -> str:
    """
    Returns: bool formula in string
    """
    res = []
    for val in lst:
        end_val = encode_bin(val, prefix)
        res.append(end_val)
    return '|'.join(res)

def build_BDD(bool_expr) -> object:
    """[Convert bool_expr in string to Expression then convert to BDD object]
    Returns: BDD object
    """
    expression = expr(bool_expr)
    bdd = expr2bdd(expression)
    return bdd

def build_BDDcompose(bdd1:object, bdd2:object) -> object:
    """[compose y to z for BDD1, x to Z for BDD2 then smoothing all Z]
    Returns: RR2
    """
    Z = [bddvar("z1"), bddvar("z2"), bddvar("z3"), bddvar("z4"), bddvar("z5")]
    X = [bddvar("x1"), bddvar("x2"), bddvar("x3"), bddvar("x4"), bddvar("x5")]
    Y = [bddvar("y1"), bddvar("y2"), bddvar("y3"), bddvar("y4"), bddvar("y5")]
    b1 = bdd1.compose({Y[0]:Z[0], Y[1]:Z[1], Y[2]:Z[2], Y[3]:Z[3], Y[4]:Z[4]})
    b2 = bdd2.compose({X[0]:Z[0], X[1]:Z[1], X[2]:Z[2], X[3]:Z[3], X[4]:Z[4]})
    return (b1 & b2).smoothing(Z) 
    
def get_transitive_closure(bdd:object) -> object:
    """[U->V iff u -> v within m-1 steps where m = # nodes in G]
    Returns: The fixpoint BDD
    """
    H = bdd
    while True:
        Hp = H 
        H = Hp or build_BDDcompose(Hp, bdd)
        if H.equivalent(Hp):
            break 
    return H # for some n, at most n-step reachability = at most(n+1)step reachability
    
# ----------------------------------------------- TestCases -------------------------------------------- #
def testcases2(R:str, prime:str, even:str) -> None:
    """[Custom Testcases to ensure the correctness in R, prime, even boolean formula]
    """
    print("=============================================== Testcases for boolean formula ===============================================")
    # These just written by hand
    validR = "~x1&~x2&~x3&~x4&~x5&~y1&~y2&~y3&y4&y5|~x1&~x2&~x3&~x4&~x5&~y1&y2&~y3&~y4&~y5|~x1&~x2&~x3&~x4&x5&~y1&~y2&y3&~y4&~y5|~x1&~x2&~x3&~x4&x5&~y1&y2&~y3&~y4&y5|~x1&~x2&~x3&x4&~x5&~y1&~y2&y3&~y4&y5|~x1&~x2&~x3&x4&~x5&~y1&y2&~y3&y4&~y5|~x1&~x2&~x3&x4&x5&~y1&~y2&y3&y4&~y5|~x1&~x2&~x3&x4&x5&~y1&y2&~y3&y4&y5|~x1&~x2&x3&~x4&~x5&~y1&~y2&y3&y4&y5|~x1&~x2&x3&~x4&~x5&~y1&y2&y3&~y4&~y5|~x1&~x2&x3&~x4&x5&~y1&y2&~y3&~y4&~y5|~x1&~x2&x3&~x4&x5&~y1&y2&y3&~y4&y5|~x1&~x2&x3&x4&~x5&~y1&y2&~y3&~y4&y5|~x1&~x2&x3&x4&~x5&~y1&y2&y3&y4&~y5|~x1&~x2&x3&x4&x5&~y1&y2&~y3&y4&~y5|~x1&~x2&x3&x4&x5&~y1&y2&y3&y4&y5|~x1&x2&~x3&~x4&~x5&~y1&y2&~y3&y4&y5|~x1&x2&~x3&~x4&~x5&y1&~y2&~y3&~y4&~y5|~x1&x2&~x3&~x4&x5&~y1&y2&y3&~y4&~y5|~x1&x2&~x3&~x4&x5&y1&~y2&~y3&~y4&y5|~x1&x2&~x3&x4&~x5&~y1&y2&y3&~y4&y5|~x1&x2&~x3&x4&~x5&y1&~y2&~y3&y4&~y5|~x1&x2&~x3&x4&x5&~y1&y2&y3&y4&~y5|~x1&x2&~x3&x4&x5&y1&~y2&~y3&y4&y5|~x1&x2&x3&~x4&~x5&~y1&y2&y3&y4&y5|~x1&x2&x3&~x4&~x5&y1&~y2&y3&~y4&~y5|~x1&x2&x3&~x4&x5&y1&~y2&~y3&~y4&~y5|~x1&x2&x3&~x4&x5&y1&~y2&y3&~y4&y5|~x1&x2&x3&x4&~x5&y1&~y2&~y3&~y4&y5|~x1&x2&x3&x4&~x5&y1&~y2&y3&y4&~y5|~x1&x2&x3&x4&x5&y1&~y2&~y3&y4&~y5|~x1&x2&x3&x4&x5&y1&~y2&y3&y4&y5|x1&~x2&~x3&~x4&~x5&y1&~y2&~y3&y4&y5|x1&~x2&~x3&~x4&~x5&y1&y2&~y3&~y4&~y5|x1&~x2&~x3&~x4&x5&y1&~y2&y3&~y4&~y5|x1&~x2&~x3&~x4&x5&y1&y2&~y3&~y4&y5|x1&~x2&~x3&x4&~x5&y1&~y2&y3&~y4&y5|x1&~x2&~x3&x4&~x5&y1&y2&~y3&y4&~y5|x1&~x2&~x3&x4&x5&y1&~y2&y3&y4&~y5|x1&~x2&~x3&x4&x5&y1&y2&~y3&y4&y5|x1&~x2&x3&~x4&~x5&y1&~y2&y3&y4&y5|x1&~x2&x3&~x4&~x5&y1&y2&y3&~y4&~y5|x1&~x2&x3&~x4&x5&y1&y2&~y3&~y4&~y5|x1&~x2&x3&~x4&x5&y1&y2&y3&~y4&y5|x1&~x2&x3&x4&~x5&y1&y2&~y3&~y4&y5|x1&~x2&x3&x4&~x5&y1&y2&y3&y4&~y5|x1&~x2&x3&x4&x5&y1&y2&~y3&y4&~y5|x1&~x2&x3&x4&x5&y1&y2&y3&y4&y5|x1&x2&~x3&~x4&~x5&~y1&~y2&~y3&~y4&~y5|x1&x2&~x3&~x4&~x5&y1&y2&~y3&y4&y5|x1&x2&~x3&~x4&x5&~y1&~y2&~y3&~y4&y5|x1&x2&~x3&~x4&x5&y1&y2&y3&~y4&~y5|x1&x2&~x3&x4&~x5&~y1&~y2&~y3&y4&~y5|x1&x2&~x3&x4&~x5&y1&y2&y3&~y4&y5|x1&x2&~x3&x4&x5&~y1&~y2&~y3&y4&y5|x1&x2&~x3&x4&x5&y1&y2&y3&y4&~y5|x1&x2&x3&~x4&~x5&~y1&~y2&y3&~y4&~y5|x1&x2&x3&~x4&~x5&y1&y2&y3&y4&y5|x1&x2&x3&~x4&x5&~y1&~y2&~y3&~y4&~y5|x1&x2&x3&~x4&x5&~y1&~y2&y3&~y4&y5|x1&x2&x3&x4&~x5&~y1&~y2&~y3&~y4&y5|x1&x2&x3&x4&~x5&~y1&~y2&y3&y4&~y5|x1&x2&x3&x4&x5&~y1&~y2&~y3&y4&~y5|x1&x2&x3&x4&x5&~y1&~y2&y3&y4&y5"
    validPrime = "~x1&~x2&~x3&x4&x5|~x1&~x2&x3&~x4&x5|~x1&~x2&x3&x4&x5|~x1&x2&~x3&x4&x5|~x1&x2&x3&~x4&x5|x1&~x2&~x3&~x4&x5|x1&~x2&~x3&x4&x5|x1&~x2&x3&x4&x5|x1&x2&x3&~x4&x5|x1&x2&x3&x4&x5"
    validEven = "~y1&~y2&~y3&~y4&~y5|~y1&~y2&~y3&y4&~y5|~y1&~y2&y3&~y4&~y5|~y1&~y2&y3&y4&~y5|~y1&y2&~y3&~y4&~y5|~y1&y2&~y3&y4&~y5|~y1&y2&y3&~y4&~y5|~y1&y2&y3&y4&~y5|y1&~y2&~y3&~y4&~y5|y1&~y2&~y3&y4&~y5|y1&~y2&y3&~y4&~y5|y1&~y2&y3&y4&~y5|y1&y2&~y3&~y4&~y5|y1&y2&~y3&y4&~y5|y1&y2&y3&~y4&~y5|y1&y2&y3&y4&~y5"
    print("R boolean formula tested:\t {} as expected".format(validR == R))
    print("prime boolean formula tested:\t {} as expected".format(validPrime == prime))
    print("even boolean formula tested:\t {} as expected".format(validEven == even))
    print()
    print("R boolean formula:\t {}\n".format(R))
    print("prime boolean formula:\t {}\n".format(prime))
    print("even boolean formula:\t {}\n".format(even))
    
    
def testcases3_1(RR:object, PRIME:object, EVEN:object) -> None:
    """[Provided Testcases from PDF]
    """
    Rtest = [(27,3), (16,20)]
    EVENtest = [14, 13]
    PRIMEtest = [7, 2]
    print("=============================================== Testcases 3.1 for BDDs ===============================================")
    for x, y in Rtest:
        formula = encode_bin(x, 'x') + '&' + encode_bin(y, 'y')
        cur_bdd = build_BDD(formula)
        resultedBDD = cur_bdd & RR
        # AND the two BDD, if there exist a solution return True
        print("RR({}, {}) is:\t {}".format(x, y, resultedBDD.satisfy_count() > 0))    
      
    for val in EVENtest:
        formula = encode_bin(val, 'y')
        cur_bdd = build_BDD(formula)
        resultedBDD = cur_bdd & EVEN
        print("EVEN({}) is:\t {}".format(val, resultedBDD.satisfy_count() > 0))
    
    for val in PRIMEtest:
        formula = encode_bin(val, 'x')
        cur_bdd = build_BDD(formula)
        resultedBDD = cur_bdd & PRIME
        print("PRIME({}) is:\t {}".format(val, resultedBDD.satisfy_count() > 0))


def testcases3_2(RR2:object) -> None:
    print("")
    print("=============================================== Testcases 3.2 for RR2 ===============================================")
    cases = [(27,6), (27,9)]
    for x, y in cases:
        formula = encode_bin(x, 'x') + '&' + encode_bin(y, 'y')
        cur_bdd = build_BDD(formula)
        resultedBDD = cur_bdd & RR2
        print("RR2({}, {}) is:\t {}".format(x, y, resultedBDD.satisfy_count() > 0))
        

def statementA_verify(RR2star:object, PRIME:object, EVEN:object) -> None:
    """(StatementA) for each node u in [prime], there is a node v in [even] such that u can reach v
       in a positive even number of steps.
    """ 
    print("")
    print("=============================================== Verifying Statement A ===============================================")
    # for all u, (if PRIME(u) -> thee exists v such that EVEN(v) AND RR2star(u,v))
    U = [bddvar("x1"), bddvar("x2"), bddvar("x3"), bddvar("x4"), bddvar("x5")]
    V = [bddvar("y1"), bddvar("y2"), bddvar("y3"), bddvar("y4"), bddvar("y5")]
    # Professor Dang say below formula return either True or False, but the return value is in Object --> <class 'pyeda.boolalg.bdd.BDDConstant'>
    # So I just equivalent to evaluate the BDDconstant.
    ans = (~PRIME) | ((EVEN & RR2star).smoothing(V))
    print("Statement A is: {}".format(ans.equivalent(True)))
    
    
# ------------------------------------------------------------------------------------------------------- #       

def void_main()->None:

    # even and prime numbers in range [0, 31]
    evenlst = [val for val in range(0, 32) if val % 2 == 0]
    primelst = [val for val in range(0, 32) if is_prime(val)]
    
    # ======== question 2 build R, prime, even (encoded in boolean formula)
    R = build_edges()  
    prime = encode_to_bool(primelst, 'x')  # for statement A usage name prime x
    even = encode_to_bool(evenlst , 'y')   # for statement A usage name even y
    testcases2(R,prime,even)

     
    # ======== question 3.1 create BDD for R, prime, even
    RR = build_BDD(R)
    PRIME = build_BDD(prime)
    EVEN = build_BDD(even) 
    testcases3_1(RR, PRIME, EVEN)
    
    # ======== question 3.2 create RR2 
    RR2 = build_BDDcompose(RR, RR)
    testcases3_2(RR2)
    
    # ======== question 3.3 compute the transitive closure RR2star
    RR2star = get_transitive_closure(RR2)
    
    # ======== question 3.4 verify statment A
    statementA_verify(RR2star, PRIME, EVEN)

    
if __name__ == '__main__':
    void_main()
    
