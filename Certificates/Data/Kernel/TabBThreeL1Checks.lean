module

public import CFSG.Monster.B.Classical.E6AdjointTable
public import Certificates.Data.TabBThreeL1Levels

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabBThreeL1

open CFSG.Monster.B.Classical.E6Adjoint

@[expose] def levMask (j : ℕ) : ℕ :=
  [0x20000000000000000000, 0xae69b11883002004000, 0x28570bf1ff3f7f, 0x51964c620c40c008080,
    0x10000000000000000000].getD j 0

@[expose] def levMaskOK (M : ℕ → ℕ) : Bool :=
  (List.range 5).all (fun j => decide (M j < 2 ^ 78)) &&
    (List.range 78).all fun k => decide (lev k < 5) &&
      (List.range 5).all fun j => (M j).testBit k == (lev k == j)

@[expose] def gradedOK (br : ℕ → ℕ → ℕ) (fb : ℕ → ℕ → Bool) (a b : ℕ) : Bool :=
  (br a b == 0 || (decide (2 ≤ lev a + lev b) &&
    (br a b &&& levMask (lev a + lev b - 2) == br a b))) &&
  (!fb a b || lev a + lev b == 4)

@[expose] def gradedRows (br : ℕ → ℕ → ℕ) (fb : ℕ → ℕ → Bool) (lo n : ℕ) : Bool :=
  (List.range n).all fun i => (List.range 78).all fun b => gradedOK br fb (lo + i) b

@[expose] def pivOK (f : ℕ → ℕ → ℕ) : List (ℕ × ℕ × ℕ) → Bool
  | [] => true
  | (k, β, c) :: rest =>
    (f β k).testBit c && rest.all (fun p => !(f β p.1).testBit c) && pivOK f rest

@[expose] def certMask (P : List (ℕ × ℕ × ℕ)) : ℕ :=
  P.foldr (fun p m => 1 <<< p.1 ||| m) 0

@[expose] def testB : List ℕ := [6, 8, 9, 33]

@[expose] def adSqTestOK (B : List ℕ) : Bool :=
  B.all fun β => (List.range 78).all fun k => lev k != 1 || adSqOK β k

@[expose] def ch17575PivTheta : List (ℕ × ℕ × ℕ) :=
  [(14, 76, 74), (25, 76, 72), (36, 76, 68), (37, 76, 67), (43, 76, 64), (47, 76, 62),
    (48, 76, 61), (52, 76, 58), (56, 76, 55), (57, 76, 54), (59, 76, 50), (60, 76, 49),
    (63, 76, 45), (65, 76, 39), (66, 76, 38), (69, 76, 34), (70, 76, 27), (71, 76, 26),
    (73, 76, 15), (75, 76, 7)]

@[expose] def ch17575PivTest : List (ℕ × ℕ × ℕ) :=
  [(14, 33, 43), (25, 9, 14), (36, 8, 25), (37, 33, 59), (43, 6, 36), (47, 8, 37),
    (48, 33, 66), (52, 6, 47), (56, 9, 47), (57, 8, 48), (59, 6, 56), (60, 6, 57),
    (63, 9, 57), (65, 8, 59), (66, 6, 63), (69, 33, 75), (70, 8, 66), (71, 6, 69),
    (73, 8, 71), (75, 9, 73)]

end CFSG.HardMathSupport.Dickson.I271.TabBThreeL1
