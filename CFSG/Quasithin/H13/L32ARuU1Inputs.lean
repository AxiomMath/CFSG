module

public import CFSG.Sporadic.Schreier.RuCheckCentersInputs
public meta import CFSG.Sporadic.Schreier.RuCheckCentersInputs

public section

namespace CFSG.Quasithin.H13.KGRu

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.RuSchreier

@[expose] def ruU1Words : List (List ℤ) :=
  [[-1, 2, 2, 1, 2, 2, -1, 2, 2, 1, 2, 2],
    [-1, -1, 2, 2, 1, 1, 2, 2, -1, -1, 2, 2, 1, 1, 2, 2],
    [-2, -1, 2, 2, 1, 2, 2, 2, -2, -1, 2, 2, 1, 2, 2, 2],
    [-1, -1, 2, 2, 1, 1, -1, 2, 2, 1, -1, -1, 2, 2, 1, 1, -1, 2, 2, 1]]

@[expose] def ruCW (w : List ℤ) : Array ℕ :=
  wordA 4060 #[ruC0A, ruC1A] #[ruInv ruC0A, ruInv ruC1A] w

@[expose] def ruU1BasisA (k : ℕ) : Array ℕ := ruCW (ruU1Words.getD k [])

@[expose] def ruU1Prod (i : ℕ) : Array ℕ :=
  compA 4060 (powA 4060 ruZA (i % 2)) (compA 4060 (powA 4060 (ruU1BasisA 0) (i / 2 % 2))
    (compA 4060 (powA 4060 (ruU1BasisA 1) (i / 4 % 2))
      (compA 4060 (powA 4060 (ruU1BasisA 2) (i / 8 % 2)) (powA 4060 (ruU1BasisA 3) (i / 16 % 2)))))

@[expose] def ruU1Arr : Array (Array ℕ) := Array.ofFn (n := 32) fun i => ruU1Prod i.val

@[expose] def ruU1FArr : Array (Array ℕ) :=
  Array.ofFn (n := 32) fun i => resA ruF ruFPos ruU1Arr[i]!

@[expose] def ruU1Sig : List (List ℕ) :=
  [[0, 1, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 14, 15, 17, 16, 18, 19, 21, 20, 22, 23, 24, 25,
      27, 26, 28, 29, 31, 30],
    [0, 1, 3, 2, 4, 5, 7, 6, 9, 8, 10, 11, 13, 12, 14, 15, 16, 17, 19, 18, 20, 21, 23, 22, 25, 24,
      26, 27, 29, 28, 30, 31],
    [0, 1, 24, 25, 10, 11, 18, 19, 28, 29, 4, 5, 22, 23, 14, 15, 30, 31, 6, 7, 20, 21, 12, 13, 2,
      3, 26, 27, 8, 9, 16, 17],
    [0, 1, 24, 25, 17, 16, 9, 8, 4, 5, 28, 29, 21, 20, 13, 12, 7, 6, 31, 30, 22, 23, 14, 15, 3,
      2, 27, 26, 18, 19, 10, 11]]

@[expose] def ruU1Tau : List ℕ := [1, 25, 27, 2, 3, 24, 26]

@[expose] def ruEPi : List (List ℕ) := [[0, 2, 1, 3, 4, 6, 5], [1, 3, 4, 0, 5, 2, 6]]

@[expose] def ruOddA (k : ℕ) : List ℤ := if k = 3 then [1, 1, 2, 1, 1, 2] else [1, 1, 1, 1]

@[expose] def ruOddB (k : ℕ) : List ℤ := if k = 4 then [-2, -1, -1, -1, -1, 2] else []

@[expose] def ruOddM (k : ℕ) : ℕ := if k = 3 ∨ k = 4 then 3 else 5

@[expose] def ruOddMA (k : ℕ) : ℕ := if k = 3 then 3 else 5

@[expose] def ruOddMB (k : ℕ) : ℕ := if k = 4 then 5 else 1

@[expose] def ruCommZ1920 (g h : Array ℕ) : Bool :=
  eqA 1920 (compA 1920 g h) (compA 1920 h g) ||
    eqA 1920 (compA 1920 g h) (compA 1920 ruZF (compA 1920 h g))

@[expose] def ruU1Span (a b : ℕ) : List ℕ :=
  [0, 1, a, a ^^^ 1, b, b ^^^ 1, a ^^^ b, a ^^^ b ^^^ 1]

@[expose] def ruU1PairOK (a b : ℕ) : Bool :=
  !(decide (2 ≤ a) && decide (2 ≤ b) && decide (b ≠ a) && decide (b ≠ a ^^^ 1)) ||
    (decide (ruU1Span a b).Nodup &&
      (!(allLt 4 fun k => (ruU1Span a b).all fun w =>
          decide ((ruU1Sig.getD k []).getD w 0 ∈ ruU1Span a b)) ||
        (ruU1Span a b).all fun w => decide (w = 0 ∨ w ∈ ruU1Tau)))

end CFSG.Quasithin.H13.KGRu
