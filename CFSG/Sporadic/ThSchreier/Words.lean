
module

public import CFSG.Sporadic.ThSchreier.WordsBase1

public import CFSG.Sporadic.Th.Max3.AllConj

public section

namespace CFSG.Sporadic.ThSchreier

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3

theorem isRows_abLetter
    (l : ℤ) : IsRows (abLetterRows l) (pairLetters a b l) := by
  unfold abLetterRows pairLetters
  by_cases h1 : l = 1
  · simp only [h1, true_or, ite_true]
    exact isRows_a
  · by_cases h2 : l = -1
    · simp only [h2, or_true, ite_true, show (-1 : ℤ) ≠ 1 by decide, ite_false]
      rw [AllConj.a_inv]
      exact isRows_a
    · simp only [h1, h2, or_self, ite_false]
      by_cases h3 : l = 2
      · simp only [h3, ite_true]
        exact isRows_b
      · simp only [h3, ite_false]
        rw [AllConj.b_inv]
        exact isRows_b.mul isRows_b

theorem isRows_abRows
    (w : List ℤ) : IsRows (abRows w) (wordG (pairLetters a b) w) :=
  isRows_signedRows isRows_abLetter w

end CFSG.Sporadic.ThSchreier
