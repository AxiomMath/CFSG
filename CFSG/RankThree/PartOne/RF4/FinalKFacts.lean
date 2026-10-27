module

public import CFSG.RankThree.PartOne.RF4.Descent
public import CFSG.RankThree.PartTwo.KFacts.AutLargeRee

public section

namespace CFSG.RankThree.PartOne.RF4

open CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag

theorem largeReeOrderThreeFieldConj
    (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    CFSG.RankThree.PartTwo.KFacts.LargeReeOrderThreeFieldConj a K := by
  intro β hβ α hα hinn
  obtain ⟨x, hx⟩ := hinn
  refine largeRee_fieldAut_coset_conj a hK Nat.prime_three β hβ α hα ⟨x, ?_⟩
  rw [eq_mul_inv_iff_mul_eq] at hx
  rw [← hx]

end CFSG.RankThree.PartOne.RF4
