module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3RowO4bAA2A

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix Pointwise

theorem s16h_H5_omegaMinusFour_stab_card {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 2 ^ 3) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {q : ℕ} (hq : q = 3 ∨ q = 7) (v : StdMod s16h_H5E3RkιA K) (hv : v ≠ 1)
    (hcase : q = 3 ∨ StatedQuadMinus 2 K b c (Multiplicative.toAdd v) ≠ 0) :
    q ∣ Nat.card ↥(natImage (StatedOmega (StatedQuadMinus 2 K b c)) ⊓
      MulAction.stabilizer (MulAut (StdMod s16h_H5E3RkιA K)) v) := by
  rcases hq with rfl | rfl
  · by_cases h0 : StatedQuadMinus 2 K b c (Multiplicative.toAdd v) = 0
    · refine s16h_H5E3_stab_dvd_singular hK hirr h0 ?_
      intro h
      exact hv (by rw [← ofAdd_toAdd v, h]; rfl)
    · exact s16h_H5E3_stab_dvd_nonsingular hK hirr (q := 3) (Or.inl rfl) h0
  · exact s16h_H5E3_stab_dvd_nonsingular hK hirr (q := 7) (Or.inr rfl)
      (hcase.resolve_left (by norm_num))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
