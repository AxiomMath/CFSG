module

public import CFSG.LocalAnalysis.StandardType.PhanELiftFamily
public import CFSG.LocalAnalysis.StandardType.PhanELiftQuasi
import CFSG.LocalAnalysis.StandardType.PhanELiftOfFamily

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.LieType.Universal

theorem phanELiftAt_of_isEShape {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]
    (hK : Nat.card K = (2 ^ f) ^ 2) {n : ℕ} {M : CoxeterMatrix (Fin n)} (hM : IsEShape M)
    {Y : LieUniversal} (hY : CFSG.IsQuasisimple Y.K) : PhanELiftAt K f M Y :=
  phanELiftAt_of_family hK (by have := hM.1; omega) hY
    (fun U W hW => exists_phanFamilyE_of_isEShape hK hM hW)


theorem phanELift_holds :
    PhanELift := by
  intro K _ _ f _ hK hq
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · norm_num at hq
    · exact h
  exact ⟨phanELiftAt_of_isEShape hK isEShape_E₆ (isQuasisimple_lieUniversal_twistedE6 f hf),
    phanELiftAt_of_isEShape hK isEShape_E₇ (isQuasisimple_lieUniversal_E7 f),
    phanELiftAt_of_isEShape hK isEShape_E₈ (isQuasisimple_lieUniversal_E8 f)⟩

end CFSG.ClassicalInvolution.Phan.PhanE
