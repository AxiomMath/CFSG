module

public import CFSG.Quasithin.MS93.S36Frat
public import CFSG.Quasithin.MS93.S5ABase

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ
open CFSG.Quasithin.MS93.S36

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem qv_inr (h : PUHyp M T L) (ψ : MulAut ↥T) :
    Qv (puAmalgam h.le) ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _) =
      imM h.le (tImage ψ (pCoreOf 2 M)) := by
  rw [qv_smul, S5.qv_baseA_eq h, imM_map_conj_inr h.le ψ h.pCore_le]

theorem isCritical_inr_inv (h : PUHyp M T L) (ψ : MulAut ↥T)
    (hc : IsCritical (puAmalgam h.le) (baseA _)
      ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _)) :
    IsCritical (puAmalgam h.le) (baseA _)
      ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ⁻¹) • baseA _) := by
  have h' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  have e : (puAmalgam h.le).ofB (SemidirectProduct.inr ψ⁻¹) •
      ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA (puAmalgam h.le)) =
        baseA (puAmalgam h.le) := by
    rw [smul_smul, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, one_smul]
  rw [← isCritical_smul _ ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ⁻¹)), e] at h'
  exact h'

theorem not_le_of_isCritical_inr (h : PUHyp M T L) (ψ : MulAut ↥T)
    (hc : IsCritical (puAmalgam h.le) (baseA _)
      ((puAmalgam h.le).ofB (SemidirectProduct.inr ψ) • baseA _)) :
    ¬ Z0q M T ≤ tImage ψ (pCoreOf 2 M) ∧ ¬ tImage ψ (Z0q M T) ≤ pCoreOf 2 M := by
  have h' := ms22_iii _ h.hyp20 h.critDist_pos h.centHyp hc
  refine ⟨fun hle => hc.2.2 ?_, fun hle => h'.2.2 ?_⟩
  · rw [puAmalgam.zm_baseA, qv_inr h]
    exact imM_mono h.le hle
  · rw [zm_inr h, S5.qv_baseA_eq h]
    exact imM_mono h.le hle

end CFSG.Quasithin.MS93.S36SP
