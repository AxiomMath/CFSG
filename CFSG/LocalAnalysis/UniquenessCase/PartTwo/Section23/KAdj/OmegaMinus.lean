module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusTorus
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.ConjBack
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.MapInjective
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusChar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer
import CFSG.LocalAnalysis.UniquenessCase.UC22P22m

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.Open

noncomputable abbrev omegaMinusQAlpha {K : Type} [Field K] {b c : K}
    (φ : ↥(StatedOmega (StatedQuadMinus 4 K b c)) ≃* OmegaMinusE K b c) :
    Subgroup ↥(StatedOmega (StatedQuadMinus 4 K b c)) :=
  (omegaMinusTailQAlpha K b c).comap φ.toMonoidHom

private theorem map_mem_inf_E18 {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (φ : ↥(StatedOmega (StatedQuadMinus 4 K b c)) ≃* OmegaMinusE K b c)
    (hφ : (omegaMinusQZero K b c).map φ.toMonoidHom = omegaMinusTailQZero K b c)
    {t : ↥(StatedOmega (StatedQuadMinus 4 K b c))}
    (ht : t ∈ Hinf (omegaMinusQAlpha φ) ⊓ omegaMinusQZero K b c) :
    φ t ∈ Hinf (omegaMinusTailQAlpha K b c) ⊓ omegaMinusTailQZero K b c := by
  constructor
  · have hmem : φ t ∈ (Hinf (omegaMinusQAlpha φ)).map φ.toMonoidHom :=
      Subgroup.mem_map_of_mem φ.toMonoidHom ht.1
    rwa [Hinf_map φ.toMonoidHom (omegaMinusQAlpha φ),
      Subgroup.map_comap_eq_self_of_surjective φ.surjective
        (omegaMinusTailQAlpha K b c)] at hmem
  · rw [← hφ]
    exact Subgroup.mem_map_of_mem φ.toMonoidHom ht.2

private theorem map_hinf_qzero_E18 {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (φ : ↥(StatedOmega (StatedQuadMinus 4 K b c)) ≃* OmegaMinusE K b c)
    (hφ : (omegaMinusQZero K b c).map φ.toMonoidHom = omegaMinusTailQZero K b c) :
    (Hinf (omegaMinusQZero K b c)).map φ.toMonoidHom = Hinf (omegaMinusTailQZero K b c) := by
  rw [← hφ]
  exact Hinf_map φ.toMonoidHom (omegaMinusQZero K b c)

theorem kAdj_tail_omegaMinusEight {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {r : ℕ} (hr : Odd r) {t : OmegaMinusE K b c}
    (ht : t ∈ Hinf (omegaMinusTailQAlpha K b c) ⊓ omegaMinusTailQZero K b c)
    (hord : orderOf t = r) : KAdjConcl (Hinf (omegaMinusTailQZero K b c)) t r n := by
  obtain ⟨e, he, u, hτ, hu⟩ := omegaMinus_exists_conj_coroot hirr ht (by rwa [hord])
  have heQ : e ∈ omegaMinusTailQZero K b c := (omegaMinus_tailUnipotent_le_inf hirr he).1
  exact kAdjConcl_conj e (uc22p22m_le_normalizer_Hinf _ heQ)
    (kAdjConcl_omegaMinusTorus hirr hK hn hr (hu.trans hord) hτ)

theorem kAdj_model_omegaMinusEight {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n)
    {r : ℕ} (hr : Odd r) (φ : ↥(StatedOmega (StatedQuadMinus 4 K b c)) ≃* OmegaMinusE K b c)
    (hφ : (omegaMinusQZero K b c).map φ.toMonoidHom = omegaMinusTailQZero K b c)
    {t : ↥(StatedOmega (StatedQuadMinus 4 K b c))}
    (ht : t ∈ Hinf (omegaMinusQAlpha φ) ⊓ omegaMinusQZero K b c) (hord : orderOf t = r) :
    KAdjConcl (Hinf (omegaMinusQZero K b c)) t r n := by
  have h := kAdj_tail_omegaMinusEight hirr hK hn hr (map_mem_inf_E18 φ hφ ht)
    ((MulEquiv.orderOf_eq φ t).trans hord)
  rw [← map_hinf_qzero_E18 φ hφ] at h
  exact kAdjConcl_of_map_injective φ.toMonoidHom φ.injective h

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
