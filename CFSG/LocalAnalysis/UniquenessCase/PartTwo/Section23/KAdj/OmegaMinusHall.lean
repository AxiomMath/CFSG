module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.OmegaMinusModel
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.Hall
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE

open CFSG.ClassicalGroups.Orthogonal CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

private theorem tailTorus_le_normalizer_E13 {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (tailTorus 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) ≤
      Subgroup.normalizer (((tailUnipotent 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) :
          Subgroup (OmegaMinusE K b c)) : Set (OmegaMinusE K b c)) := by
  rw [normalizer_tailUnipotent (r := 3) (qA := minusTailForm K b c)
    (anisotropic_minusTailForm hirr)
    ⟨fun _ => 1, fun h => one_ne_zero (congrFun h 0)⟩]
  exact fun x hx => tailTorus_le_tailBorel (Subgroup.mem_subgroupOf.mp hx)

private theorem not_two_dvd_card_tailTorus_E13 {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ 2 ∣ Nat.card ((tailTorus 3 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 3 (minusTailForm K b c)))) := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (tailTorus_le (r := 3) (qA := minusTailForm K b c))).toEquiv]
  exact orthogonal_geometry_tail_small_anisotropic_Levi_p_prime (p := 2) (le_refl 3)
    (anisotropic_minusTailForm hirr) (nondegenerate_minusTailForm hirr)
    (Or.inr finrank_fin_two_fun)

private theorem mem_sup_of_mem_tailBorel_E13 {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {t : OmegaMinusE K b c}
    (ht : t ∈ (tailBorel 3 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 3 (minusTailForm K b c)))) :
    t ∈ (tailUnipotent 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) ⊔
      (tailTorus 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) := by
  obtain ⟨-, hBU⟩ := tailBorel_eq_mul (r := 3) (qA := minusTailForm K b c)
    (anisotropic_minusTailForm hirr)
  have htB : (t : ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K))) ∈
      (tailBorel 3 (minusTailForm K b c) : Set _) := Subgroup.mem_subgroupOf.mp ht
  rw [hBU] at htB
  obtain ⟨u, hu, s, hs, hus⟩ := Set.mem_mul.1 htB
  have ht_eq : t = (⟨u, tailUnipotent_le hu⟩ : OmegaMinusE K b c) *
      ⟨s, tailTorus_le hs⟩ := Subtype.ext hus.symm
  rw [ht_eq]
  exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hu)
    (Subgroup.mem_subgroupOf.mpr hs)

theorem omegaMinus_exists_conj_mem_tailTorus {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {t : OmegaMinusE K b c}
    (ht : t ∈ (tailBorel 3 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 3 (minusTailForm K b c))))
    (hodd : Odd (orderOf t)) :
    ∃ e ∈ (tailUnipotent 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))),
      e * t * e⁻¹ ∈ (tailTorus 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) := by
  obtain ⟨e, he, hconj⟩ := exists_conj_mem_of_mem_sup
    (G := OmegaMinusE K b c) (p := 2)
    (tailTorus_le_normalizer_E13 hirr)
    (isPGroup_tailUnipotent (p := 2) (r := 3) (qA := minusTailForm K b c)
      (anisotropic_minusTailForm hirr))
    (not_two_dvd_card_tailTorus_E13 hirr)
    (mem_sup_of_mem_tailBorel_E13 hirr ht)
    (by rw [← even_iff_two_dvd]; exact Nat.not_even_iff_odd.mpr hodd)
  exact ⟨e, he, hconj⟩

theorem omegaMinus_tailUnipotent_le_inf {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (tailUnipotent 3 (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) ≤
      omegaMinusTailQZero K b c ⊓ omegaMinusTailQAlpha K b c := by
  rw [omegaMinusTailQZero_inf_QAlpha]
  exact fun x hx => Subgroup.mem_subgroupOf.mpr
    (tailUnipotent_le_tailBorel (anisotropic_minusTailForm hirr)
      (Subgroup.mem_subgroupOf.mp hx))

end CFSG.LocalAnalysis.UniquenessCase.UC22.KAdjE
