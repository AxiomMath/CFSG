module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem commutator_zpowers_le {Y : Subgroup G} {d : G}
    (hd : d ∈ Subgroup.normalizer (Y : Set G)) : ⁅Y, Subgroup.zpowers d⁆ ≤ Y :=
  (Subgroup.le_normalizer_iff_commutator_le_left).1 (Subgroup.zpowers_le.2 hd)

@[expose] def commModJ (X J : Subgroup G) (d : G) : Subgroup G :=
  ⁅X, Subgroup.zpowers d⁆ ⊔ J

private theorem s762Q_commModJ_le_of_mul_mem {X J : Subgroup G} [(J.subgroupOf X).Normal]
    {d d₁ : G} (hJX : J ≤ X) (hdJ : d ∈ Subgroup.normalizer (J : Set G))
    (h : d⁻¹ * d₁ ∈ J) : commModJ X J d₁ ≤ commModJ X J d := by
  have hXnorm : X ≤ Subgroup.normalizer (J : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hJX).1 inferInstance
  have hJnorm : Subgroup.zpowers d ≤ Subgroup.normalizer (J : Set G) :=
    Subgroup.zpowers_le.2 hdJ
  have hd₁ : d₁ ∈ Subgroup.zpowers d ⊔ J := by
    rw [show d₁ = d * (d⁻¹ * d₁) by group]
    exact Subgroup.mul_mem_sup (Subgroup.mem_zpowers d) h
  change ⁅X, Subgroup.zpowers d₁⁆ ⊔ J ≤ ⁅X, Subgroup.zpowers d⁆ ⊔ J
  refine sup_le ?_ le_sup_right
  refine Subgroup.commutator_le.2 ?_
  intro x hx z hz
  have hzsup : z ∈ Subgroup.zpowers d ⊔ J := (Subgroup.zpowers_le.2 hd₁) hz
  have hzJ : z ∈ (Subgroup.zpowers d : Set G) * (J : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers d) J hJnorm]
    exact hzsup
  rw [Set.mem_mul] at hzJ
  obtain ⟨y, hy, j', hj', hyj⟩ := hzJ
  obtain ⟨n, rfl⟩ := (Subgroup.mem_zpowers_iff).1 hy
  rw [← hyj]
  rw [show ⁅x, d ^ n * j'⁆ = ⁅x, d ^ n⁆ * (d ^ n * ⁅x, j'⁆ * (d ^ n)⁻¹) by
    simp only [commutatorElement_def]; group]
  refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
  · exact Subgroup.commutator_mem_commutator hx (Subgroup.zpow_mem_zpowers d n)
  · have hcommJ : ⁅x, j'⁆ ∈ J :=
      (Subgroup.commutator_le.1 ((Subgroup.le_normalizer_iff_commutator_le_right).1 hXnorm))
        x hx j' hj'
    exact (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (J : Set G)).zpow_mem hdJ n) ⁅x, j'⁆).1 hcommJ

theorem commModJ_eq_of_mul_mem {X J : Subgroup G} [(J.subgroupOf X).Normal] {d d₁ : G}
    (hJX : J ≤ X) (hdJ : d ∈ Subgroup.normalizer (J : Set G)) (h : d⁻¹ * d₁ ∈ J) :
    commModJ X J d = commModJ X J d₁ := by
  have hd₁J : d₁ ∈ Subgroup.normalizer (J : Set G) := by
    rw [show d₁ = d * (d⁻¹ * d₁) by group]
    exact (Subgroup.normalizer (J : Set G)).mul_mem hdJ (Subgroup.le_normalizer h)
  have h₁ : d₁⁻¹ * d ∈ J := by
    rw [show d₁⁻¹ * d = (d⁻¹ * d₁)⁻¹ by group]
    exact J.inv_mem h
  exact le_antisymm (s762Q_commModJ_le_of_mul_mem hJX hd₁J h₁)
    (s762Q_commModJ_le_of_mul_mem hJX hdJ h)

theorem commModJ_sup_eq {Y J : Subgroup G} {d : G}
    (hY : Y ≤ Subgroup.normalizer (J : Set G)) (hdJ : d ∈ Subgroup.normalizer (J : Set G)) :
    commModJ (Y ⊔ J) J d = ⁅Y, Subgroup.zpowers d⁆ ⊔ J := by
  rw [commModJ]
  apply le_antisymm
  · refine sup_le ?_ le_sup_right
    refine Subgroup.commutator_le.2 ?_
    intro a ha z hz
    have ha' : a ∈ (Y : Set G) * (J : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y J hY]
      exact ha
    rw [Set.mem_mul] at ha'
    obtain ⟨y, hy, j, hj, hyj⟩ := ha'
    rw [← hyj]
    have hzN : z ∈ Subgroup.normalizer (J : Set G) := (Subgroup.zpowers_le.2 hdJ) hz
    have hcommJ : ⁅j, z⁆ ∈ J :=
      (Subgroup.commutator_le.1 (commutator_zpowers_le hzN)) j hj z (Subgroup.mem_zpowers z)
    have hconj : y * ⁅j, z⁆ * y⁻¹ ∈ J :=
      (Subgroup.mem_normalizer_iff.1 (hY hy) ⁅j, z⁆).1 hcommJ
    have hyz : ⁅y, z⁆ ∈ ⁅Y, Subgroup.zpowers d⁆ :=
      Subgroup.commutator_mem_commutator hy hz
    rw [show ⁅y * j, z⁆ = y * ⁅j, z⁆ * y⁻¹ * ⁅y, z⁆ by
      simp only [commutatorElement_def]; group]
    exact mul_mem (Subgroup.mem_sup_right hconj) (Subgroup.mem_sup_left hyz)
  · refine sup_le ((Subgroup.commutator_mono le_sup_left le_rfl).trans le_sup_left) le_sup_right

end CFSG.LocalAnalysis.WeakClosure81
