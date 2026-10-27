module

public import CFSG.RankThree.GF2n.Parrott.Section2J0Normal

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem J_le_normalizer_J0sub (h : Tim79a.ParrottHyp z) :
    (J z).subgroupOf (H z) ≤ Subgroup.normalizer (J0sub (z := z) D : Set ↥(H z)) := by
  have hzH_mem : (⟨z, z_mem_H⟩ : ↥(H z)) ∈ J0sub D := by
    rw [mem_J0sub_iff']
    refine ⟨z_mem_J h, ?_⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp (z_centralizes_H h)
      (sigma1Nine (z := z) D : G) (sigma1Nine (z := z) D).2
    simpa using hcomm.symm
  have hzpow_le : Subgroup.zpowers (⟨z, z_mem_H⟩ : ↥(H z)) ≤ J0sub D :=
    Subgroup.zpowers_le_of_mem hzH_mem
  have hcomm_le : ⁅(J z).subgroupOf (H z), (J z).subgroupOf (H z)⁆ ≤ J0sub D := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haJ : (a : G) ∈ J z := (Subgroup.mem_subgroupOf).mp ha
    have hbJ : (b : G) ∈ J z := (Subgroup.mem_subgroupOf).mp hb
    have hcommJ : ⁅J z, J z⁆ = Subgroup.zpowers z := h.2.2.1
    have hG : ((⁅a, b⁆ : ↥(H z)) : G) ∈ Subgroup.zpowers z := by
      rw [← hcommJ]
      exact Subgroup.commutator_mem_commutator haJ hbJ
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hG
    refine hzpow_le ?_
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  rw [Subgroup.le_normalizer_iff]
  intro j hj x hx
  have hx' := hx
  rw [mem_J0sub_iff'] at hx'
  have hxL : x ∈ (J z).subgroupOf (H z) := Subgroup.mem_subgroupOf.mpr hx'.1
  have hcomm' : j * x * j⁻¹ * x⁻¹ ∈ J0sub D :=
    hcomm_le (Subgroup.commutator_mem_commutator hj hxL)
  have hconj : j * x * j⁻¹ = j * x * j⁻¹ * x⁻¹ * x := by group
  rw [hconj]
  exact (J0sub D).mul_mem hcomm' hx

theorem J0sub_normal_of_generation' (h : Tim79a.ParrottHyp z) (σ₂ : ↥(H z))
    (hEq : centralizerJ (sigma1Nine (z := z) D) = centralizerJ σ₂)
    (hgen : (Subgroup.normalizer (Subgroup.zpowers (sigma1Nine (z := z) D) : Set ↥(H z)) ⊔
      Subgroup.centralizer ({σ₂} : Set ↥(H z))) ⊔ ((J z).subgroupOf (H z)) = ⊤) :
    (J0sub D).Normal :=
  J0sub_normal_of_generation (D := D) σ₂ hEq hgen (J_le_normalizer_J0sub (D := D) h)

end CFSG.RankThree.GF2n.Parrott
