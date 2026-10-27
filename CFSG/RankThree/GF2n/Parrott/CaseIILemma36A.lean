module

public import CFSG.RankThree.GF2n.Parrott.CaseIIIndex
public import CFSG.RankThree.GF2n.Parrott.CaseIICentreSylow
public import CFSG.RankThree.GF2n.Parrott.CaseIILemma36
public import CFSG.RankThree.GF2n.Parrott.QA45InvolutionClasses

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open CFSG.ABGLocalTools CFSG.GroupTheory Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43

variable {G : Type} [Group G] [Finite G] {z : G}

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "QP" => QP45.originalSubgroup.subgroupOf QA45.originalSubgroup
set_option quotPrecheck false in
local notation "tA" => (⟨t, t_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)

section Model

theorem uv_not_mem_QP45 : uA * vA ∉ QP := by
  intro h
  rw [Subgroup.mem_subgroupOf] at h
  change u * v ∈ QP45.originalSubgroup at h
  apply v_not_mem_Q
  have h2 : u⁻¹ * (u * v) ∈ QP45.originalSubgroup :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ u_mem_Q) h
  simpa using h2

theorem not_mem_QP45_of_isConj {a b : A45} (hab : IsConj a b) (hb : b ∉ QP) : a ∉ QP := by
  intro ha
  obtain ⟨c, hc⟩ := isConj_iff.mp hab
  apply hb
  rw [← hc]
  exact (Subgroup.normal_of_index_eq_two index_QP45).conj_mem _ ha c

theorem mem_QP45_of_isConj {a b : A45} (hab : IsConj a b) (hb : b ∈ QP) : a ∈ QP := by
  obtain ⟨c, hc⟩ := isConj_iff.mp hab.symm
  rw [← hc]
  exact (Subgroup.normal_of_index_eq_two index_QP45).conj_mem _ hb c

theorem mem_commutator_of_qH_mem_QP45 (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hJ : J z ≤ ⁅H z, H z⁆) {x : G} (hxH : x ∈ H z) (hq : qH D ⟨x, hxH⟩ ∈ QP) :
    x ∈ ⁅H z, H z⁆ := by
  have hmap : (_root_.commutator ↥(H z)).map (qH D) = _root_.commutator A45 := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ (qH_surjective (z := z) D)]
  have hq' : qH D ⟨x, hxH⟩ ∈ (_root_.commutator ↥(H z)).map (qH D) := by
    rw [hmap]
    exact QP45_subgroupOf_le_commutator_QA45 hq
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hq'
  have hyW : (y : G) ∈ ⁅H z, H z⁆ := by
    have h1 : (H z).subtype y ∈ (_root_.commutator ↥(H z)).map (H z).subtype :=
      Subgroup.mem_map_of_mem _ hy
    rwa [Subgroup.map_subtype_commutator] at h1
  have hJmem : (⟨x, hxH⟩ : ↥(H z)) * y⁻¹ ∈ (J z).subgroupOf (H z) :=
    (J_mem_iff D _).2 (by rw [map_mul, map_inv, hyx, mul_inv_cancel])
  have h1 : x * (y : G)⁻¹ ∈ ⁅H z, H z⁆ := hJ (Subgroup.mem_subgroupOf.mp hJmem)
  simpa using Subgroup.mul_mem _ h1 hyW

theorem qH_mul_of_mem_J (D : QuotientData (z := z) (J_subgroupOf_normal z)) {x j : G}
    (hxH : x ∈ H z) (hj : j ∈ J z) :
    qH D ⟨x * j, Subgroup.mul_mem _ hxH (J_le_H hj)⟩ = qH D ⟨x, hxH⟩ := by
  have e : (⟨x * j, Subgroup.mul_mem _ hxH (J_le_H hj)⟩ : ↥(H z)) =
      ⟨x, hxH⟩ * ⟨j, J_le_H hj⟩ := rfl
  rw [e, map_mul, (J_mem_iff D ⟨j, J_le_H hj⟩).1 (Subgroup.mem_subgroupOf.mpr hj), mul_one]

end Model

theorem mul_self_eq_one_of_isConj_z_A (h : Tim79a.ParrottHypA z) {a : G} (ha : IsConj z a) :
    a * a = 1 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp ha
  have hzz : z * z = 1 := by
    rw [← sq, ← orderOf_z_A h]
    exact pow_orderOf_eq_one z
  calc c * z * c⁻¹ * (c * z * c⁻¹) = c * (z * z) * c⁻¹ := by group
    _ = 1 := by rw [hzz]; group

section Lemma36

theorem exists_index_two_inf_eq_commutator_A_of_uv_involution (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hF1 : ∀ j ∈ J z, orderOf j = 2 → j ∉ zpowers z → ¬ IsConj z j)
    (huv : ∀ (a : G) (ha : a ∈ H z), a * a = 1 → IsConj (qH D ⟨a, ha⟩) (uA * vA) →
      ¬ IsConj z a)
    {x : G} (hxH : x ∈ H z) (hxx : x * x = 1) (hxq : IsConj (qH D ⟨x, hxH⟩) (uA * vA)) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ z ∈ G₀ ∧ H z ⊓ G₀ = ⁅H z, H z⁆ := by
  have hxz : x * x ∈ zpowers z := by
    rw [hxx]
    exact Subgroup.one_mem _
  refine exists_index_two_inf_eq_commutator_of_lift_of_not_isConj h
    (relIndex_commutator_of_not_equalityBranch_A h D hIII) hxH
    (not_mem_commutator_of_qH_not_mem_QP45 D hxH (not_mem_QP45_of_isConj hxq uv_not_mem_QP45))
    hxz (fun _ hY => mem_J_or_mul_of_mem_centre_sylow_uv_A h D hIII hxH hxz hxq hY) hF1
    (fun hxz' => ?_) (fun j hj hc => ?_)
  · exfalso
    have hz1 : z = 1 := hxz'.symm.trans hxx
    have hz := orderOf_z_A h
    rw [hz1, orderOf_one] at hz
    norm_num at hz
  · refine huv (x * j) (Subgroup.mul_mem _ hxH (J_le_H hj))
      (mul_self_eq_one_of_isConj_z_A h hc) ?_ hc
    rw [qH_mul_of_mem_J D hxH hj]
    exact hxq

theorem exists_index_two_inf_eq_commutator_A_of_no_uv_involution
    (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hF1 : ∀ j ∈ J z, orderOf j = 2 → j ∉ zpowers z → ¬ IsConj z j)
    (hnouv : ∀ (a : G) (ha : a ∈ H z), IsConj (qH D ⟨a, ha⟩) (uA * vA) → a * a ≠ 1)
    (hv : ∀ (a : G) (ha : a ∈ H z), a * a = 1 → IsConj (qH D ⟨a, ha⟩) vA → ¬ IsConj z a) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ z ∈ G₀ ∧ H z ⊓ G₀ = ⁅H z, H z⁆ := by
  have hJ := J_le_commutator_of_not_equalityBranch_A h D hIII
  have hF2 : ∀ g : G, g * z * g⁻¹ ∈ H z → g * z * g⁻¹ ∈ ⁅H z, H z⁆ := by
    intro g hg
    have hc : IsConj z (g * z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
    have hee := mul_self_eq_one_of_isConj_z_A h hc
    by_cases heJ : g * z * g⁻¹ ∈ J z
    · exact hJ heJ
    have hq1 : qH D ⟨g * z * g⁻¹, hg⟩ ≠ 1 := by
      intro hq
      exact heJ (Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).2 hq))
    have hq2 : qH D ⟨g * z * g⁻¹, hg⟩ * qH D ⟨g * z * g⁻¹, hg⟩ = 1 := by
      rw [← map_mul]
      have e : (⟨g * z * g⁻¹, hg⟩ : ↥(H z)) * ⟨g * z * g⁻¹, hg⟩ = 1 := Subtype.ext hee
      rw [e, map_one]
    have hord : orderOf (qH D ⟨g * z * g⁻¹, hg⟩) = 2 :=
      orderOf_eq_prime (by rw [sq]; exact hq2) hq1
    rcases qa45_involution_classes _ hord with hct | hcut | hcv | hcuv
    · exact mem_commutator_of_qH_mem_QP45 D hJ hg (mem_QP45_of_isConj hct
        (Subgroup.mem_subgroupOf.mpr t_mem_Q))
    · refine mem_commutator_of_qH_mem_QP45 D hJ hg (mem_QP45_of_isConj hcut ?_)
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mul_mem _ u_mem_Q t_mem_Q
    · exact absurd hc (hv _ hg hee hcv)
    · exact absurd hee (hnouv _ hg hcuv)
  obtain ⟨x, hxH, hxx, hxq⟩ := exists_uv_lift_sq_mem_A h D hIII
  have hxc : IsConj (qH D ⟨x, hxH⟩) (uA * vA) := by
    rw [hxq]
  refine exists_index_two_inf_eq_commutator_of_lift_of_not_isConj h
    (relIndex_commutator_of_not_equalityBranch_A h D hIII) hxH
    (not_mem_commutator_of_qH_not_mem_QP45 D hxH (by rw [hxq]; exact uv_not_mem_QP45)) hxx
    (fun _ hY => mem_J_or_mul_of_mem_centre_sylow_uv_A h D hIII hxH hxx hxc hY) hF1
    (fun _ => hF2) (fun j hj hc => ?_)
  refine hnouv (x * j) (Subgroup.mul_mem _ hxH (J_le_H hj)) ?_
    (mul_self_eq_one_of_isConj_z_A h hc)
  rw [qH_mul_of_mem_J D hxH hj]
  exact hxc

end Lemma36

end CFSG.RankThree.GF2n.Parrott
