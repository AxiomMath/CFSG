module

public import CFSG.RankThree.GroupTheory.ThetaComponents
public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.GroupTheory.LocalCores.Components
import CFSG.RankThree.PartTwo.Late.Transitivity

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank
open scoped commutatorElement

theorem commutator_le_of_mem_thetaComponents {H : Type*} [Group H] [Finite H]
    {Y₁ Y₂ : Subgroup H} (h₁ : Y₁ ∈ thetaComponents 3 H) (h₂ : Y₂ ∈ thetaComponents 3 H)
    (hne : Y₁ ≠ Y₂) : ⁅Y₁, Y₂⁆ ≤ aschbacherSolvableCore 3 H := by
  have hK₁ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₁
  have hK₂ := isComponent_map_of_mem_thetaComponents Nat.prime_three h₂
  have hKne : Y₁.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) ≠
      Y₂.map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) := fun h =>
    hne ((theta_component_quotient_correspondence (H := H) Nat.prime_three).1.injOn h₁ h₂ h)
  have hc := (CFSG.LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hc
  exact hc

theorem eq_one_of_mem_of_pow_three {H : Type*} [Group H] [Finite H] {N : Subgroup H}
    (hN : ¬ 3 ∣ Nat.card N) {x : H} (hx : x ∈ N) (hx3 : x ^ 3 = 1) : x = 1 := by
  have h1 : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
  have h2 : orderOf x ∣ Nat.card N := by
    rw [← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hN
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem four_le_pRank_of_commutator_le {H : Type*} [Group H] [Finite H] (N : Subgroup H)
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {E₁ E₂ : Subgroup H}
    (hE₁ : CFSG.Open.IsElemAbelian 3 E₁) (hE₂ : CFSG.Open.IsElemAbelian 3 E₂)
    (h₁ : Nat.card E₁ = 9) (h₂ : Nat.card E₂ = 9) (hc : ⁅E₁, E₂⁆ ≤ N)
    (hd : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y⁻¹ ∈ N → x = 1) :
    4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup H) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [← CFSG.SectionRank.pRank_quotient_eq N hN]
  have hcomm : ∀ (x : E₁) (y : E₂), Commute ((QuotientGroup.mk' N).comp E₁.subtype x)
      ((QuotientGroup.mk' N).comp E₂.subtype y) := by
    intro x y
    have hxy : ⁅(x : H), (y : H)⁆ ∈ N := hc (Subgroup.commutator_mem_commutator x.2 y.2)
    have h1 : QuotientGroup.mk' N ⁅(x : H), (y : H)⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hxy
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  set f : E₁ × E₂ →* H ⧸ N := MonoidHom.noncommCoprod ((QuotientGroup.mk' N).comp E₁.subtype)
    ((QuotientGroup.mk' N).comp E₂.subtype) hcomm with hfdef
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    rintro ⟨x, y⟩ hxy
    have h1 : QuotientGroup.mk' N ((x : H) * y) = 1 := by
      rw [map_mul]
      exact hxy
    have hN1 : (x : H) * y ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have hx1 : (x : H) = 1 := hd x x.2 (y : H)⁻¹ (E₂.inv_mem y.2) (by rwa [inv_inv])
    have hy1 : (y : H) = 1 := by
      rw [hx1, one_mul] at hN1
      exact eq_one_of_mem_of_pow_three hN hN1 (hE₂.2 y y.2)
    rw [Subgroup.mem_bot]
    exact Prod.ext (Subtype.ext hx1) (Subtype.ext hy1)
  have := hE₁.1
  have := hE₂.1
  refine CFSG.SectionRank.le_pRank_of_injective (by norm_num) ?_ ?_ ?_ f hf le_top
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩
    exact Prod.ext (mul_comm' x₁ x₂) (mul_comm' y₁ y₂)
  · rintro ⟨x, y⟩
    exact Prod.ext (Subtype.ext (by simpa using hE₁.2 x x.2))
      (Subtype.ext (by simpa using hE₂.2 y y.2))
  · rw [Nat.card_prod, h₁, h₂]
    norm_num

theorem map_aschbacherSolvableCore_facts {G : Type*} [Group G] [Finite G] (Y : Subgroup G) :
    Y ≤ Subgroup.normalizer (((aschbacherSolvableCore 3 ↥Y).map Y.subtype : Subgroup G) : Set G) ∧
      Group.IsSolvable ↥((aschbacherSolvableCore 3 ↥Y).map Y.subtype) ∧
      ¬ 3 ∣ Nat.card ↥((aschbacherSolvableCore 3 ↥Y).map Y.subtype) := by
  obtain ⟨hs, hc, h3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Y) Nat.prime_three
  refine ⟨Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _), ?_, ?_⟩
  · exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective _ _ Y.subtype_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  · rwa [Subgroup.card_map_of_injective Y.subtype_injective]

theorem inf_le_map_aschbacherSolvableCore {G : Type*} [Group G] [Finite G] {N Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hNs : Group.IsSolvable N)
    (hN3 : ¬ 3 ∣ Nat.card N) : N ⊓ Y ≤ (aschbacherSolvableCore 3 ↥Y).map Y.subtype := by
  set K := (N ⊓ Y).subgroupOf Y with hK
  have hKn : K.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr
    (Late.le_normalizer_inf hYN Subgroup.le_normalizer)
  have hKe : K ≃* ↥(N ⊓ Y) := Subgroup.subgroupOfEquivOfLe inf_le_right
  have hKs : Group.IsSolvable K :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.inclusion (inf_le_left : N ⊓ Y ≤ N)).comp hKe.toMonoidHom)
      ((Subgroup.inclusion_injective (inf_le_left : N ⊓ Y ≤ N)).comp hKe.injective)
  have hK3 : ¬ 3 ∣ Nat.card K := by
    rw [Nat.card_congr hKe.toEquiv]
    exact fun h => hN3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hle : K ≤ aschbacherSolvableCore 3 ↥Y :=
    (solvable_prime_complement_core_characterization Nat.prime_three).2.2.2.1 K hKn hKs hK3
  have hmap : K.map Y.subtype = N ⊓ Y := by
    rw [hK, Subgroup.subgroupOf_map_subtype, inf_assoc, inf_idem]
  rw [← hmap]
  exact Subgroup.map_mono hle

end CFSG.RankThree.PartTwo.Sec15
