module

public import CFSG.RankThree.PartTwo.Sec4.Statements
import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem u38_four_nine (h49 : Sec4.Item4_9) (hG : TheoremFourHyp G)
    {B : Subgroup G} (hB3 : IsPGroup 3 B) {a : G} (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1)
    (hF : ∀ L' ∈ thetaComponentsAt 3 a, B ≤ Subgroup.normalizer (L' : Set G))
    (hBa : B ≤ Subgroup.centralizer ({a} : Set G))
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a)
    {Q : Subgroup G} (hQ2 : IsPGroup 2 Q) (hQa : Q ≤ Subgroup.centralizer ({a} : Set G))
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hQB : Q ≤ ⁅Q, B⁆) :
    Q ≤ Y ⊔ Sec4.thetaQuotCentralizer Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.centralizer ({a} : Set G) with hH
  obtain ⟨hYH, hY'⟩ := mem_thetaComponentsIn_iff.mp hY
  have hH4 : SectionFourHyp H := hG.sectionFourHyp (Sec6.centralizer_ne_top_of_ne_one hG ha1)
  have h3Z : 3 ∣ Nat.card (Subgroup.center H) := by
    set a' : H := ⟨a, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    have ha'3 : orderOf a' = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime ha3 ha1
    have hle : Subgroup.zpowers a' ≤ Subgroup.center H := by
      rw [Subgroup.zpowers_le, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp g.2)
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, ha'3] at this
  have hXK : ∀ K' ∈ thetaComponents 3 H, B.subgroupOf H ≤ Subgroup.normalizer (K' : Set H) := by
    intro K' hK'' x hx
    exact Sec6.mem_normalizer_of_mem_normalizer_map
      (hF (K'.map H.subtype) ⟨K', hK'', rfl⟩ (Subgroup.mem_subgroupOf.mp hx))
  have hBV : ⁅B, Q⁆ = Q := by
    rw [Subgroup.commutator_comm]
    exact le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.mp hBQ) hQB
  have hV' : Q.subgroupOf H ∈ invariantPiSubgroups ⊤ (B.subgroupOf H) (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨le_top,
      hQ2.comap_of_injective H.subtype H.subtype_injective,
      Sec6.subgroupOf_le_normalizer_subgroupOf hBQ⟩
  have hVB' : ⁅B.subgroupOf H, Q.subgroupOf H⁆ = Q.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hBa,
      Subgroup.map_subgroupOf_eq_of_le hQa]
    exact hBV
  have h49' := h49 H hH4 h3Z (Y.subgroupOf H) hY' (B.subgroupOf H)
    (hB3.comap_of_injective H.subtype H.subtype_injective) hXK (Q.subgroupOf H) hV' hVB'
  have h1 := Subgroup.map_mono (f := H.subtype) h49'
  rw [Subgroup.map_subgroupOf_eq_of_le hQa, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hYH] at h1
  refine h1.trans (sup_le_sup_left ?_ Y)
  have h2 := Sec6.map_thetaQuotCentralizer_le (Y.subgroupOf H)
  rwa [Subgroup.map_subgroupOf_eq_of_le hYH] at h2

end CFSG.RankThree.PartTwo.Sec8
