module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.FaithfulSimple.SectionAction
public import CFSG.SignalizerFunctorTheorem.Inheritance.HypB
public import CFSG.SignalizerFunctorTheorem.Inheritance.Induction

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem

theorem mcBrideHypothesisB_of_isSectionOf {G V : Type*} [Group G] [Finite G] [Group V] [Finite V]
    {p : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p (Nat.card V)) {H : Subgroup G}
    (hH : signalizerMcBrideHypothesisB p H) {Y : Subgroup V} (hY : IsSectionOf Y H) :
    signalizerMcBrideHypothesisB p Y := by
  refine ⟨hp, hcop.of_dvd_right (Subgroup.card_subgroup_dvd_card Y), ?_⟩
  intro K L hKY hLK _ hsimple hnc
  have := hsimple
  have hXK : IsSectionOf (K ⧸ L.subgroupOf K) K :=
    IsSectionOf.of_surjective (QuotientGroup.mk' (L.subgroupOf K))
      (QuotientGroup.mk'_surjective _)
  have hKY' : IsSectionOf K Y :=
    (IsSectionOf.refl K).of_injective (Subgroup.inclusion hKY) (Subgroup.inclusion_injective hKY)
  exact signalizerMcBrideHypothesisA_of_isSectionOf hH ((hXK.trans hKY').trans hY) hnc

variable {G : Type*} [Group G] {K L A : Subgroup G} [(L.subgroupOf K).Normal]

theorem isSectionOf_fixed [Finite G] {p : ℕ} (hp : p.Prime) (hLK : L ≤ K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {a : A} (ha : (a : G) ^ p = 1) (hcop : Nat.Coprime p (Nat.card L)) :
    IsSectionOf (signalizerFixedSubgroup (sectionAction hAK hAL a))
      ↥(K ⊓ Subgroup.centralizer {(a : G)}) := by
  let π : ↥(K ⊓ Subgroup.centralizer {(a : G)}) →* K ⧸ L.subgroupOf K :=
    (QuotientGroup.mk' (L.subgroupOf K)).comp (Subgroup.inclusion inf_le_left)
  have hπ : ∀ y, π y ∈ signalizerFixedSubgroup (sectionAction hAK hAL a) := by
    intro y
    show sectionAction hAK hAL a (QuotientGroup.mk (Subgroup.inclusion inf_le_left y)) =
      QuotientGroup.mk (Subgroup.inclusion inf_le_left y)
    rw [sectionAction_mk_eq_iff]
    have h1 : (a : G) * (y : G) = (y : G) * (a : G) :=
      (Subgroup.mem_centralizer_singleton_iff.mp y.2.2).symm
    have h2 : (a : G) * y * (a : G)⁻¹ = y := by rw [mul_inv_eq_iff_eq_mul]; exact h1
    simp [h2]
  refine IsSectionOf.of_surjective (π.codRestrict _ hπ) ?_
  rintro ⟨v, hv⟩
  obtain ⟨y, hy1, hy2⟩ := exists_fixed_mk hp hLK hAK hAL ha hcop hv
  exact ⟨⟨y, y.2, mem_centralizer_singleton_of_conj hy1⟩, Subtype.ext hy2⟩

theorem mcBrideHypothesisB_fixed [Finite G] {p : ℕ} (hp : p.Prime) (hLK : L ≤ K)
    (hAK : A ≤ Subgroup.normalizer (K : Set G)) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {a : A} (ha : (a : G) ^ p = 1) (hcopL : Nat.Coprime p (Nat.card L))
    (hcopV : Nat.Coprime p (Nat.card (K ⧸ L.subgroupOf K))) {H : Subgroup G}
    (hH : signalizerMcBrideHypothesisB p H) (hle : K ⊓ Subgroup.centralizer {(a : G)} ≤ H) :
    signalizerMcBrideHypothesisB p (signalizerFixedSubgroup (sectionAction hAK hAL a)) :=
  mcBrideHypothesisB_of_isSectionOf hp hcopV hH
    ((isSectionOf_fixed hp hLK hAK hAL ha hcopL).trans
      ((IsSectionOf.refl _).of_injective (Subgroup.inclusion hle)
        (Subgroup.inclusion_injective hle)))

end CFSG.SignalizerFunctorTheorem
