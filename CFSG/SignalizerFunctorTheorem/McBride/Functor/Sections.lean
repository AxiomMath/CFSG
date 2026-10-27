module

public import CFSG.SignalizerFunctorTheorem.Inheritance.Sections
public import CFSG.SignalizerFunctorTheorem.Inheritance.HypB

public section

open CFSG.Open

universe u v

namespace CFSG.SignalizerFunctorTheorem.McBride

theorem isSectionOf_of_le {G : Type*} [Group G] {X Y : Subgroup G} (h : X ≤ Y) {S : Type*}
    [Group S] (hS : IsSectionOf S ↥X) : IsSectionOf S ↥Y :=
  hS.of_injective (Subgroup.inclusion h) (Subgroup.inclusion_injective h)

theorem isSectionOf_map_iff {G : Type*} {K : Type*} [Group G] [Group K] (f : G →* K)
    (hf : Function.Injective f) (X : Subgroup G) (S : Type*) [Group S] :
    IsSectionOf S ↥(X.map f) ↔ IsSectionOf S ↥X :=
  ⟨fun h => h.trans (IsSectionOf.of_mulEquiv (X.equivMapOfInjective f hf)),
    fun h => h.trans (IsSectionOf.of_mulEquiv (X.equivMapOfInjective f hf).symm)⟩

theorem isSectionOf_of_isSectionOf_map {G : Type*} {K : Type*} [Group G] [Group K] (f : G →* K)
    (X : Subgroup G) {S : Type*} [Group S] (hS : IsSectionOf S ↥(X.map f)) :
    IsSectionOf S ↥X :=
  hS.trans (IsSectionOf.of_surjective (f.subgroupMap X) (f.subgroupMap_surjective X))

theorem ker_subgroupMap_mk' {G : Type*} [Group G] (N X : Subgroup G) [N.Normal] :
    ((QuotientGroup.mk' N).subgroupMap X).ker = N.subgroupOf X := by
  ext k
  simp [MonoidHom.mem_ker, Subtype.ext_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_map_mk'_mul_card {G : Type*} [Group G] {N X : Subgroup G} [N.Normal] (hN : N ≤ X) :
    Nat.card (X.map (QuotientGroup.mk' N)) * Nat.card N = Nat.card X := by
  have h := Subgroup.card_ker_mul_card_of_surjective
    ((QuotientGroup.mk' N).subgroupMap_surjective X)
  rw [ker_subgroupMap_mk', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN).toEquiv] at h
  rwa [mul_comm] at h

theorem isSectionOf_normal_or_quotient {G : Type*} [Group G] {N X : Subgroup G} [N.Normal]
    (hN : N ≤ X) {S : Type*} [Group S] [IsSimpleGroup S] (hS : IsSectionOf S ↥X) :
    IsSectionOf S ↥N ∨ IsSectionOf S ↥(X.map (QuotientGroup.mk' N)) := by
  rcases hS.of_hom ((QuotientGroup.mk' N).subgroupMap X) with h | h
  · rw [ker_subgroupMap_mk'] at h
    exact Or.inl (h.trans (IsSectionOf.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hN).symm))
  · exact Or.inr h

theorem isSectionOf_quotient_subgroup {G : Type*} [Group G] {K L X : Subgroup G} (hKX : K ≤ X)
    [(L.subgroupOf K).Normal] : IsSectionOf (K ⧸ L.subgroupOf K) ↥X :=
  isSectionOf_of_le hKX (IsSectionOf.of_surjective (QuotientGroup.mk' (L.subgroupOf K))
    (QuotientGroup.mk'_surjective _))

theorem signalizerMcBrideHypothesisB_iff {G : Type u} [Group G] [Finite G] {p : ℕ}
    {X : Subgroup G} :
    signalizerMcBrideHypothesisB p X ↔ p.Prime ∧ Nat.Coprime p (Nat.card X) ∧
      ∀ (S : Type u) [Group S] [Finite S] [IsSimpleGroup S], IsSectionOf S ↥X →
        (∃ a b : S, a * b ≠ b * a) → signalizerMcBrideHypothesisA p S := by
  constructor
  · intro hX
    exact ⟨hX.1, hX.2.1, fun S _ _ _ hS hnc =>
      signalizerMcBrideHypothesisA_of_isSectionOf hX hS hnc⟩
  · rintro ⟨hp, hcop, h⟩
    refine ⟨hp, hcop, fun K L hKX hLK _ hsimple hnc => ?_⟩
    exact h (K ⧸ L.subgroupOf K) (isSectionOf_quotient_subgroup hKX) hnc

theorem signalizerNearPSolvable_iff {X : Type u} [Group X] {p : ℕ} :
    signalizerNearPSolvable p X ↔ Nat.Coprime p (Nat.card X) ∧
      ∀ (S : Type u) [Group S] [IsSimpleGroup S], IsSectionOf S X →
        (∃ a b : S, a * b ≠ b * a) → signalizerNearSimpleModel p S := by
  constructor
  · rintro ⟨hcop, h⟩
    refine ⟨hcop, fun S _ _ hS hnc => ?_⟩
    obtain ⟨K, f, hf⟩ := hS
    let L : Subgroup X := f.ker.map K.subtype
    have hLK : L ≤ K := Subgroup.map_subtype_le _
    have hker : L.subgroupOf K = f.ker :=
      Subgroup.comap_map_eq_self_of_injective K.subtype_injective f.ker
    have : (L.subgroupOf K).Normal := by
      rw [hker]
      exact MonoidHom.normal_ker f
    let E : K ⧸ L.subgroupOf K ≃* S :=
      (QuotientGroup.quotientMulEquivOfEq hker).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hf)
    have hsimple : IsSimpleGroup (K ⧸ L.subgroupOf K) := E.isSimpleGroup
    have hnonab : ∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a := by
      obtain ⟨x, y, hxy⟩ := hnc
      exact ⟨E.symm x, E.symm y, fun hc => hxy (by simpa using congrArg E hc)⟩
    exact TransportA.nearSimpleModel_of_mulEquiv E (h K L hLK hsimple hnonab)
  · rintro ⟨hcop, h⟩
    refine ⟨hcop, fun K L hLK _ hsimple hnonab => ?_⟩
    exact h (K ⧸ L.subgroupOf K)
      ((IsSectionOf.of_surjective (QuotientGroup.mk' (L.subgroupOf K))
        (QuotientGroup.mk'_surjective _)).trans (IsSectionOf.of_subgroup K)) hnonab

end CFSG.SignalizerFunctorTheorem.McBride
