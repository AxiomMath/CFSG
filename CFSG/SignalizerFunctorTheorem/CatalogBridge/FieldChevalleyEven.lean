module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.StabilizerLift
public import CFSG.RankThree.Chevalley.SteinbergBTCanonicalFieldCommon

public section

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley.SteinbergBT (orderOf_entrywiseAdjointAut not_commute_fixedFieldImage)
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem fixedClauses_of_FStarSimple_S2
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    (σ : K ≃+* K) (hσ : orderOf σ = p) (hrank : 0 < τ.rank)
    (hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ)
    (hF : FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)))
    (hOut : ∀ a b : MulAut (adjointGroup τ K), ⁅a, b⁆ ∈
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hS2 : ∀ β : MulAut (adjointGroup τ K),
      β * entrywiseAdjointAut τ σ = entrywiseAdjointAut τ σ * β →
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → β j = j) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ))
    (hNL : FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) →
      NonLocalized (signalizerFixedSubgroup (entrywiseAdjointAut τ σ))) :
    FixedClauses p (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  set C := adjointGroup τ K with hC
  set δ := entrywiseAdjointAut τ σ with hδ
  set J := fixedFieldImage τ σ with hJ
  set N := signalizerFixedSubgroup δ with hN
  have hmemN : ∀ g : C, g ∈ N ↔ (g : ModGL τ K) ∈ J := by
    intro g
    rw [← hΓJ, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨g.2, congrArg Subtype.val (show δ g = g from h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hCbot : Subgroup.centralizer (N : Set C) = ⊥ :=
    centralizer_eq_bot_of_nonLocalized (hNL hF)
  refine fixedClauses_of_stabilizer (by rw [hδ, orderOf_entrywiseAdjointAut hrank σ, hσ]) hF hNL
    fun g hg => ?_
  exact mem_zpowers_of_fixes_of_outer_abelian (δ := δ) (N := N) (fun x => Iff.rfl) hOut hCbot
    (fun β hβ hβfix => hS2 β hβ fun j hj => hβfix j ((hmemN j).2 hj)) hg

theorem fixedClauses_of_fixedFieldImage_S2
    {τ : Tag} {K : Type} [Field K] [Finite K] {p : ℕ}
    (σ : K ≃+* K) (hσ : orderOf σ = p) (hrank : 0 < τ.rank)
    (hΓJ : entrywiseFixedGroup τ σ = fixedFieldImage τ σ)
    (hJs : IsSimpleGroup (fixedFieldImage τ σ))
    (hOut : ∀ a b : MulAut (adjointGroup τ K), ⁅a, b⁆ ∈
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (hS2 : ∀ β : MulAut (adjointGroup τ K),
      β * entrywiseAdjointAut τ σ = entrywiseAdjointAut τ σ * β →
      (∀ j : adjointGroup τ K, (j : ModGL τ K) ∈ fixedFieldImage τ σ → β j = j) →
        β ∈ Subgroup.zpowers (entrywiseAdjointAut τ σ))
    (hNL : FStarSimple (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) →
      NonLocalized (signalizerFixedSubgroup (entrywiseAdjointAut τ σ))) :
    FixedClauses p (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) := by
  classical
  set C := adjointGroup τ K with hC
  set δ := entrywiseAdjointAut τ σ with hδ
  set J := fixedFieldImage τ σ with hJ
  set N := signalizerFixedSubgroup δ with hN
  have hmemN : ∀ g : C, g ∈ N ↔ (g : ModGL τ K) ∈ J := by
    intro g
    rw [← hΓJ, mem_entrywiseFixedGroup]
    constructor
    · intro h
      exact ⟨g.2, congrArg Subtype.val (show δ g = g from h)⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hmap : N.map C.subtype = J := by
    ext y
    constructor
    · rintro ⟨g, hg, rfl⟩
      exact (hmemN g).1 hg
    · intro hy
      have hyC : y ∈ C := ((mem_entrywiseFixedGroup).1 (hΓJ ▸ hy)).1
      exact ⟨⟨y, hyC⟩, (hmemN ⟨y, hyC⟩).2 hy, rfl⟩
  let eNJ : N ≃* J :=
    (N.equivMapOfInjective C.subtype C.subtype_injective).trans (MulEquiv.subgroupCongr hmap)
  have hsN : IsSimpleGroup N := eNJ.isSimpleGroup
  have hnN : ∃ a b : N, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply not_commute_fixedFieldImage hrank σ
    intro a b
    have h := hcon (eNJ.symm a) (eNJ.symm b)
    apply eNJ.symm.injective
    rw [map_mul, map_mul]
    exact h
  exact fixedClauses_of_FStarSimple_S2 σ hσ hrank hΓJ (fStarSimple_of_simple hsN hnN) hOut hS2 hNL

end CFSG.SignalizerFunctorTheorem.CatalogBridge
