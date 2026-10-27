module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements

public section

open CFSG.Open (signalizerFixedSubgroup)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem fixedFieldImage_subgroupOf_le
    {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K) :
    (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K) ≤
      signalizerFixedSubgroup (entrywiseAdjointAut τ σ) := fun _ hx =>
  Subtype.ext ((mem_entrywiseFixedGroup.1 (fixedFieldImage_le (Subgroup.mem_subgroupOf.1 hx))).2)

theorem nonLocalized_fixed_entrywiseAdjointAut
    {τ : Tag} {K : Type} [Field K] (σ : K ≃+* K)
    (h : NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K))) :
    NonLocalized (signalizerFixedSubgroup (entrywiseAdjointAut τ σ)) :=
  NonLocalized.mono (fixedFieldImage_subgroupOf_le σ) h

@[expose] def ChevalleySubfieldNL
    (τ : Tag) (K : Type) [Field K] (p : ℕ) : Prop :=
  ∀ σ : K ≃+* K, orderOf σ = p →
    NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K))

theorem ChevalleySubfieldNL.of_chevalley
    (hNL : SubfieldNonLocalizedChevalley) {τ : Tag}
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {K : Type} [Field K] [Finite K]
    (hsC : IsSimpleGroup (adjointGroup τ K)) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpC : ¬ p ∣ Nat.card (adjointGroup τ K)) : ChevalleySubfieldNL τ K p :=
  fun σ hσ => hNL τ hτ K hsC p hp hp2 hpC σ hσ

end CFSG.SignalizerFunctorTheorem.CatalogBridge
