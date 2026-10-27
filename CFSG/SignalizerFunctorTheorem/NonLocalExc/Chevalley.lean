module

public import CFSG.SignalizerFunctorTheorem.NonLocalExc.F4Even
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.ChevalleyE
public import CFSG.SignalizerFunctorTheorem.NonLocalExc.G2Two
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.NonLocalizedStatements

public section

namespace CFSG.SignalizerFunctorTheorem.NonLocalExc

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SignalizerFunctorTheorem.CatalogBridge

variable {K : Type} [Field K] [Finite K]

theorem nonLocalized_G2
    (σ : K ≃+* K) :
    NonLocalized ((fixedFieldImage .G2 σ).subgroupOf (adjointGroup .G2 K)) := by
  by_cases hk : Nat.card (fixSubfield σ) = 2
  · exact nonLocalized_G2_of_card_eq_two σ hk
  · exact nonLocalized_G2_of_card_ne_two σ hk

theorem nonLocalized_chevalley
    (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (σ : K ≃+* K) :
    NonLocalized ((fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)) := by
  rcases hτ with rfl | rfl | rfl | rfl | rfl
  exacts [nonLocalized_G2 σ, nonLocalized_F4 σ, nonLocalized_E6 σ, nonLocalized_E7 σ,
    nonLocalized_E8 σ]

theorem subfieldNonLocalizedChevalley
    : SubfieldNonLocalizedChevalley :=
  fun τ hτ _ _ _ _ _ _ _ _ σ _ => nonLocalized_chevalley τ hτ σ

end CFSG.SignalizerFunctorTheorem.NonLocalExc
