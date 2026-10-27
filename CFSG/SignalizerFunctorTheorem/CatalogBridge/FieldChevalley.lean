module

public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyOdd
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyEvenTypes
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.FieldChevalleyE

public section

open CFSG.Open (signalizerNearPSolvable)

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem nearOrField_chevalleyF4
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .F4 ℓ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedChevalley) :
    signalizerNearPSolvable p T ∨ FieldClauses p T := by
  refine Or.inr ?_
  by_cases h2 : ℓ = 2
  · exact fieldClauses_chevalleyEvenF4 hs hm h2 hp hp2 hpT hNL
  · exact fieldClauses_chevalleyOddF4 hs hm h2 hp hp2 hpT hNL

theorem nearOrField_chevalleyE8
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    {ℓ f p : ℕ} (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .E8 ℓ f) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedChevalley) :
    signalizerNearPSolvable p T ∨ FieldClauses p T := by
  refine Or.inr ?_
  by_cases h2 : ℓ = 2
  · exact fieldClauses_chevalleyEvenE8 hs hm h2 hp hp2 hpT hNL
  · exact fieldClauses_chevalleyOddE8 hs hm h2 hp hp2 hpT hNL

theorem nearOrField_chevalleyE6
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .E6 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedChevalley) :
    signalizerNearPSolvable p T ∨ FieldClauses p T :=
  Or.inr (fieldClauses_chevalleyE6 hs hn hm hp hp2 hpT hNL)

theorem nearOrField_chevalleyE7
    {T : Type} [Group T] [Finite T] (hs : IsSimpleGroup T)
    (hn : ∃ a b : T, a * b ≠ b * a) {ℓ f p : ℕ}
    (hm : CFSG.Blueprint.ChevalleyExceptionalModel T .E7 ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpT : ¬ p ∣ Nat.card T) (hNL : SubfieldNonLocalizedChevalley) :
    signalizerNearPSolvable p T ∨ FieldClauses p T := by
  refine Or.inr ?_
  by_cases h2 : ℓ = 2
  · exact fieldClauses_chevalleyEvenE7 hs hm h2 hp hp2 hpT hNL
  · exact fieldClauses_chevalleyOddE7 hs hn hm h2 hp hp2 hpT hNL

end CFSG.SignalizerFunctorTheorem.CatalogBridge
