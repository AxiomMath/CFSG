module

public import CFSG.RankThree.PartOne.S11b.OuterPrimeTwoGeneral

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Blueprint CFSG.ComponentClassification.OuterAutomorphisms

@[expose] def SporadicOuterSmall (s : TauCeti.SporadicName) : Prop :=
  Nat.card (Outer (NativeSporadic.Carrier s)) < 40 ∨
    ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer (NativeSporadic.Carrier s))

theorem outerPrimeTwoTrivial_of_sporadicOuterSmall {s : TauCeti.SporadicName}
    (hs : SporadicOuterSmall s) {S : Type} [Group S] [Finite S]
    (e : S ≃* NativeSporadic.Carrier s) : OuterPrimeTwoTrivial S := by
  have hcard : Nat.card (Outer S) = Nat.card (Outer (NativeSporadic.Carrier s)) :=
    Nat.card_congr (equivalence e).toEquiv
  rcases hs with h | h
  · exact outerPrimeTwoTrivial_of_card_lt (by rw [hcard]; exact h)
  · exact outerPrimeTwoTrivial_of_not_dvd fun q hq hq5 => by rw [hcard]; exact h q hq hq5

theorem outerPrimeTwoTrivial_sporadic_of_small (hsp : ∀ s, SporadicOuterSmall s) {S : Type}
    [Group S] [Finite S] (hS : NativeSporadic.SporadicRep S) : OuterPrimeTwoTrivial S := by
  obtain ⟨s, ⟨e⟩⟩ := hS
  exact outerPrimeTwoTrivial_of_sporadicOuterSmall (hsp s) e

@[expose] def SporadicOuterSmallSimple (s : TauCeti.SporadicName) : Prop :=
  ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
    Nonempty (T ≃* NativeSporadic.Carrier s) →
      Nat.card (Outer T) < 40 ∨ ∀ q : ℕ, q.Prime → 5 ≤ q → ¬ q ∣ Nat.card (Outer T)

@[expose] def SporadicOuterOrderLeTwoSimple : Prop :=
  ∀ s : TauCeti.SporadicName,
    (s = .Co1 ∨ s = .Co2 ∨ s = .HN ∨ s = .Ly ∨ s = .Th ∨ s = .B ∨ s = .M) →
      ∀ (T : Type) [Group T] [Finite T] [IsSimpleGroup T], (∃ a b : T, a * b ≠ b * a) →
        Nonempty (T ≃* NativeSporadic.Carrier s) → Nat.card (Outer T) ≤ 2

theorem SporadicOuterSmall.toSimple {s : TauCeti.SporadicName} (hs : SporadicOuterSmall s) :
    SporadicOuterSmallSimple s := by
  intro T _ _ _ _ ⟨e⟩
  have hcard : Nat.card (Outer T) = Nat.card (Outer (NativeSporadic.Carrier s)) :=
    Nat.card_congr (equivalence e).toEquiv
  rw [hcard]
  exact hs

theorem outerPrimeTwoTrivial_of_sporadicOuterSmallSimple {s : TauCeti.SporadicName}
    (hs : SporadicOuterSmallSimple s) {S : Type} [Group S] [Finite S] [IsSimpleGroup S]
    (hnonab : ∃ a b : S, a * b ≠ b * a) (e : S ≃* NativeSporadic.Carrier s) :
    OuterPrimeTwoTrivial S := by
  rcases hs S hnonab ⟨e⟩ with h | h
  · exact outerPrimeTwoTrivial_of_card_lt h
  · exact outerPrimeTwoTrivial_of_not_dvd h

theorem outerPrimeTwoTrivial_sporadic_of_small_simple (hsp : ∀ s, SporadicOuterSmallSimple s)
    {S : Type} [Group S] [Finite S] [IsSimpleGroup S] (hnonab : ∃ a b : S, a * b ≠ b * a)
    (hS : NativeSporadic.SporadicRep S) : OuterPrimeTwoTrivial S := by
  obtain ⟨s, ⟨e⟩⟩ := hS
  exact outerPrimeTwoTrivial_of_sporadicOuterSmallSimple (hsp s) hnonab e

end CFSG.RankThree.PartOne
