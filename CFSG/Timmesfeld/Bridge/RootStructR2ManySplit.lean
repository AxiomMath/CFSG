module

public import CFSG.Timmesfeld.Bridge.RootStructR2Many

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

@[expose] def ThinGateCoreSmallStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (q : ℕ), ThinGateCounter G D → ThinGateCount G D q 2 2 →
    ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a →
      Nat.card ↥(nCore D a ⊓ nCore D d) < q ^ 3 →
      (∀ z ∈ nCore D a, (∀ m ∈ nCore D a, Commute z m) → z ∈ rootGroup D a) ∧
        Nat.card ↥(nCore D a ⊓ nCore D d) = q ^ 2

@[expose] def ThinGateCoreOneStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (q : ℕ), ThinGateCounter G D → ThinGateCount G D q 2 2 →
    ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a →
      (∀ z ∈ nCore D a, (∀ m ∈ nCore D a, Commute z m) → z ∈ rootGroup D a) →
      Nat.card ↥(nCore D a ⊓ nCore D d) = q ^ 2 → False

theorem thinGateCoreStep_of (hs : ThinGateCoreSmallStep) (h1 : ThinGateCoreOneStep) :
    ThinGateCoreStep := by
  intro G _ D q C K a ha d hd had hadD hdT
  by_contra h
  push Not at h
  obtain ⟨hZ, hN⟩ := hs G D q C K a ha d hd had hadD hdT h
  exact h1 G D q C K a ha d hd had hadD hdT hZ hN

end CFSG.Timmesfeld.Bridge
