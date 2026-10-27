module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManySplit

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

@[expose] def ThinGateCenterStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (q : ℕ), ThinGateCounter G D → ThinGateCount G D q 2 2 →
    ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a →
      Nat.card ↥(nCore D a ⊓ nCore D d) < q ^ 3 →
      ∀ z ∈ nCore D a, (∀ m ∈ nCore D a, Commute z m) → z ∈ rootGroup D a

@[expose] def ThinGateIrrStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (q : ℕ), ThinGateCounter G D → ThinGateCount G D q 2 2 →
    ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a →
      Nat.card ↥(nCore D a ⊓ nCore D d) < q ^ 3 →
      (∀ z ∈ nCore D a, (∀ m ∈ nCore D a, Commute z m) → z ∈ rootGroup D a) →
      Nat.card ↥(nCore D a ⊓ nCore D d) = q ^ 2

theorem thinGateCoreSmallStep_of (hc : ThinGateCenterStep) (hi : ThinGateIrrStep) :
    ThinGateCoreSmallStep := by
  intro G _ D q C K a ha d hd had hadD hdT h
  have hZ := hc G D q C K a ha d hd had hadD hdT h
  exact ⟨hZ, hi G D q C K a ha d hd had hadD hdT h hZ⟩

end CFSG.Timmesfeld.Bridge
