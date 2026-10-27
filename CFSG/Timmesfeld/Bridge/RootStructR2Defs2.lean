module

public import CFSG.Timmesfeld.Bridge.RootStructWTIProps
public import CFSG.Timmesfeld.Bridge.RootStructR2Gate
public import CFSG.Timmesfeld.Bridge.RootStructThmE

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G]

@[expose] def oneOmega (D : Set G) (a : G) : Set (Subgroup G) :=
  {B | ∃ x ∈ D, B = rootGroup D x ∧ ¬ Commute a x ∧ Odd (orderOf (a * x)) ∧ OneOpposite D a x}

@[expose] def gatedLines (D : Set G) (a x : G) : Set (Subgroup G) :=
  {L | L ∈ rootLines D a ∧ ∃ p ∈ D, p ∈ L ∧ orderOf (x * p) = 4}

@[expose] def gatedPoints (D : Set G) (a : G) (T : Subgroup G) : Set (Subgroup G) :=
  {B | B ∈ oneOmega D a ∧ ∃ x ∈ D, B = rootGroup D x ∧ ∃ p ∈ D, p ∈ T ∧ orderOf (x * p) = 4}

structure ThinGateCounter (G : Type) [Group G] (D : Set G) : Prop where
  hyp : Hyp G D
  IH : RootIHStructE G
  nontrivial : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d
  closure : RootClosure D
  special : SpecialClosure D
  conn : Moufang.ExcCollConnected D
  allTI : AllLinesTI D
  three : ThreeLines D
  gen : ∀ b ∈ D, ∀ a ∈ D, ∀ x ∈ D, Commute b a → b * a ∈ D → a ∉ rootSet D b →
    ¬ Commute b x → Odd (orderOf (b * x)) → OneOpposite D b x →
    (∀ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a → orderOf (x * p) ≠ 4) →
    rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x = ⊤
  counter : ¬ ThinGate D

structure ThinGateCount (G : Type) [Group G] (D : Set G) (q n k : ℕ) : Prop where
  card_rootGroup : ∀ a ∈ D, Nat.card (rootGroup D a) = q
  ncard_rootLines : ∀ a ∈ D, (rootLines D a).ncard = q ^ n + 1
  ncard_gatedLines : ∀ a ∈ D, ∀ x ∈ D, ¬ Commute a x → Odd (orderOf (a * x)) →
    OneOpposite D a x → (gatedLines D a x).ncard = k
  ncard_gatedPoints : ∀ a ∈ D, ∀ T ∈ rootLines D a, (gatedPoints D a T).ncard = q ^ (2 * n + 3)
  ncard_oneOmega : ∀ a ∈ D, (oneOmega D a).ncard * k = (q ^ n + 1) * q ^ (2 * n + 3)

@[expose] def ThinGateManyStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (q n : ℕ), ThinGateCounter G D → ThinGateCount G D q n 2 →
    2 ≤ n → False

@[expose] def ThinGateOneStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G) (q k : ℕ), ThinGateCounter G D → ThinGateCount G D q 1 k →
    (k = 1 ∨ k = 2 ∨ k = q) → False

end CFSG.Timmesfeld.Bridge
