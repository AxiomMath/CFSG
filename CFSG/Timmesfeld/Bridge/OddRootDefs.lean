module

public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.Timmesfeld.Bridge.OddTranspBasic

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.Timmesfeld.Bridge.OddTransp CFSG.BenderSuzuki

structure Hyp (G : Type) [Group G] (D : Set G) : Prop where
  setup : Asc72.Setup G D
  o2 : CFSG.pCore 2 G = ⊥
  sq : OddTransp.MeetsSq D
  conn : ¬ Connectivity.Disconnected D

@[expose] def PSL2Pair {G : Type} [Group G] (D : Set G) (d x : G) : Prop :=
  ∃ n : ℕ, 2 ≤ n ∧
    Nonempty (↥(rootGen D d x) ⧸ CFSG.pCore 2 ↥(rootGen D d x) ≃* PSL2Model n)

@[expose] def SqOut (Y : Type*) [Group Y] : Prop :=
  ∃ g : Y, (∃ k : ℕ, g ^ 2 ^ k = 1) ∧ g ^ 2 ∉ CFSG.pCore 2 Y

@[expose] def NoSzBelow (m : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Nat.card G < m → Hyp G D →
    ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → ¬ SqOut ↥(rootGen D d x)

@[expose] def Qof {G : Type} [Group G] (D : Set G) (d x : G) : Subgroup G :=
  (CFSG.pCore 2 ↥(rootGen D d x)).map (rootGen D d x).subtype

@[expose] def Wof {G : Type} [Group G] (D : Set G) (d x : G) : Subgroup G :=
  rootGroup D d ⊓ Qof D d x

end CFSG.Timmesfeld.Bridge.OddRoot
