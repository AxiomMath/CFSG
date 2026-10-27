module

public import CFSG.Timmesfeld.Bridge.RootStructR2Defs
public import CFSG.Timmesfeld.Bridge.RootStructBasic
public import CFSG.Timmesfeld.Exceptional.CaseIConnected

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G]

structure LineSetting (G : Type*) [Group G] (D : Set G) : Prop where
  hyp : Hyp G D
  closure : RootClosure D
  special : SpecialClosure D
  conn : Moufang.ExcCollConnected D
  line : ∃ a ∈ D, ∃ d ∈ D, Commute a d ∧ a * d ∈ D ∧ d ∉ rootSet D a ∧ LineTI D a d

@[expose] def rootLines (D : Set G) (a : G) : Set (Subgroup G) :=
  {L | ∃ b ∈ D, Commute a b ∧ a * b ∈ D ∧ b ∉ rootSet D a ∧ L = rootGroup D a ⊔ rootGroup D b}

@[expose] def lineGroup (D : Set G) (a d : G) : Subgroup G :=
  ⨆ g : Subgroup.centralizer ({a} : Set G),
    ((nCore D d ⊓ Subgroup.centralizer {a}) ⊔ nCore D a).map (MulAut.conj (g : G)).toMonoidHom

@[expose] def RootLinesRegularStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), LineSetting G D →
    ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a →
    ∀ b ∈ D, Commute a b → a * b ∈ D → b ∉ rootGroup D a ⊔ rootGroup D d →
    ∀ c ∈ D, Commute a c → a * c ∈ D → c ∉ rootGroup D a ⊔ rootGroup D d →
      (∃ k ∈ nCore D d ⊓ Subgroup.centralizer {a},
        (rootGroup D a ⊔ rootGroup D b).map (MulAut.conj k).toMonoidHom =
          rootGroup D a ⊔ rootGroup D c) ∧
      ∀ k ∈ nCore D d ⊓ Subgroup.centralizer {a},
        (rootGroup D a ⊔ rootGroup D b).map (MulAut.conj k).toMonoidHom =
          rootGroup D a ⊔ rootGroup D b → k ∈ nCore D a

@[expose] def RootLinesPowerStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), LineSetting G D →
    ∀ a ∈ D, ∃ n : ℕ, (rootLines D a).ncard = Nat.card (rootGroup D a) ^ n + 1

@[expose] def RootLinesTorusStep : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), LineSetting G D →
    ∀ a ∈ D, ∀ d ∈ D, Commute a d → a * d ∈ D → d ∉ rootSet D a → 3 ≤ (rootLines D a).ncard →
    ∀ L₁ ∈ rootLines D a, ∀ L₂ ∈ rootLines D a, L₁ ≠ L₂ →
      ∃ h ∈ lineGroup D a d, orderOf h + 2 = (rootLines D a).ncard ∧
        L₁.map (MulAut.conj h).toMonoidHom = L₁ ∧ L₂.map (MulAut.conj h).toMonoidHom = L₂ ∧
        ∀ L ∈ rootLines D a, ∀ L' ∈ rootLines D a, L ≠ L₁ → L ≠ L₂ → L' ≠ L₁ → L' ≠ L₂ →
          ∃ i < orderOf h, L.map (MulAut.conj (h ^ i)).toMonoidHom = L'

end CFSG.Timmesfeld.Bridge
