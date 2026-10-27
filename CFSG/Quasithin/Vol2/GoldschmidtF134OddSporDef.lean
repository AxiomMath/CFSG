module

public import CFSG.Quasithin.H13.NQCoreP134Inputs

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Blueprint

@[expose] def NoPowerOvergroup (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X : Type) [Group X] [Finite X], F X → ∀ (p a : ℕ), p.Prime → 5 ≤ p → (a = 2 ∨ a = 3) →
    ∀ H S : Subgroup X, IsPGroup 2 S → ¬ 2 ∣ S.index → S ≤ H →
      Nat.card H = p ^ a * Nat.card S → False

@[expose] def NoOddConfigSpor (s : TauCeti.SporadicName) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A), 5 ≤ p →
    OddConfig p L P T →
    (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) →
    Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* NativeSporadic.Carrier s) → False

structure Facts134OddSporadic : Prop where
  m11 : NoOddConfigSpor .M11
  m12 : NoOddConfigSpor .M12
  m22 : NoOddConfigSpor .M22
  m23 : NoOddConfigSpor .M23
  m24 : NoOddConfigSpor .M24
  j1 : NoOddConfigSpor .J1
  j2 : NoOddConfigSpor .J2
  hs : NoOddConfigSpor .HS
  he : NoOddConfigSpor .He
  ru : NoOddConfigSpor .Ru
  j4 : NoOddConfigSpor .J4

end CFSG.Quasithin.H13.NQCore
