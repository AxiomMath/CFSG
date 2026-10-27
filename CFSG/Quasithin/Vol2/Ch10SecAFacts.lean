module

public import CFSG.Quasithin.Vol2.Ch10SecAShape

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank

@[expose] def FactOrthA5 : Prop :=
  ∀ (V : Type) [CommGroup V] (H : Subgroup (MulAut V)) (U Z : Subgroup V),
    BinaryOrthogonalFour H U Z 1 → AlternatingNatural H U Z 5

@[expose] def FactSp4TwoNormal : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ N : Subgroup ↥(StatedSp 2 K), N.Normal → CFSG.IsQuasisimple ↥N → Nat.card ↥N = 360

@[expose] def FactG2TwoNormal : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (H : Type) [Group H] (π : ↥(quasithinG2 K) →* H), Function.Surjective π →
      ∀ N : Subgroup H, N.Normal → CFSG.IsQuasisimple ↥N → Nat.card ↥N = 6048

@[expose] def FactB4aG2 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (n : ℕ), 2 ≤ n → Nat.card K = 2 ^ n →
    ∀ (X : Type) [Group X], IsShapeGroup X →
      ∀ π : ↥(quasithinG2 K) →* X, ¬ Function.Surjective π

@[expose] def FactB4aG2Derived : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = 2 →
    ∀ (X : Type) [Group X], IsShapeGroup X →
      ∀ π : ↥⁅quasithinG2 K, quasithinG2 K⁆ →* X, ¬ Function.Surjective π

@[expose] def FactB4aNineTensor : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (a : ℕ), 1 ≤ a → Nat.card K = 2 ^ (2 * a) →
    ∀ (X : Type) [Group X], IsShapeGroup X →
      ∀ π : ↥(StatedSL 3 K) →* X, ¬ Function.Surjective π

@[expose] def FactB4aSU3 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (a : ℕ), Nat.card K = (2 ^ a) ^ 2 →
    ∀ (X : Type) [Group X], IsShapeGroup X →
      ∀ π : ↥(StatedSU 3 (2 ^ a) K) →* X, ¬ Function.Surjective π

@[expose] def FactB4aSp4Twisted : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (a : ℕ), 1 ≤ a → Nat.card K = 2 ^ (2 * a) →
    ∀ (X : Type) [Group X], IsShapeGroup X →
      ∀ π : ↥(StatedSp 2 K) →* X, ¬ Function.Surjective π

@[expose] def FactB4aM12 : Prop :=
  ∀ eY : G6.PermMod 24, eY ∈ golayC → hammingNorm (Multiplicative.toAdd eY) = 12 →
    ∀ (X : Type) [Group X], IsShapeGroup X →
      ∀ π : ↥(m24Fix eY) →* X, ¬ Function.Surjective π

@[expose] def FactB4aM22 : Prop :=
  ∀ x y : Fin 24, x ≠ y → ∀ (X : Type) [Group X], IsShapeGroup X →
    ∀ π : ↥(CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x ⊓
      MulAction.stabilizer (Equiv.Perm (Fin 24)) y) →* X, ¬ Function.Surjective π

@[expose] def FactB4aM23 : Prop :=
  ∀ x : Fin 24, ∀ (X : Type) [Group X], IsShapeGroup X →
    ∀ π : ↥(CFSG.Monster.Code.AutPerm ⊓ MulAction.stabilizer (Equiv.Perm (Fin 24)) x) →* X,
      ¬ Function.Surjective π

@[expose] def FactB4aM24 : Prop :=
  ∀ (X : Type) [Group X], IsShapeGroup X →
    ∀ π : ↥CFSG.Monster.Code.AutPerm →* X, ¬ Function.Surjective π

@[expose] def FactB4aJ2 : Prop :=
  ∀ (X : Type) [Group X], IsShapeGroup X →
    ¬ Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.Carrier .J2)

structure Facts10_1 : Prop where
  orthA5 : FactOrthA5
  sp4Two : FactSp4TwoNormal
  g2Two : FactG2TwoNormal
  g2 : FactB4aG2
  g2Derived : FactB4aG2Derived
  nineTensor : FactB4aNineTensor
  su3 : FactB4aSU3
  sp4Twisted : FactB4aSp4Twisted
  m12 : FactB4aM12
  m22 : FactB4aM22
  m23 : FactB4aM23
  m24 : FactB4aM24
  j2 : FactB4aJ2

end CFSG.Quasithin.Vol2.Ch10.SecA
