module

public import CFSG.Quasithin.H13.NQCoreP134Inputs

public section

namespace CFSG.Quasithin.H13.NQCore

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

@[expose] def IsoInvariant (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X Y : Type) [Group X] [Group Y], X ≃* Y → F X → F Y

structure OddCfg {A : Type} [Group A] (p : ℕ) (L P T : Subgroup A) : Prop where
  normal : L.Normal
  le : P ≤ L
  exp : ∀ x ∈ P, x ^ p = 1
  card : Nat.card P = p ^ 2 ∨ Nat.card P = p ^ 3
  nonab : Nat.card P = p ^ 3 → ∃ a ∈ P, ∃ b ∈ P, a * b ≠ b * a
  sylow : IsSylowTwoOf T ⊤
  mul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s
  irred : ∀ U : Subgroup A, ⁅P, P⁆ ≤ U → U ≤ P →
    T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (U : Set A) → U = ⁅P, P⁆ ∨ U = P

@[expose] def NoOddCfg (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A), 5 ≤ p →
    F ↥L → OddCfg p L P T → False

@[expose] def NoOddConfigQ (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A), 5 ≤ p →
    OddConfig p L P T →
    (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) →
    F (↥L ⧸ Subgroup.center ↥L) → False

@[expose] def Psp4EvenSimple : Prop :=
  ∀ (n : ℕ) (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A), 5 ≤ p →
    StatedClassicalModel ↥L .PSp 2 2 n → OddCfg p L P T →
      Nat.card P = p ^ 2 ∧ Even n ∧ p ∣ 2 ^ n - 1 ∧ AutCyclic T P

@[expose] def Psl3OddSimple : Prop :=
  ∀ (r : ℕ) (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A),
    r.Prime → r ≠ 2 → 5 ≤ p → StatedClassicalModel ↥L .PSL 3 r 1 → OddCfg p L P T →
      r = p ∧ Nat.card P = p ^ 2

@[expose] def LiePsp4Even : Prop :=
  ∀ (n : ℕ) (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A), 5 ≤ p →
    OddConfig p L P T →
    (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) →
    StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 n →
      Nat.card P = p ^ 2 ∧ Even n ∧ p ∣ 2 ^ n - 1 ∧ AutCyclic T P

@[expose] def LiePsl3Odd : Prop :=
  ∀ (r : ℕ) (A : Type) [Group A] [Finite A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A),
    r.Prime → r ≠ 2 → 5 ≤ p → OddConfig p L P T →
    (Nat.card (Subgroup.center ↥L) = 1 ∨ Nat.card (Subgroup.center ↥L) = 3) →
    StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSL 3 r 1 → r = p ∧ Nat.card P = p ^ 2

@[expose] def LieAlt : Prop :=
  ∀ n : ℕ, 5 ≤ n → n ≤ 8 →
    NoOddConfigQ fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin n))

@[expose] def LiePsl45 : Prop :=
  ∀ n : ℕ, (n = 4 ∨ n = 5) →
    NoOddConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL n 2 1

@[expose] def LiePsl2Odd : Prop :=
  ∀ r f : ℕ, r.Prime → r ≠ 2 → (f = 1 ∨ f = 2) →
    NoOddConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 r f

@[expose] def LiePsl2Even : Prop :=
  ∀ n : ℕ, NoOddConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 n

@[expose] def LieSz : Prop :=
  ∀ n : ℕ, NoOddConfigQ fun (X : Type) [Group X] => SuzukiModel X 2 n

@[expose] def LiePsu3Even : Prop :=
  ∀ n : ℕ, NoOddConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n

@[expose] def LiePsl3Even : Prop :=
  ∀ n : ℕ, NoOddConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n

@[expose] def LiePsu3Odd : Prop :=
  ∀ r : ℕ, r.Prime → r ≠ 2 →
    NoOddConfigQ fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 r 1

@[expose] def LieG2Even : Prop :=
  ∀ n : ℕ, NoOddConfigQ fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 n

@[expose] def LieD4Even : Prop :=
  ∀ n : ℕ, NoOddConfigQ fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n

@[expose] def LieF4Even : Prop :=
  ∀ n : ℕ, NoOddConfigQ fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n

@[expose] def LieTits : Prop :=
  NoOddConfigQ fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1

structure Facts134OddLie : Prop where
  alt : LieAlt
  psl45 : LiePsl45
  psl2Odd : LiePsl2Odd
  psl2Even : LiePsl2Even
  sz : LieSz
  psu3Even : LiePsu3Even
  psl3Even : LiePsl3Even
  psu3Odd : LiePsu3Odd
  g2Even : LieG2Even
  d4Even : LieD4Even
  f4Even : LieF4Even
  tits : LieTits
  psp4Even : LiePsp4Even
  psl3Odd : LiePsl3Odd

end CFSG.Quasithin.H13.NQCore
