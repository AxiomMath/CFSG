module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Inputs5
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

structure E9Config {A : Type} [Group A] (L P T : Subgroup A) : Prop where
  hyp : SQTKHypCat A
  normal : L.Normal
  le : P ≤ L
  card : Nat.card P = 9
  exp : ∀ x ∈ P, x ^ 3 = 1
  sylow : IsSylowTwoOf T ⊤
  mul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s
  irred : ∀ U : Subgroup A, U ≤ P →
    T ⊓ Subgroup.normalizer (P : Set A) ≤ Subgroup.normalizer (U : Set A) → U = ⊥ ∨ U = P

@[expose] def NoE9Config (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A), F ↥L → E9Config L P T → False

@[expose] def OrderThree (F : ∀ (X : Type) [Group X], Prop) : Prop :=
  ∀ (X : Type) [Group X], F X → 3 ∣ Nat.card X

@[expose] def TheoremCSimple : Prop :=
  ∀ (S : Type) [Group S] [Finite S] [IsSimpleGroup S], (∃ a b : S, a * b ≠ b * a) →
    CFSG.SectionRank.IsSQTKCat S → CFSG.Milestones.SQTKSimpleList S

structure Facts134E9He : Prop where
  alt6 : NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 6))
  alt7 : NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* alternatingGroup (Fin 7))
  psl2OddOrder : ∀ p f : ℕ, p.Prime → p ≠ 2 → (f = 1 ∨ f = 2) →
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 p f
  psl2OddCyclic : ∀ p f : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → (f = 1 ∨ f = 2) →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 p f
  psl2Nine : NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 3 2
  psl3OddOrder : ∀ p : ℕ, p.Prime → p ≠ 2 →
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1
  psl3Minus : ∀ p : ℕ, p.Prime → p ≠ 2 → p % 3 = 2 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1
  psl3Plus : ∀ p : ℕ, p.Prime → p % 3 = 1 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 p 1
  psu3OddOrder : ∀ p : ℕ, p.Prime → p ≠ 2 →
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1
  psu3Three : NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 3 1
  psu3Plus : ∀ p : ℕ, p.Prime → p % 3 = 1 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1
  psu3Minus : ∀ p : ℕ, p.Prime → p ≠ 2 → p % 3 = 2 →
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 p 1
  psl2EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 n
  psl2EvenCyclic : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 2 2 n
  psl2EvenBorel : ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (n : ℕ) (y : A),
    SQTKHypCat A → StatedClassicalModel ↥L .PSL 2 2 n → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3) → y ∈ B → orderOf y = 3 → Even n
  psl3EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n
  psl3Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSL 3 2 n
  psu3EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n
  psu3Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => StatedClassicalModel X .PSU 3 2 n
  psp4EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSp 2 2 n
  psp4Even : ∀ n : ℕ, ∀ (A : Type) [Group A] [Finite A] (L P T : Subgroup A),
    StatedClassicalModel ↥L .PSp 2 2 n → E9Config L P T → Even n ∧ AutCyclic T P
  g2EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 n
  g2Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .G2 2 n
  d4EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n
  d4Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => ChevalleyExceptionalModel X .trialityD4 2 n
  f4EvenOrder : ∀ n : ℕ,
    OrderThree fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n
  f4Even : ∀ n : ℕ,
    NoE9Config fun (X : Type) [Group X] => ReeTitsModel X .twistedF4 2 n
  titsOrder : OrderThree fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1
  tits : NoE9Config fun (X : Type) [Group X] => ReeTitsModel X .Tits 2 1
  szOrder : ∀ n : ℕ, ∀ (X : Type) [Group X], SuzukiModel X 2 n → ¬ 3 ∣ Nat.card X
  szOut : ∀ n : ℕ, ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), SQTKHypCat A →
    SuzukiModel ↥L 2 n → ∀ a ∈ Subgroup.normalizer (L : Set A),
      ∀ b ∈ Subgroup.normalizer (L : Set A), ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A)
  psl45Order : ∀ n : ℕ, (n = 4 ∨ n = 5) →
    OrderThree fun (X : Type) [Group X] => StatedClassicalModel X .PSL n 2 1
  j1Order : OrderThree fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J1)
  j1 : NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J1)
  j1Local : ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (y g : A), SQTKHypCat A →
    Nonempty (↥L ≃* NativeSporadic.Carrier .J1) → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 3) → y ∈ B → orderOf y = 3 →
      g ∈ Subgroup.normalizer (L : Set A) → g ∈ Subgroup.normalizer (U : Set A) →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup A) : Set A) → g * y * g⁻¹ = y
  m12 : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M12)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M12)
  m22 : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M22)
  m23 : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M23)
  m24 : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .M24)
  j2 : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J2)
  j4 : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .J4)
  hs : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .HS)
  he : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .He))
  ru : OrderThree (fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru)) ∧
    NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .Ru)

structure Facts134E9 : Prop extends Facts134E9He where
  heNoE9 : NoE9Config fun (X : Type) [Group X] => Nonempty (X ≃* NativeSporadic.Carrier .He)

end CFSG.Quasithin.P134
