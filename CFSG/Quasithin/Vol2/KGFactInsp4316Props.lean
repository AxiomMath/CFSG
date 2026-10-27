module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Quasithin.Background.A3Structure316

public section

namespace CFSG.Quasithin.H13.KGInsp4316

open CFSG.Open hiding StatedSL StatedSp StatedClassicalModel StatedLieTag
open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

structure Cfg4316 {X : Type} [Group X] [Finite X] (S R K : Subgroup X) (n : ℕ) (x : X) :
    Prop where
  normal : S.Normal
  simple : IsSimpleGroup ↥S
  noncomm : ∃ a b : ↥S, a * b ≠ b * a
  list : A23List ↥S
  cent : Subgroup.centralizer (S : Set X) = ⊥
  two_le : 2 ≤ n
  ne_bot : R ≠ ⊥
  isPGroup : IsPGroup 2 ↥R
  le : K ≤ S
  perfect : ⁅K, K⁆ = K
  le_normalizer : K ≤ Subgroup.normalizer (R : Set X)
  normalizer_le : Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (K : Set X)
  chi : ∃ (F : Type) (_ : Field F) (_ : Fintype F), Fintype.card F = 2 ^ n ∧
    ∃ χ : ↥K →* SL(2, F), Function.Surjective χ ∧ IsPGroup 2 ↥χ.ker
  prime : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 →
    CFSG.Open.pRank p S ≤ 1 ∨
      (p = 3 ∧ ∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧
        IsPSLEps3q s q ↥S)
  core_le : pCoreOf 2 K ≤ R
  pow : x ^ (2 ^ n - 1) = 1
  mem_normalizer : x ∈ Subgroup.normalizer (R : Set X)
  centralizes : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 K
  gen : R ≤ ⁅R, Subgroup.zpowers x⁆ ⊔ pCoreOf 2 K

@[expose] def OutTwoFam (S : Type) [Group S] : Prop :=
  (∃ n : ℕ, 5 ≤ n ∧ n ≤ 8 ∧ Nonempty (S ≃* alternatingGroup (Fin n))) ∨
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ (f = 1 ∨ f = 2) ∧ StatedClassicalModel S .PSL 2 p f) ∨
  ReeTitsModel S .Tits 2 1 ∨
  (∃ n : ℕ, (n = 4 ∨ n = 5) ∧ StatedClassicalModel S .PSL n 2 1) ∨
  (∃ s : TauCeti.SporadicName,
    (s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J1 ∨ s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru) ∧
    Nonempty (S ≃* NativeSporadic.Carrier s))

@[expose] def OddOutLie (S : Type) [Group S] : Prop :=
  (∃ p : ℕ, p.Prime ∧ p ≠ 2 ∧
    (StatedClassicalModel S .PSL 3 p 1 ∨ StatedClassicalModel S .PSU 3 p 1)) ∨
  (∃ f : ℕ,
    (2 ≤ f ∧ StatedClassicalModel S .PSL 2 2 f) ∨
    (1 ≤ f ∧ StatedClassicalModel S .PSL 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSU 3 2 f) ∨
    (2 ≤ f ∧ StatedClassicalModel S .PSp 2 2 f) ∨
    (2 ≤ f ∧ ChevalleyExceptionalModel S .G2 2 f) ∨
    (1 ≤ f ∧ ChevalleyExceptionalModel S .trialityD4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ ReeTitsModel S .twistedF4 2 f) ∨
    (Odd f ∧ 3 ≤ f ∧ SuzukiModel S 2 f))

@[expose] def Insp4316OutDer : Prop :=
  ∀ (S : Type) [Group S] [Finite S], IsSimpleGroup S → (∃ a b : S, a * b ≠ b * a) →
    (OddOutLie S ∨ ∃ (s : Bool) (q : ℕ), IsPSLEps3q s q S) →
      Odd (Nat.card ↥(commutator (Outer S)))

@[expose] def Insp4316E16m : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S R K : Subgroup X), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → A23List ↥S → Subgroup.centralizer (S : Set X) = ⊥ →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 2 ^ 2 →
    K ≤ S → ⁅K, K⁆ = K → K ≤ Subgroup.normalizer (R : Set X) →
    Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (K : Set X) →
    (∃ χ : ↥K →* SL(2, F), Function.Surjective χ ∧ IsPGroup 2 ↥χ.ker) →
    CFSG.Open.pRank 3 S ≤ 1 → R = pCoreOf 2 K → IsElemAbelian 2 R → Nat.card ↥R = 2 ^ 4 →
    (∀ R' : Subgroup X, R' ≤ R → K ≤ Subgroup.normalizer (R' : Set X) → R' = ⊥ ∨ R' = R) →
      IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S

@[expose] def Insp4316E16L : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S R K : Subgroup X), S.Normal → IsSimpleGroup ↥S →
    (∃ a b : ↥S, a * b ≠ b * a) → A23List ↥S → Subgroup.centralizer (S : Set X) = ⊥ →
    ∀ (F : Type) [Field F] [Fintype F], Fintype.card F = 2 ^ 2 →
    K ≤ S → ⁅K, K⁆ = K → K ≤ Subgroup.normalizer (R : Set X) →
    Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (K : Set X) →
    (∃ χ : ↥K →* SL(2, F), Function.Surjective χ ∧ IsPGroup 2 ↥χ.ker) →
    (∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧ IsPSLEps3q s q ↥S) →
    R = pCoreOf 2 K → IsElemAbelian 2 R → Nat.card ↥R = 2 ^ 4 →
    (∀ R' : Subgroup X, R' ≤ R → K ≤ Subgroup.normalizer (R' : Set X) → R' = ⊥ ∨ R' = R) →
      IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S

@[expose] def Insp4316L3eps : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S R K : Subgroup X) (n : ℕ) (x : X), Cfg4316 S R K n x →
    R ≤ S → ∀ x' ∈ Subgroup.zpowers x, orderOf x' = 3 → x' ∈ S →
    (∃ (s : Bool) (q : ℕ), Int.ModEq 3 (q : ℤ) (if s then 1 else -1) ∧ IsPSLEps3q s q ↥S) →
      n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S)

@[expose] def Insp4316OutLie : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (S R K : Subgroup X) (n : ℕ) (x : X), Cfg4316 S R K n x →
    R ≤ S → OddOutLie ↥S → ∀ x' ∈ Subgroup.zpowers x, ∀ p : ℕ, p.Prime → p ≠ 2 →
      p ∣ 2 ^ n - 1 → orderOf x' = p → x' ∉ S → n = 2 ∧ (IsPSL 3 2 2 ↥S ∨ IsPSU 3 5 1 ↥S)

end CFSG.Quasithin.H13.KGInsp4316
