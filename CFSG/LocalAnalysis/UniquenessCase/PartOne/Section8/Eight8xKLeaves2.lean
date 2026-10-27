module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight56Spine

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor IsSp4 IsG2)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (List880 IsA6Z3 IsA7Z3 IsM22Z3 IsSU5)

@[expose] def List880PRankInspection : Prop :=
  ∀ (X : Type) [Group X] [Finite X], List880 X → ∀ p : ℕ, p.Prime → 5 ≤ p →
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
      ¬ (IsA6Z3 X ∨ IsA7Z3 X ∨ IsM22Z3 X) ∧
        (((IsSpor X .J2 ∨ IsSpor X .HS ∨ IsSpor X .Ru) ∧ p = 5 ∧
            CFSG.Open.pRank p (⊤ : Subgroup X) = 2) ∨
          (IsSpor X .J4 ∧ p = 11 ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2) ∨
          (∃ n : ℕ, 1 < n ∧ (IsSp4 X n ∨ IsG2 X n) ∧ 2 ^ (2 * n) ≡ 1 [MOD p] ∧
            CFSG.Open.pRank p (⊤ : Subgroup X) = 2) ∨
          (∃ n : ℕ, IsSU5 X n ∧
            (p ∣ 2 ^ n + 1 ∨ (2 ^ n ≡ 1 [MOD p] ∧ CFSG.Open.pRank p (⊤ : Subgroup X) = 2))))

@[expose] def J2FivePRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .J2 →
    CFSG.Open.pRank 5 (⊤ : Subgroup X) = 2 ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ 5 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 1

@[expose] def List880CRExc (X : Type) [Group X] (p : ℕ) : Prop :=
  p = 5 ∧ ∃ m : ℕ, 2 < m ∧ IsSU5 X m ∧ Nat.card (center X) = 1 ∧ 5 ∣ 2 ^ m + 1 ∧ ¬ 25 ∣ 2 ^ m + 1

@[expose] def List880CentralizerRanks : Prop :=
  ∀ (X H : Type) [Group X] [Finite X] [Group H] [Finite H] (ι : X →* H),
    Function.Injective ι → ι.range.Normal → List880 X → ¬ IsSpor X .J2 →
    CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 →
    ∀ p : ℕ, p.Prime → 5 ≤ p → 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) →
      3 ≤ CFSG.Open.pRank p (⊤ : Subgroup H) → ¬ List880CRExc X p →
      ∀ S : Subgroup X, IsSylowOf 3 S ⊤ →
        0 < CFSG.Open.pRank p (centralizer ((ι '' (S : Set X) : Set H))) ∧
          ∀ e ∈ S, orderOf e = 3 → 2 ≤ CFSG.Open.pRank p (centralizer ({ι e} : Set H))

@[expose] def List880ThreeInE9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], List880 X → CFSG.Open.pRank 3 (⊤ : Subgroup X) = 2 →
    ∀ S : Subgroup X, IsSylowOf 3 S ⊤ → ∀ e ∈ S, orderOf e = 3 →
      ∃ E : Subgroup X, e ∈ E ∧ E ≤ S ∧ IsElemAbelian 3 E ∧ Nat.card E = 9

@[expose] def J2ThreeClasses : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .J2 → ∀ S : Subgroup X, IsSylowOf 3 S ⊤ →
    Nat.card (ZOf S) = 3 ∧
      (∃ A : Subgroup X, A ≤ S ∧ Nat.card A = 3 ∧ A ∉ MConjSet (⊤ : Subgroup X) (ZOf S) ∧
        ∀ B : Subgroup X, Nat.card B = 3 →
          B ∈ MConjSet (⊤ : Subgroup X) (ZOf S) ∨ B ∈ MConjSet (⊤ : Subgroup X) A) ∧
      (∀ α : MulAut X,
        (ZOf S).map α.toMonoidHom ∈ MConjSet (⊤ : Subgroup X) (ZOf S)) ∧
      (∀ B : Subgroup X, B ≤ S → B ∈ MConjSet (⊤ : Subgroup X) (ZOf S) → B = ZOf S)

@[expose] def J2CentralizerThreeA : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsSpor X .J2 → ∀ S : Subgroup X, IsSylowOf 3 S ⊤ →
    IsA6Z3 ↥(centralizer (ZOf S : Set X))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
