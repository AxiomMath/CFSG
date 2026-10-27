module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.GH74.GLS.Classes

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.F6
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def W4Lem13_5Concl (W : Type) [CommGroup W] [Finite W] (_Y L : Subgroup (MulAut W))
    (t : MulAut W) : Prop :=
  (∃ n a : ℕ, a ≤ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ∧
    ((IsSLn ↥L n a ∧ BinaryNaturalSL L ⊤ ⊥ n a) ∨
      (IsSpn ↥L n a ∧ NatSpn L ⊤ ⊥ n a) ∨
      ((IsOmegaPlus ↥L n a ∧ NatOmegaPlus L ⊤ ⊥ n a) ∨
        (IsOmegaMinus ↥L n a ∧ NatOmegaMinus L ⊤ ⊥ n a)))) ∨
    (∃ n : ℕ,
      (IsSLn ↥L n 1 ∧ BinaryNaturalSL L ⊤ ⊥ n 1) ∨
      (IsSpn ↥L n 1 ∧ NatSpn L ⊤ ⊥ n 1) ∨
      (IsOmegaPlus ↥L n 1 ∧ NatOmegaPlus L ⊤ ⊥ n 1) ∨
      (IsOmegaMinus ↥L n 1 ∧ NatOmegaMinus L ⊤ ⊥ n 1) ∨
      (IsSUn ↥L n 1 ∧ NatSUn L ⊤ ⊥ n 1) ∨
      (LieModel ↥L .PSU 3 3 1 ∧ G2NaturalDerived L ⊤ ⊥ 1)) ∨
    (IsHat ↥L ↥(alternatingGroup (Fin 6)) ∧ Nat.card W = 2 ^ 6) ∨
    (∃ (S : Type) (_ : Group S), LieModel S .PSU 4 3 1 ∧ IsHat ↥L S ∧
      Nat.card W = 2 ^ 12) ∨
    (∃ n : ℕ, IsAlt ↥L n ∧ AlternatingNatural L ⊤ ⊥ n) ∨
    (IsAlt ↥L 7 ∧ Nat.card W = 2 ^ 4) ∨
    (IsSpn ↥L 6 1 ∧ Nat.card W = 2 ^ 8) ∨
    (IsSLn ↥L 5 1 ∧ Nat.card W = 2 ^ 10) ∨
    (IsSpor ↥L .M22 ∧ Nat.card W = 2 ^ 10) ∨
    (LieModel ↥L .PSL 3 2 2 ∧ Nat.card W = 2 ^ 9) ∨
    (IsL3 ↥L 1 ∧ Nat.card W = 2 ^ 8)

theorem w4Lem13_5_iff_concl : W4Lem13_5 ↔
    ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
      ∀ Y L : Subgroup (MulAut W), ∀ t : MulAut W,
        Is135Context Y L → t ∈ Y → orderOf t = 2 →
        E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 → W4Lem13_5Concl W Y L t :=
  Iff.rfl

section Intro

variable {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)} {t : MulAut W}

theorem W4Lem13_5Concl.of_hatA6
    (h : IsHat ↥L ↥(alternatingGroup (Fin 6)) ∧ Nat.card W = 2 ^ 6) :
    W4Lem13_5Concl W Y L t :=
  Or.inr (Or.inr (Or.inl h))

theorem W4Lem13_5Concl.of_hatU43
    (h : ∃ (S : Type) (_ : Group S), LieModel S .PSU 4 3 1 ∧ IsHat ↥L S ∧
      Nat.card W = 2 ^ 12) :
    W4Lem13_5Concl W Y L t :=
  Or.inr (Or.inr (Or.inr (Or.inl h)))

theorem W4Lem13_5Concl.of_alt (h : ∃ n : ℕ, IsAlt ↥L n ∧ AlternatingNatural L ⊤ ⊥ n) :
    W4Lem13_5Concl W Y L t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))

theorem W4Lem13_5Concl.of_alt_seven (h : IsAlt ↥L 7 ∧ Nat.card W = 2 ^ 4) :
    W4Lem13_5Concl W Y L t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))

theorem W4Lem13_5Concl.of_m22 (h : IsSpor ↥L .M22 ∧ Nat.card W = 2 ^ 10) :
    W4Lem13_5Concl W Y L t :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))

end Intro

@[expose] def W4Lem13_5AtChev2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W), ∀ t : MulAut W,
      Is135Context Y L → t ∈ Y → orderOf t = 2 →
      E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 →
      CFSG.GH74.GLS.InChev2 (↥L ⧸ Subgroup.center ↥L) →
      W4Lem13_5Concl W Y L t

@[expose] def W4Lem13_5Chev2 : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L : Subgroup (MulAut W), ∀ t : MulAut W,
      Is135Context Y L → t ∈ Y → orderOf t = 2 →
      E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3 →
      CFSG.GH74.GLS.InChev2 (↥L ⧸ Subgroup.center ↥L) →
      (Subgroup.center ↥L ≠ ⊥ → ¬ IsAlt (↥L ⧸ Subgroup.center ↥L) 6) →
      W4Lem13_5Concl W Y L t

end CFSG.LocalAnalysis.WeakClosure81
