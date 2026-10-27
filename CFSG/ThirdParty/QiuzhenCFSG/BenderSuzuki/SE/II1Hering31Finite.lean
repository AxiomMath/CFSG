module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Lemma98
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Permutation
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.PStabilityReduction
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.V.ComplementTransfer
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.theorem
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Ring.MinimalAxioms
import Mathlib.Algebra.CharP.CharAndCard

namespace CFSG
end CFSG
open CFSG

/-!
# The finite `F₈` obstruction in Hering's theorem

This module verifies that one explicit transvection of the additive group of
`F₈` cannot preserve the square maps in Higman's types A, B, or C through an
additive lift.  It also rules out type D over `F₈`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII

private structure HeringF8 where
  c0 : Bool
  c1 : Bool
  c2 : Bool
deriving DecidableEq

private instance : Fintype HeringF8 where
  elems := {
    ⟨false, false, false⟩, ⟨true, false, false⟩,
    ⟨false, true, false⟩, ⟨true, true, false⟩,
    ⟨false, false, true⟩, ⟨true, false, true⟩,
    ⟨false, true, true⟩, ⟨true, true, true⟩ }
  complete := by
    rintro ⟨a, b, c⟩
    fin_cases a <;> fin_cases b <;> fin_cases c <;> simp

private instance heringF8DecidableForall (p : HeringF8 → Prop)
    [DecidablePred p] : Decidable (∀ x, p x) :=
  decidable_of_iff
    (p ⟨false, false, false⟩ ∧ p ⟨true, false, false⟩ ∧
      p ⟨false, true, false⟩ ∧ p ⟨true, true, false⟩ ∧
      p ⟨false, false, true⟩ ∧ p ⟨true, false, true⟩ ∧
      p ⟨false, true, true⟩ ∧ p ⟨true, true, true⟩) (by
        constructor
        · rintro ⟨h000, h100, h010, h110, h001, h101, h011, h111⟩
          rintro ⟨a, b, c⟩
          fin_cases a <;> fin_cases b <;> fin_cases c <;> assumption
        · intro h
          exact ⟨h _, h _, h _, h _, h _, h _, h _, h _⟩)

private instance : Zero HeringF8 :=
  ⟨⟨false, false, false⟩⟩

private instance : One HeringF8 :=
  ⟨⟨true, false, false⟩⟩

private instance : Add HeringF8 :=
  ⟨fun a b => ⟨a.c0 ^^ b.c0, a.c1 ^^ b.c1, a.c2 ^^ b.c2⟩⟩

private instance : Neg HeringF8 :=
  ⟨fun a => a⟩

private instance : Mul HeringF8 :=
  ⟨fun a b =>
    ⟨(a.c0 && b.c0) ^^ (a.c1 && b.c2) ^^ (a.c2 && b.c1),
      (a.c0 && b.c1) ^^ (a.c1 && b.c0) ^^ (a.c1 && b.c2) ^^
        (a.c2 && b.c1) ^^ (a.c2 && b.c2),
      (a.c0 && b.c2) ^^ (a.c1 && b.c1) ^^ (a.c2 && b.c0) ^^
        (a.c2 && b.c2)⟩⟩

private instance : CommRing HeringF8 :=
  CommRing.ofMinimalAxioms
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)
    (by decide)

private instance : Nontrivial HeringF8 :=
  ⟨⟨0, 1, by decide⟩⟩

private instance : NoZeroDivisors HeringF8 :=
  ⟨by decide⟩

private instance : IsDomain HeringF8 :=
  NoZeroDivisors.to_isDomain HeringF8

private instance : Field HeringF8 :=
  Fintype.fieldOfDomain HeringF8

example : Fintype.card HeringF8 = 8 := by decide

private instance : CharP HeringF8 2 :=
  charP_of_card_eq_prime_pow
    (show Fintype.card HeringF8 = 2 ^ 3 by decide)

private instance : Algebra (ZMod 2) HeringF8 :=
  ZMod.algebra HeringF8 2

private theorem heringF8_finrank : Module.finrank (ZMod 2) HeringF8 = 3 := by
  letI : Module.Finite (ZMod 2) HeringF8 := Module.Finite.of_finite
  have hcard : Nat.card HeringF8 =
      2 ^ Module.finrank (ZMod 2) HeringF8 := by
    simpa [ZMod.card] using
      (Module.natCard_eq_pow_finrank (K := ZMod 2) (V := HeringF8))
  have hpow : 2 ^ Module.finrank (ZMod 2) HeringF8 = 2 ^ 3 := by
    rw [← hcard]
    have hcard' : Nat.card HeringF8 = 8 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  exact Nat.pow_right_injective (by omega) hpow

private theorem heringF8_ringEquiv_eq_frobenius
    (theta : HeringF8 ≃+* HeringF8) :
    ∃ i : Fin 3, ∀ x : HeringF8, theta x = x ^ (2 ^ (i : ℕ)) := by
  let thetaAlg : HeringF8 ≃ₐ[ZMod 2] HeringF8 :=
    { theta with
      commutes' := by
        intro c
        fin_cases c
        · change theta 0 = 0
          exact theta.map_zero
        · change theta 1 = 1
          exact theta.map_one }
  have hsurj : Function.Surjective
      (fun i : Fin 3 =>
        FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) HeringF8 ^ (i : ℕ)) := by
    have hbij :=
      FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow
        (ZMod 2) HeringF8
    rw [heringF8_finrank] at hbij
    exact hbij.2
  obtain ⟨i, hi⟩ := hsurj thetaAlg
  refine ⟨i, ?_⟩
  intro x
  have hx := DFunLike.congr_fun hi x
  simpa [thetaAlg, AlgEquiv.coe_pow,
    FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] using hx.symm

private def heringF8Transvection : HeringF8 ≃+ HeringF8 where
  toFun a := ⟨a.c2, a.c1, a.c0⟩
  invFun a := ⟨a.c2, a.c1, a.c0⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private def heringF8Theta (i : Fin 3) (a : HeringF8) : HeringF8 :=
  a ^ (2 ^ (i : ℕ))

private def heringF8e0 : HeringF8 := ⟨true, false, false⟩
private def heringF8e1 : HeringF8 := ⟨false, true, false⟩
private def heringF8e2 : HeringF8 := ⟨false, false, true⟩

private def heringF8PairBasis (j : Fin 6) : HeringF8 × HeringF8 :=
  ![(heringF8e0, 0), (heringF8e1, 0), (heringF8e2, 0),
    (0, heringF8e0), (0, heringF8e1), (0, heringF8e2)] j

private def heringF8QuadA (i : Fin 3) (a : HeringF8) : HeringF8 :=
  a * heringF8Theta i a

private def heringF8QuadB
    (i : Fin 3) (epsilon : HeringF8)
    (ab : HeringF8 × HeringF8) : HeringF8 :=
  ab.1 * heringF8Theta i ab.1 +
    epsilon * ab.1 * heringF8Theta i ab.2 +
    ab.2 * heringF8Theta i ab.2

private def heringF8QuadC
    (i : Fin 3) (epsilon : HeringF8)
    (ab : HeringF8 × HeringF8) : HeringF8 :=
  ab.1 * heringF8Theta i ab.1 +
    epsilon * ab.1 ^ 4 * heringF8Theta i (ab.2 ^ 2) +
    ab.2 ^ 2

private abbrev HeringF8TypeAParam :=
  {i : Fin 3 // i ≠ 0}

private abbrev HeringF8TypeBParam :=
  {p : Fin 3 × HeringF8 //
    p.2 ≠ 0 ∧
      ∀ a b : HeringF8, a ≠ 0 → b ≠ 0 →
        heringF8QuadB p.1 p.2 (a, b) ≠ 0}

private abbrev HeringF8TypeCParam :=
  {p : Fin 3 × HeringF8 //
    p.2 ≠ 0 ∧
      (∀ x : HeringF8,
        heringF8Theta p.1 (heringF8Theta p.1 (x ^ 2)) = x) ∧
      ∀ rho : HeringF8,
        p.2 ≠ rho⁻¹ + heringF8Theta p.1 (rho ^ 2) * rho}

private def heringPartialSum
    {A : Type*} [AddCommMonoid A] {n : ℕ}
    (y : Fin n → A) (mask : Fin (2 ^ n)) : A :=
  ∑ j, if mask.val.testBit j.val then y j else 0

private theorem heringPartialSum_map
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (L : A ≃+ B) {n : ℕ} (y : Fin n → A) (mask : Fin (2 ^ n)) :
    L (heringPartialSum y mask) =
      heringPartialSum (fun j => L (y j)) mask := by
  rw [heringPartialSum, heringPartialSum, map_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  by_cases hbit : mask.val.testBit j.val = true
  · simp [hbit]
  · simp [hbit]

private theorem heringPartialSum_eq_map
    {A B : Type*} [AddCommMonoid A] [AddCommMonoid B]
    (L : A ≃+ B) {n : ℕ} (x : Fin n → A) (y : Fin n → B)
    (hy : ∀ j, y j = L (x j)) (mask : Fin (2 ^ n)) :
    heringPartialSum y mask = L (heringPartialSum x mask) := by
  rw [heringPartialSum_map]
  congr 1
  funext j
  exact hy j

private theorem heringPartialSum_two
    {A : Type*} [AddCommMonoid A]
    (y : Fin 2 → A) (mask : Fin 4) :
    heringPartialSum y mask =
      (if mask.val.testBit 0 then y 0 else 0) +
      (if mask.val.testBit 1 then y 1 else 0) := by
  simp [heringPartialSum, Fin.sum_univ_two]

private theorem heringPartialSum_three
    {A : Type*} [AddCommMonoid A]
    (y : Fin 3 → A) (mask : Fin 8) :
    heringPartialSum y mask =
      (if mask.val.testBit 0 then y 0 else 0) +
      (if mask.val.testBit 1 then y 1 else 0) +
      (if mask.val.testBit 2 then y 2 else 0) := by
  simp [heringPartialSum, Fin.sum_univ_three]

private theorem heringPartialSum_four
    {A : Type*} [AddCommMonoid A]
    (y : Fin 4 → A) (mask : Fin 16) :
    heringPartialSum y mask =
      (if mask.val.testBit 0 then y 0 else 0) +
      (if mask.val.testBit 1 then y 1 else 0) +
      (if mask.val.testBit 2 then y 2 else 0) +
      (if mask.val.testBit 3 then y 3 else 0) := by
  simp [heringPartialSum, Fin.sum_univ_four]

private def heringPreviousBasis
    {V : Type*} {m : ℕ} (basis : Fin m → V)
    (j : Fin m) (k : Fin j.val) : V :=
  basis ⟨k.val, k.isLt.trans j.isLt⟩

private abbrev HeringCompatible
    {V Z : Type*} [AddCommMonoid V] {m : ℕ}
    (basis : Fin m → V) (q : V → Z) (T : Z → Z)
    (j : Fin m) (y : Fin j.val → V) (z : V) : Prop :=
  ∀ mask : Fin (2 ^ j.val),
    q (heringPartialSum y mask + z) =
      T (q (heringPartialSum (heringPreviousBasis basis j) mask + basis j))

private abbrev HeringNext
    {V Z : Type*} [AddCommMonoid V] {m : ℕ}
    (basis : Fin m → V) (q : V → Z) (T : Z → Z)
    (j : Fin m) (y : Fin j.val → V) :=
  {z : V // HeringCompatible basis q T j y z}

private def heringNextOfAddEquiv
    {V Z : Type*} [AddCommMonoid V] {m : ℕ}
    (basis : Fin m → V) (q : V → Z) (T : Z → Z)
    (L : V ≃+ V) (hL : ∀ v, q (L v) = T (q v))
    (j : Fin m) (y : Fin j.val → V)
    (hy : ∀ k, y k = L (heringPreviousBasis basis j k)) :
    HeringNext basis q T j y := by
  refine ⟨L (basis j), ?_⟩
  intro mask
  rw [heringPartialSum_eq_map L (heringPreviousBasis basis j) y hy]
  rw [← L.map_add]
  exact hL _

private def heringF8Basis (j : Fin 3) : HeringF8 :=
  ![heringF8e0, heringF8e1, heringF8e2] j

private abbrev HeringF8NextA
    (p : HeringF8TypeAParam) (j : Fin 3)
    (y : Fin j.val → HeringF8) :=
  HeringNext heringF8Basis (heringF8QuadA p) heringF8Transvection j y

private abbrev HeringF8NextB
    (p : HeringF8TypeBParam) (j : Fin 6)
    (y : Fin j.val → HeringF8 × HeringF8) :=
  HeringNext heringF8PairBasis (heringF8QuadB p.1.1 p.1.2)
    heringF8Transvection j y

private abbrev HeringF8NextC
    (p : HeringF8TypeCParam) (j : Fin 6)
    (y : Fin j.val → HeringF8 × HeringF8) :=
  HeringNext heringF8PairBasis (heringF8QuadC p.1.1 p.1.2)
    heringF8Transvection j y

private theorem heringF8_typeA_partial_obstruction_raw :
    ∀ (i : Fin 3), i ≠ 0 →
      ∀ y0 : HeringF8,
        HeringCompatible heringF8Basis (heringF8QuadA i)
          heringF8Transvection 0 ![] y0 →
      ∀ y1 : HeringF8,
        HeringCompatible heringF8Basis (heringF8QuadA i)
          heringF8Transvection 1 ![y0] y1 → False := by
  intro i
  fin_cases i <;> decide

private theorem heringF8_typeA_partial_obstruction
    (p : HeringF8TypeAParam)
    (y0 : HeringF8NextA p 0 ![])
    (y1 : HeringF8NextA p 1 ![(y0 : HeringF8)]) : False :=
  heringF8_typeA_partial_obstruction_raw p p.property
    y0 y0.property y1 y1.property

private def heringF8Elements : List HeringF8 :=
  [⟨false, false, false⟩, ⟨true, false, false⟩,
   ⟨false, true, false⟩, ⟨true, true, false⟩,
   ⟨false, false, true⟩, ⟨true, false, true⟩,
   ⟨false, true, true⟩, ⟨true, true, true⟩]

private theorem heringF8_mem_elements (x : HeringF8) :
    x ∈ heringF8Elements := by
  rcases x with ⟨a, b, c⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    simp [heringF8Elements]

private def heringF8PairElements : List (HeringF8 × HeringF8) :=
  heringF8Elements.flatMap fun a =>
    heringF8Elements.map fun b => (a, b)

private theorem heringF8_mem_pairElements (x : HeringF8 × HeringF8) :
    x ∈ heringF8PairElements := by
  rcases x with ⟨a, b⟩
  simp only [heringF8PairElements, List.mem_flatMap, List.mem_map]
  exact ⟨a, heringF8_mem_elements a, b, heringF8_mem_elements b, rfl⟩

private def heringF8AddRaw (a b : HeringF8) : HeringF8 :=
  ⟨a.c0 ^^ b.c0, a.c1 ^^ b.c1, a.c2 ^^ b.c2⟩

private def heringF8MulRaw (a b : HeringF8) : HeringF8 :=
  ⟨(a.c0 && b.c0) ^^ (a.c1 && b.c2) ^^ (a.c2 && b.c1),
    (a.c0 && b.c1) ^^ (a.c1 && b.c0) ^^ (a.c1 && b.c2) ^^
      (a.c2 && b.c1) ^^ (a.c2 && b.c2),
    (a.c0 && b.c2) ^^ (a.c1 && b.c1) ^^ (a.c2 && b.c0) ^^ (a.c2 && b.c2)⟩

private theorem heringF8_add_eq_raw (a b : HeringF8) :
    a + b = heringF8AddRaw a b := rfl

private theorem heringF8_mul_eq_raw (a b : HeringF8) :
    a * b = heringF8MulRaw a b := rfl

private def heringF8PowRaw (a : HeringF8) : ℕ → HeringF8
  | 0 => heringF8e0
  | n + 1 => heringF8MulRaw (heringF8PowRaw a n) a

private def heringF8ThetaRaw (i : Fin 3) (a : HeringF8) : HeringF8 :=
  heringF8PowRaw a (2 ^ (i : ℕ))

private def heringF8QuadBRaw
    (i : Fin 3) (epsilon : HeringF8)
    (ab : HeringF8 × HeringF8) : HeringF8 :=
  heringF8AddRaw
    (heringF8AddRaw
      (heringF8MulRaw ab.1 (heringF8ThetaRaw i ab.1))
      (heringF8MulRaw
        (heringF8MulRaw epsilon ab.1) (heringF8ThetaRaw i ab.2)))
    (heringF8MulRaw ab.2 (heringF8ThetaRaw i ab.2))

private theorem heringF8_pow_eq_raw (a : HeringF8) (n : ℕ) :
    a ^ n = heringF8PowRaw a n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ih]
    rfl

private theorem heringF8Theta_eq_raw (i : Fin 3) (a : HeringF8) :
    heringF8Theta i a = heringF8ThetaRaw i a := by
  simp [heringF8Theta, heringF8ThetaRaw, heringF8_pow_eq_raw]

private theorem heringF8QuadB_eq_raw
    (i : Fin 3) (epsilon : HeringF8)
    (ab : HeringF8 × HeringF8) :
    heringF8QuadB i epsilon ab = heringF8QuadBRaw i epsilon ab := by
  simp [heringF8QuadB, heringF8QuadBRaw, heringF8Theta_eq_raw,
    heringF8_add_eq_raw, heringF8_mul_eq_raw]

private abbrev HeringCompatibleRaw
    {V Z : Type*} [AddCommMonoid V] {m : ℕ}
    (basis : Fin m → V) (q : V → Z) (T : Z → Z)
    (j : Fin m) (y : Fin j.val → V) (z : V) : Prop :=
  ∀ mask : Fin (2 ^ j.val),
    q (heringPartialSum y mask + z) =
      T (q (heringPartialSum (heringPreviousBasis basis j) mask + basis j))

private theorem heringCompatibleRaw_of_eq
    {V Z : Type*} [AddCommMonoid V] {m : ℕ}
    (basis : Fin m → V) (q q' : V → Z) (T : Z → Z)
    (j : Fin m) (y : Fin j.val → V) (z : V)
    (hqq' : ∀ x, q x = q' x)
    (h : HeringCompatible basis q T j y z) :
    HeringCompatibleRaw basis q' T j y z := by
  intro mask
  simpa [HeringCompatible, HeringCompatibleRaw, hqq'] using h mask

private theorem heringF8CompatibleB_raw
    (i : Fin 3) (epsilon : HeringF8) (j : Fin 6)
    (y : Fin j.val → HeringF8 × HeringF8)
    (z : HeringF8 × HeringF8)
    (h : HeringCompatible heringF8PairBasis (heringF8QuadB i epsilon)
      heringF8Transvection j y z) :
    HeringCompatibleRaw heringF8PairBasis (heringF8QuadBRaw i epsilon)
      heringF8Transvection j y z :=
  heringCompatibleRaw_of_eq heringF8PairBasis
    (heringF8QuadB i epsilon) (heringF8QuadBRaw i epsilon)
    heringF8Transvection j y z (heringF8QuadB_eq_raw i epsilon) h

private def heringF8PairZeroRaw : HeringF8 × HeringF8 :=
  (⟨false, false, false⟩, ⟨false, false, false⟩)

@[simp] private theorem heringF8RawZero_eq_zero :
    (⟨false, false, false⟩ : HeringF8) = 0 := rfl

@[simp] private theorem heringF8PairZeroRaw_eq_zero :
    heringF8PairZeroRaw = 0 := rfl

@[simp] private theorem heringF8Pair_tuple_zero_eq_zero :
    ((0, 0) : HeringF8 × HeringF8) = 0 := rfl

private def heringF8PairAddRaw
    (a b : HeringF8 × HeringF8) : HeringF8 × HeringF8 :=
  (heringF8AddRaw a.1 b.1, heringF8AddRaw a.2 b.2)

private theorem heringF8Pair_add_eq_raw
    (a b : HeringF8 × HeringF8) :
    a + b = heringF8PairAddRaw a b := rfl

private theorem heringF8PairAddRaw_eq_add
    (a b : HeringF8 × HeringF8) :
    heringF8PairAddRaw a b = a + b := rfl

private def heringF8TransvectionRaw (a : HeringF8) : HeringF8 :=
  ⟨a.c2, a.c1, a.c0⟩

private theorem heringF8Transvection_eq_raw (a : HeringF8) :
    heringF8Transvection a = heringF8TransvectionRaw a := rfl

private theorem heringF8TransvectionRaw_eq (a : HeringF8) :
    heringF8TransvectionRaw a = heringF8Transvection a := rfl

private def heringF8EqRaw (a b : HeringF8) : Bool :=
  (a.c0 == b.c0) && (a.c1 == b.c1) && (a.c2 == b.c2)

@[simp] private theorem heringF8EqRaw_eq_true_iff (a b : HeringF8) :
    heringF8EqRaw a b = true ↔ a = b := by
  rcases a with ⟨a0, a1, a2⟩
  rcases b with ⟨b0, b1, b2⟩
  fin_cases a0 <;> fin_cases a1 <;> fin_cases a2 <;>
    fin_cases b0 <;> fin_cases b1 <;> fin_cases b2 <;> decide

private def heringF8PairSubsetSums :
    List (HeringF8 × HeringF8) → List (HeringF8 × HeringF8)
  | [] => [heringF8PairZeroRaw]
  | x :: xs =>
      (heringF8PairSubsetSums xs).flatMap fun y =>
        [y, heringF8PairAddRaw x y]

private def heringF8PairBasisList : List (HeringF8 × HeringF8) :=
  [(heringF8e0, 0), (heringF8e1, 0), (heringF8e2, 0),
   (0, heringF8e0), (0, heringF8e1), (0, heringF8e2)]

private def heringF8PairCompatibleListRaw
    (q : (HeringF8 × HeringF8) → HeringF8)
    (ys : List (HeringF8 × HeringF8))
    (z : HeringF8 × HeringF8) : Bool :=
  match heringF8PairBasisList[ys.length]? with
  | none => false
  | some b =>
      (List.zip (heringF8PairSubsetSums ys)
        (heringF8PairSubsetSums (heringF8PairBasisList.take ys.length))).all
        fun sums => heringF8EqRaw
          (q (heringF8PairAddRaw sums.1 z))
          (heringF8TransvectionRaw (q (heringF8PairAddRaw sums.2 b)))

private theorem heringF8PairCompatibleListRaw_zero
    (q : (HeringF8 × HeringF8) → HeringF8)
    (z : HeringF8 × HeringF8)
    (h : HeringCompatibleRaw heringF8PairBasis q heringF8Transvection
      0 ![] z) :
    heringF8PairCompatibleListRaw q [] z = true := by
  have h0 := h (0 : Fin 1)
  simpa [heringF8PairCompatibleListRaw, heringF8PairSubsetSums,
    heringF8PairBasisList, heringF8PairZeroRaw, heringF8PairAddRaw_eq_add,
    heringF8TransvectionRaw_eq, heringPartialSum, heringPreviousBasis,
    heringF8PairBasis, Fin.sum_univ_succ] using h0

private theorem heringF8PairCompatibleListRaw_one
    (q : (HeringF8 × HeringF8) → HeringF8)
    (y0 z : HeringF8 × HeringF8)
    (h : HeringCompatibleRaw heringF8PairBasis q heringF8Transvection
      1 ![y0] z) :
    heringF8PairCompatibleListRaw q [y0] z = true := by
  have h0 := h (0 : Fin 2)
  have h1 := h (1 : Fin 2)
  simpa [heringF8PairCompatibleListRaw, heringF8PairSubsetSums,
    heringF8PairBasisList, heringF8PairZeroRaw, heringF8PairAddRaw_eq_add,
    heringF8TransvectionRaw_eq, heringPartialSum, heringPreviousBasis,
    heringF8PairBasis, Fin.sum_univ_succ] using And.intro h0 h1

private theorem heringF8PairCompatibleListRaw_two
    (q : (HeringF8 × HeringF8) → HeringF8)
    (y0 y1 z : HeringF8 × HeringF8)
    (h : HeringCompatibleRaw heringF8PairBasis q heringF8Transvection
      2 ![y0, y1] z) :
    heringF8PairCompatibleListRaw q [y0, y1] z = true := by
  have h0 := h (0 : Fin 4)
  have h1 := h (1 : Fin 4)
  have h2 := h (2 : Fin 4)
  have h3 := h (3 : Fin 4)
  simpa [heringF8PairCompatibleListRaw, heringF8PairSubsetSums,
    heringF8PairBasisList, heringF8PairZeroRaw, heringF8PairAddRaw_eq_add,
    heringF8TransvectionRaw_eq, heringPartialSum_two, heringPreviousBasis,
    heringF8PairBasis, Nat.testBit_succ] using
      And.intro h0 (And.intro h1 (And.intro h2 h3))

private theorem heringF8PairCompatibleListRaw_three
    (q : (HeringF8 × HeringF8) → HeringF8)
    (y0 y1 y2 z : HeringF8 × HeringF8)
    (h : HeringCompatibleRaw heringF8PairBasis q heringF8Transvection
      3 ![y0, y1, y2] z) :
    heringF8PairCompatibleListRaw q [y0, y1, y2] z = true := by
  have h0 := h (0 : Fin 8)
  have h1 := h (1 : Fin 8)
  have h2 := h (2 : Fin 8)
  have h3 := h (3 : Fin 8)
  have h4 := h (4 : Fin 8)
  have h5 := h (5 : Fin 8)
  have h6 := h (6 : Fin 8)
  have h7 := h (7 : Fin 8)
  simpa [heringF8PairCompatibleListRaw, heringF8PairSubsetSums,
    heringF8PairBasisList, heringF8PairZeroRaw, heringF8PairAddRaw_eq_add,
    heringF8TransvectionRaw_eq, heringPartialSum_three, heringPreviousBasis,
    heringF8PairBasis, Nat.testBit_succ, add_assoc] using
      And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3
        (And.intro h4 (And.intro h5 (And.intro h6 h7))))))

private theorem heringF8PairCompatibleListRaw_four
    (q : (HeringF8 × HeringF8) → HeringF8)
    (y0 y1 y2 y3 z : HeringF8 × HeringF8)
    (h : HeringCompatibleRaw heringF8PairBasis q heringF8Transvection
      4 ![y0, y1, y2, y3] z) :
    heringF8PairCompatibleListRaw q [y0, y1, y2, y3] z = true := by
  have h0 := h (0 : Fin 16)
  have h1 := h (1 : Fin 16)
  have h2 := h (2 : Fin 16)
  have h3 := h (3 : Fin 16)
  have h4 := h (4 : Fin 16)
  have h5 := h (5 : Fin 16)
  have h6 := h (6 : Fin 16)
  have h7 := h (7 : Fin 16)
  have h8 := h (8 : Fin 16)
  have h9 := h (9 : Fin 16)
  have h10 := h (10 : Fin 16)
  have h11 := h (11 : Fin 16)
  have h12 := h (12 : Fin 16)
  have h13 := h (13 : Fin 16)
  have h14 := h (14 : Fin 16)
  have h15 := h (15 : Fin 16)
  simpa [heringF8PairCompatibleListRaw, heringF8PairSubsetSums,
    heringF8PairBasisList, heringF8PairZeroRaw, heringF8PairAddRaw_eq_add,
    heringF8TransvectionRaw_eq, heringPartialSum_four, heringPreviousBasis,
    heringF8PairBasis, Nat.testBit_succ, add_assoc] using
      And.intro h0 (And.intro h1 (And.intro h2 (And.intro h3
        (And.intro h4 (And.intro h5 (And.intro h6 (And.intro h7
          (And.intro h8 (And.intro h9 (And.intro h10 (And.intro h11
            (And.intro h12 (And.intro h13 (And.intro h14 h15))))))))))))))

private def heringF8PairStates
    (q : (HeringF8 × HeringF8) → HeringF8) :
    ℕ → List (List (HeringF8 × HeringF8))
  | 0 => [[]]
  | n + 1 =>
      (heringF8PairStates q n).flatMap fun ys =>
        (heringF8PairElements.filter (heringF8PairCompatibleListRaw q ys)).map
          fun z => ys ++ [z]

private theorem heringF8PairStates_snoc_mem
    (q : (HeringF8 × HeringF8) → HeringF8)
    {n : ℕ} (ys : List (HeringF8 × HeringF8))
    (hy : ys ∈ heringF8PairStates q n)
    (z : HeringF8 × HeringF8)
    (hz : heringF8PairCompatibleListRaw q ys z = true) :
    ys ++ [z] ∈ heringF8PairStates q (n + 1) := by
  simp only [heringF8PairStates, List.mem_flatMap, List.mem_map,
    List.mem_filter]
  exact ⟨ys, hy, z, ⟨heringF8_mem_pairElements z, hz⟩, rfl⟩

private theorem heringF8_typeB_states_nil_zero
    (epsilon : HeringF8) :
    epsilon ≠ 0 →
    (∀ a b : HeringF8, a ≠ 0 → b ≠ 0 →
      heringF8QuadBRaw 0 epsilon (a, b) ≠ 0) →
    heringF8PairStates (heringF8QuadBRaw 0 epsilon) 5 = [] := by
  rcases epsilon with ⟨e0, e1, e2⟩
  fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;>
    decide

private theorem heringF8_typeB_states_nil_one
    (epsilon : HeringF8) :
    epsilon ≠ 0 →
    (∀ a b : HeringF8, a ≠ 0 → b ≠ 0 →
      heringF8QuadBRaw 1 epsilon (a, b) ≠ 0) →
    heringF8PairStates (heringF8QuadBRaw 1 epsilon) 5 = [] := by
  rcases epsilon with ⟨e0, e1, e2⟩
  fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;>
    decide

private theorem heringF8_typeB_states_nil_two
    (epsilon : HeringF8) :
    epsilon ≠ 0 →
    (∀ a b : HeringF8, a ≠ 0 → b ≠ 0 →
      heringF8QuadBRaw 2 epsilon (a, b) ≠ 0) →
    heringF8PairStates (heringF8QuadBRaw 2 epsilon) 5 = [] := by
  rcases epsilon with ⟨e0, e1, e2⟩
  fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;>
    decide

private theorem heringF8_typeB_states_nil
    (i : Fin 3) (epsilon : HeringF8) :
    epsilon ≠ 0 →
    (∀ a b : HeringF8, a ≠ 0 → b ≠ 0 →
      heringF8QuadBRaw i epsilon (a, b) ≠ 0) →
    heringF8PairStates (heringF8QuadBRaw i epsilon) 5 = [] := by
  fin_cases i
  · exact heringF8_typeB_states_nil_zero epsilon
  · exact heringF8_typeB_states_nil_one epsilon
  · exact heringF8_typeB_states_nil_two epsilon

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem heringF8_typeB_partial_obstruction_raw :
    ∀ (i : Fin 3) (epsilon : HeringF8),
      epsilon ≠ 0 →
      (∀ a b : HeringF8, a ≠ 0 → b ≠ 0 →
        heringF8QuadB i epsilon (a, b) ≠ 0) →
      ∀ y00 y01 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadB i epsilon)
          heringF8Transvection 0 ![] (y00, y01) →
      ∀ y10 y11 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadB i epsilon)
          heringF8Transvection 1 ![(y00, y01)] (y10, y11) →
      ∀ y20 y21 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadB i epsilon)
          heringF8Transvection 2 ![(y00, y01), (y10, y11)] (y20, y21) →
      ∀ y30 y31 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadB i epsilon)
          heringF8Transvection 3
            ![(y00, y01), (y10, y11), (y20, y21)] (y30, y31) →
      ∀ y40 y41 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadB i epsilon)
          heringF8Transvection 4
            ![(y00, y01), (y10, y11), (y20, y21), (y30, y31)]
            (y40, y41) → False := by
  intro i epsilon hepsilon hanisotropic y00 y01 h0 y10 y11 h1 y20 y21 h2
    y30 y31 h3 y40 y41 h4
  have hanisotropicRaw : ∀ a b : HeringF8, a ≠ 0 → b ≠ 0 →
      heringF8QuadBRaw i epsilon (a, b) ≠ 0 := by
    intro a b ha hb hzero
    apply hanisotropic a b ha hb
    rw [heringF8QuadB_eq_raw]
    exact hzero
  have h0' := heringF8CompatibleB_raw i epsilon 0 ![] (y00, y01) h0
  have h1' := heringF8CompatibleB_raw i epsilon 1
    ![(y00, y01)] (y10, y11) h1
  have h2' := heringF8CompatibleB_raw i epsilon 2
    ![(y00, y01), (y10, y11)] (y20, y21) h2
  have h3' := heringF8CompatibleB_raw i epsilon 3
    ![(y00, y01), (y10, y11), (y20, y21)] (y30, y31) h3
  have h4' := heringF8CompatibleB_raw i epsilon 4
    ![(y00, y01), (y10, y11), (y20, y21), (y30, y31)] (y40, y41) h4
  have h0b := heringF8PairCompatibleListRaw_zero
    (heringF8QuadBRaw i epsilon) (y00, y01) h0'
  have h1b := heringF8PairCompatibleListRaw_one
    (heringF8QuadBRaw i epsilon) (y00, y01) (y10, y11) h1'
  have h2b := heringF8PairCompatibleListRaw_two
    (heringF8QuadBRaw i epsilon) (y00, y01) (y10, y11) (y20, y21) h2'
  have h3b := heringF8PairCompatibleListRaw_three
    (heringF8QuadBRaw i epsilon) (y00, y01) (y10, y11) (y20, y21)
      (y30, y31) h3'
  have h4b := heringF8PairCompatibleListRaw_four
    (heringF8QuadBRaw i epsilon) (y00, y01) (y10, y11) (y20, y21)
      (y30, y31) (y40, y41) h4'
  have hs0 : [] ∈ heringF8PairStates
      (heringF8QuadBRaw i epsilon) 0 := by
    simp [heringF8PairStates]
  have hs1 : [(y00, y01)] ∈ heringF8PairStates
      (heringF8QuadBRaw i epsilon) 1 := by
    simpa using heringF8PairStates_snoc_mem
      (heringF8QuadBRaw i epsilon) (n := 0) [] hs0
      (y00, y01) h0b
  have hs2 : [(y00, y01), (y10, y11)] ∈ heringF8PairStates
      (heringF8QuadBRaw i epsilon) 2 := by
    simpa using heringF8PairStates_snoc_mem
      (heringF8QuadBRaw i epsilon) (n := 1) [(y00, y01)] hs1
      (y10, y11) h1b
  have hs3 : [(y00, y01), (y10, y11), (y20, y21)] ∈ heringF8PairStates
      (heringF8QuadBRaw i epsilon) 3 := by
    simpa using heringF8PairStates_snoc_mem
      (heringF8QuadBRaw i epsilon) (n := 2)
      [(y00, y01), (y10, y11)] hs2 (y20, y21) h2b
  have hs4 : [(y00, y01), (y10, y11), (y20, y21), (y30, y31)] ∈
      heringF8PairStates (heringF8QuadBRaw i epsilon) 4 := by
    simpa using heringF8PairStates_snoc_mem
      (heringF8QuadBRaw i epsilon) (n := 3)
      [(y00, y01), (y10, y11), (y20, y21)] hs3 (y30, y31) h3b
  have hs5 : [(y00, y01), (y10, y11), (y20, y21), (y30, y31),
      (y40, y41)] ∈ heringF8PairStates
      (heringF8QuadBRaw i epsilon) 5 := by
    simpa using heringF8PairStates_snoc_mem
      (heringF8QuadBRaw i epsilon) (n := 4)
      [(y00, y01), (y10, y11), (y20, y21), (y30, y31)] hs4
      (y40, y41) h4b
  rw [heringF8_typeB_states_nil i epsilon hepsilon hanisotropicRaw] at hs5
  simp at hs5

private theorem heringF8_typeB_partial_obstruction
    (p : HeringF8TypeBParam)
    (y0 : HeringF8NextB p 0 ![])
    (y1 : HeringF8NextB p 1 ![(y0 : HeringF8 × HeringF8)])
    (y2 : HeringF8NextB p 2
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8)])
    (y3 : HeringF8NextB p 3
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8)])
    (y4 : HeringF8NextB p 4
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8), (y3 : HeringF8 × HeringF8)]) : False :=
  heringF8_typeB_partial_obstruction_raw p.1.1 p.1.2
    p.property.1 p.property.2
    y0.val.1 y0.val.2 y0.property
    y1.val.1 y1.val.2 y1.property
    y2.val.1 y2.val.2 y2.property
    y3.val.1 y3.val.2 y3.property
    y4.val.1 y4.val.2 y4.property

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
private theorem heringF8_typeC_partial_obstruction_raw :
    ∀ (i : Fin 3) (epsilon : HeringF8),
      epsilon ≠ 0 →
      (∀ x : HeringF8,
        heringF8Theta i (heringF8Theta i (x ^ 2)) = x) →
      (∀ rho : HeringF8,
        epsilon ≠ rho⁻¹ + heringF8Theta i (rho ^ 2) * rho) →
      ∀ y00 y01 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadC i epsilon)
          heringF8Transvection 0 ![] (y00, y01) →
      ∀ y10 y11 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadC i epsilon)
          heringF8Transvection 1 ![(y00, y01)] (y10, y11) →
      ∀ y20 y21 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadC i epsilon)
          heringF8Transvection 2 ![(y00, y01), (y10, y11)] (y20, y21) →
      ∀ y30 y31 : HeringF8,
        HeringCompatible heringF8PairBasis (heringF8QuadC i epsilon)
          heringF8Transvection 3
            ![(y00, y01), (y10, y11), (y20, y21)] (y30, y31) → False := by
  rintro i ⟨e0, e1, e2⟩
  fin_cases i <;>
    fin_cases e0 <;> fin_cases e1 <;> fin_cases e2 <;> decide

private theorem heringF8_typeC_partial_obstruction
    (p : HeringF8TypeCParam)
    (y0 : HeringF8NextC p 0 ![])
    (y1 : HeringF8NextC p 1 ![(y0 : HeringF8 × HeringF8)])
    (y2 : HeringF8NextC p 2
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8)])
    (y3 : HeringF8NextC p 3
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8)]) : False :=
  heringF8_typeC_partial_obstruction_raw p.1.1 p.1.2
    p.property.1 p.property.2.1 p.property.2.2
    y0.val.1 y0.val.2 y0.property
    y1.val.1 y1.val.2 y1.property
    y2.val.1 y2.val.2 y2.property
    y3.val.1 y3.val.2 y3.property

private theorem heringF8_typeA_no_lift
    (i : Fin 3) (hi : i ≠ 0)
    (L : HeringF8 ≃+ HeringF8)
    (hL : ∀ a : HeringF8,
      heringF8QuadA i (L a) =
        heringF8Transvection (heringF8QuadA i a)) : False := by
  let p : HeringF8TypeAParam := ⟨i, hi⟩
  let y0 : HeringF8NextA p 0 ![] :=
    heringNextOfAddEquiv heringF8Basis (heringF8QuadA p)
      heringF8Transvection L hL 0 ![] (fun k => Fin.elim0 k)
  let y1 : HeringF8NextA p 1 ![(y0 : HeringF8)] :=
    heringNextOfAddEquiv heringF8Basis (heringF8QuadA p)
      heringF8Transvection L hL 1 ![(y0 : HeringF8)] (by
        intro k
        fin_cases k
        rfl)
  exact heringF8_typeA_partial_obstruction p y0 y1

private theorem heringF8_typeB_no_lift
    (p : HeringF8TypeBParam)
    (L : (HeringF8 × HeringF8) ≃+ (HeringF8 × HeringF8))
    (hL : ∀ a : HeringF8 × HeringF8,
      heringF8QuadB p.1.1 p.1.2 (L a) =
        heringF8Transvection (heringF8QuadB p.1.1 p.1.2 a)) : False := by
  let y0 : HeringF8NextB p 0 ![] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadB p.1.1 p.1.2) heringF8Transvection L hL
      0 ![] (fun k => Fin.elim0 k)
  let y1 : HeringF8NextB p 1 ![(y0 : HeringF8 × HeringF8)] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadB p.1.1 p.1.2) heringF8Transvection L hL
      1 ![(y0 : HeringF8 × HeringF8)] (by
        intro k
        fin_cases k
        rfl)
  let y2 : HeringF8NextB p 2
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8)] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadB p.1.1 p.1.2) heringF8Transvection L hL
      2 ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8)] (by
        intro k
        fin_cases k <;> rfl)
  let y3 : HeringF8NextB p 3
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8)] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadB p.1.1 p.1.2) heringF8Transvection L hL
      3 ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8)] (by
          intro k
          fin_cases k <;> rfl)
  let y4 : HeringF8NextB p 4
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8), (y3 : HeringF8 × HeringF8)] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadB p.1.1 p.1.2) heringF8Transvection L hL
      4 ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8), (y3 : HeringF8 × HeringF8)] (by
          intro k
          fin_cases k <;> rfl)
  exact heringF8_typeB_partial_obstruction p y0 y1 y2 y3 y4

private theorem heringF8_typeC_no_lift
    (p : HeringF8TypeCParam)
    (L : (HeringF8 × HeringF8) ≃+ (HeringF8 × HeringF8))
    (hL : ∀ a : HeringF8 × HeringF8,
      heringF8QuadC p.1.1 p.1.2 (L a) =
        heringF8Transvection (heringF8QuadC p.1.1 p.1.2 a)) : False := by
  let y0 : HeringF8NextC p 0 ![] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadC p.1.1 p.1.2) heringF8Transvection L hL
      0 ![] (fun k => Fin.elim0 k)
  let y1 : HeringF8NextC p 1 ![(y0 : HeringF8 × HeringF8)] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadC p.1.1 p.1.2) heringF8Transvection L hL
      1 ![(y0 : HeringF8 × HeringF8)] (by
        intro k
        fin_cases k
        rfl)
  let y2 : HeringF8NextC p 2
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8)] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadC p.1.1 p.1.2) heringF8Transvection L hL
      2 ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8)] (by
        intro k
        fin_cases k <;> rfl)
  let y3 : HeringF8NextC p 3
      ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8)] :=
    heringNextOfAddEquiv heringF8PairBasis
      (heringF8QuadC p.1.1 p.1.2) heringF8Transvection L hL
      3 ![(y0 : HeringF8 × HeringF8), (y1 : HeringF8 × HeringF8),
        (y2 : HeringF8 × HeringF8)] (by
          intro k
          fin_cases k <;> rfl)
  exact heringF8_typeC_partial_obstruction p y0 y1 y2 y3

private abbrev HeringBinaryF8 := BinaryGaloisField 3

private noncomputable instance : Fintype HeringBinaryF8 :=
  Fintype.ofFinite HeringBinaryF8

private noncomputable def heringBinaryF8Equiv : HeringBinaryF8 ≃+* HeringF8 :=
  FiniteField.ringEquivOfCardEq (by
    calc
      Fintype.card HeringBinaryF8 = 8 := by
        rw [← Nat.card_eq_fintype_card]
        simpa [HeringBinaryF8, BinaryGaloisField] using
          (GaloisField.card 2 3 (by omega))
      _ = Fintype.card HeringF8 := by decide)

public noncomputable def ii1Hering31F8Transvection :
    BinaryGaloisField 3 ≃+ BinaryGaloisField 3 :=
  heringBinaryF8Equiv.toAddEquiv.trans
    (heringF8Transvection.trans heringBinaryF8Equiv.symm.toAddEquiv)

private noncomputable def heringF8TransportRingAut
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8) : HeringF8 ≃+* HeringF8 :=
  heringBinaryF8Equiv.symm.trans (theta.trans heringBinaryF8Equiv)

private noncomputable def heringF8TransportAddAut
    (L : HeringBinaryF8 ≃+ HeringBinaryF8) : HeringF8 ≃+ HeringF8 :=
  heringBinaryF8Equiv.symm.toAddEquiv.trans
    (L.trans heringBinaryF8Equiv.toAddEquiv)

private noncomputable def heringF8TransportPairAddAut
    (L : (HeringBinaryF8 × HeringBinaryF8) ≃+
      (HeringBinaryF8 × HeringBinaryF8)) :
    (HeringF8 × HeringF8) ≃+ (HeringF8 × HeringF8) :=
  let e := AddEquiv.prodCongr heringBinaryF8Equiv.toAddEquiv
    heringBinaryF8Equiv.toAddEquiv
  e.symm.trans (L.trans e)

private theorem heringF8TransportPairAddAut_apply
    (L : (HeringBinaryF8 × HeringBinaryF8) ≃+
      (HeringBinaryF8 × HeringBinaryF8))
    (a : HeringF8 × HeringF8) :
    heringF8TransportPairAddAut L a =
      (heringBinaryF8Equiv
          (L (heringBinaryF8Equiv.symm a.1,
            heringBinaryF8Equiv.symm a.2)).1,
        heringBinaryF8Equiv
          (L (heringBinaryF8Equiv.symm a.1,
            heringBinaryF8Equiv.symm a.2)).2) := by
  rfl

private def heringBinaryF8QuadA
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8)
    (a : HeringBinaryF8) : HeringBinaryF8 :=
  a * theta a

private def heringBinaryF8QuadB
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8)
    (epsilon : HeringBinaryF8)
    (ab : HeringBinaryF8 × HeringBinaryF8) : HeringBinaryF8 :=
  ab.1 * theta ab.1 + epsilon * ab.1 * theta ab.2 + ab.2 * theta ab.2

private def heringBinaryF8QuadC
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8)
    (epsilon : HeringBinaryF8)
    (ab : HeringBinaryF8 × HeringBinaryF8) : HeringBinaryF8 :=
  ab.1 * theta ab.1 + epsilon * ab.1 ^ 4 * theta (ab.2 ^ 2) + ab.2 ^ 2

private theorem heringBinaryF8_typeA_no_lift
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8)
    (htheta : ∃ x : HeringBinaryF8, theta x ≠ x)
    (L : HeringBinaryF8 ≃+ HeringBinaryF8)
    (hL : ∀ a : HeringBinaryF8,
      heringBinaryF8QuadA theta (L a) =
        ii1Hering31F8Transvection (heringBinaryF8QuadA theta a)) : False := by
  let theta8 : HeringF8 ≃+* HeringF8 := heringF8TransportRingAut theta
  obtain ⟨i, hi⟩ := heringF8_ringEquiv_eq_frobenius theta8
  have hi0 : i ≠ 0 := by
    intro hi0
    subst i
    rcases htheta with ⟨x, hx⟩
    apply hx
    apply heringBinaryF8Equiv.injective
    have h := hi (heringBinaryF8Equiv x)
    simpa [theta8, heringF8TransportRingAut] using h
  let L8 : HeringF8 ≃+ HeringF8 := heringF8TransportAddAut L
  have hL8 : ∀ a : HeringF8,
      heringF8QuadA i (L8 a) =
        heringF8Transvection (heringF8QuadA i a) := by
    intro a
    rw [heringF8QuadA, heringF8QuadA, heringF8Theta, heringF8Theta,
      ← hi (L8 a), ← hi a]
    simpa [L8, theta8, heringF8TransportAddAut,
      heringF8TransportRingAut, heringBinaryF8QuadA,
      ii1Hering31F8Transvection] using
        congrArg heringBinaryF8Equiv (hL (heringBinaryF8Equiv.symm a))
  exact heringF8_typeA_no_lift i hi0 L8 hL8

private theorem heringBinaryF8_typeB_no_lift
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8)
    (epsilon : HeringBinaryF8) (hepsilon : epsilon ≠ 0)
    (hanisotropic : ∀ a b : HeringBinaryF8, a ≠ 0 → b ≠ 0 →
      heringBinaryF8QuadB theta epsilon (a, b) ≠ 0)
    (L : (HeringBinaryF8 × HeringBinaryF8) ≃+
      (HeringBinaryF8 × HeringBinaryF8))
    (hL : ∀ a : HeringBinaryF8 × HeringBinaryF8,
      heringBinaryF8QuadB theta epsilon (L a) =
        ii1Hering31F8Transvection
          (heringBinaryF8QuadB theta epsilon a)) : False := by
  let theta8 : HeringF8 ≃+* HeringF8 := heringF8TransportRingAut theta
  obtain ⟨i, hi⟩ := heringF8_ringEquiv_eq_frobenius theta8
  let epsilon8 : HeringF8 := heringBinaryF8Equiv epsilon
  have hepsilon8 : epsilon8 ≠ 0 := by
    exact (map_ne_zero heringBinaryF8Equiv).2 hepsilon
  have hanisotropic8 : ∀ a b : HeringF8, a ≠ 0 → b ≠ 0 →
      heringF8QuadB i epsilon8 (a, b) ≠ 0 := by
    intro a b ha hb hzero
    have ha' : heringBinaryF8Equiv.symm a ≠ 0 :=
      (map_ne_zero heringBinaryF8Equiv.symm).2 ha
    have hb' : heringBinaryF8Equiv.symm b ≠ 0 :=
      (map_ne_zero heringBinaryF8Equiv.symm).2 hb
    apply hanisotropic (heringBinaryF8Equiv.symm a)
      (heringBinaryF8Equiv.symm b) ha' hb'
    apply heringBinaryF8Equiv.injective
    rw [map_zero]
    rw [← hzero]
    rw [heringF8QuadB, heringF8Theta, heringF8Theta,
      ← hi a, ← hi b]
    simp [epsilon8, theta8, heringF8TransportRingAut,
      heringBinaryF8QuadB]
  let p : HeringF8TypeBParam :=
    ⟨(i, epsilon8), hepsilon8, hanisotropic8⟩
  let L8 : (HeringF8 × HeringF8) ≃+ (HeringF8 × HeringF8) :=
    heringF8TransportPairAddAut L
  have hL8 : ∀ a : HeringF8 × HeringF8,
      heringF8QuadB i epsilon8 (L8 a) =
        heringF8Transvection (heringF8QuadB i epsilon8 a) := by
    intro a
    rw [show L8 a =
      (heringBinaryF8Equiv
          (L (heringBinaryF8Equiv.symm a.1,
            heringBinaryF8Equiv.symm a.2)).1,
        heringBinaryF8Equiv
          (L (heringBinaryF8Equiv.symm a.1,
            heringBinaryF8Equiv.symm a.2)).2) by
      exact heringF8TransportPairAddAut_apply L a]
    rw [heringF8QuadB, heringF8QuadB, heringF8Theta, heringF8Theta,
      heringF8Theta, heringF8Theta,
      ← hi (heringBinaryF8Equiv
        (L (heringBinaryF8Equiv.symm a.1,
          heringBinaryF8Equiv.symm a.2)).1),
      ← hi (heringBinaryF8Equiv
        (L (heringBinaryF8Equiv.symm a.1,
          heringBinaryF8Equiv.symm a.2)).2),
      ← hi a.1, ← hi a.2]
    simpa [L8, theta8, epsilon8, heringF8TransportPairAddAut,
      heringF8TransportRingAut, heringBinaryF8QuadB,
      ii1Hering31F8Transvection] using congrArg heringBinaryF8Equiv
        (hL (heringBinaryF8Equiv.symm a.1,
          heringBinaryF8Equiv.symm a.2))
  exact heringF8_typeB_no_lift p L8 hL8

private theorem heringBinaryF8_typeC_no_lift
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8)
    (epsilon : HeringBinaryF8) (hepsilon : epsilon ≠ 0)
    (hthetaSquare : ∀ x : HeringBinaryF8,
      theta (theta (x ^ 2)) = x)
    (havoid : ∀ rho : HeringBinaryF8,
      epsilon ≠ rho⁻¹ + theta (rho ^ 2) * rho)
    (L : (HeringBinaryF8 × HeringBinaryF8) ≃+
      (HeringBinaryF8 × HeringBinaryF8))
    (hL : ∀ a : HeringBinaryF8 × HeringBinaryF8,
      heringBinaryF8QuadC theta epsilon (L a) =
        ii1Hering31F8Transvection
          (heringBinaryF8QuadC theta epsilon a)) : False := by
  let theta8 : HeringF8 ≃+* HeringF8 := heringF8TransportRingAut theta
  obtain ⟨i, hi⟩ := heringF8_ringEquiv_eq_frobenius theta8
  let epsilon8 : HeringF8 := heringBinaryF8Equiv epsilon
  have hepsilon8 : epsilon8 ≠ 0 := by
    exact (map_ne_zero heringBinaryF8Equiv).2 hepsilon
  have hthetaSquare8 : ∀ x : HeringF8,
      heringF8Theta i (heringF8Theta i (x ^ 2)) = x := by
    intro x
    simp only [heringF8Theta]
    rw [← hi ((x ^ 2) ^ (2 ^ (i : ℕ))), ← hi (x ^ 2)]
    simpa [theta8, heringF8TransportRingAut] using congrArg
      heringBinaryF8Equiv (hthetaSquare (heringBinaryF8Equiv.symm x))
  have havoid8 : ∀ rho : HeringF8,
      epsilon8 ≠ rho⁻¹ + heringF8Theta i (rho ^ 2) * rho := by
    intro rho hEq
    simp only [heringF8Theta] at hEq
    rw [← hi (rho ^ 2)] at hEq
    apply havoid (heringBinaryF8Equiv.symm rho)
    apply heringBinaryF8Equiv.injective
    simpa [epsilon8, theta8, heringF8TransportRingAut] using hEq
  let p : HeringF8TypeCParam :=
    ⟨(i, epsilon8), hepsilon8, hthetaSquare8, havoid8⟩
  let L8 : (HeringF8 × HeringF8) ≃+ (HeringF8 × HeringF8) :=
    heringF8TransportPairAddAut L
  have hL8 : ∀ a : HeringF8 × HeringF8,
      heringF8QuadC i epsilon8 (L8 a) =
        heringF8Transvection (heringF8QuadC i epsilon8 a) := by
    intro a
    rw [show L8 a =
      (heringBinaryF8Equiv
          (L (heringBinaryF8Equiv.symm a.1,
            heringBinaryF8Equiv.symm a.2)).1,
        heringBinaryF8Equiv
          (L (heringBinaryF8Equiv.symm a.1,
            heringBinaryF8Equiv.symm a.2)).2) by
      exact heringF8TransportPairAddAut_apply L a]
    rw [heringF8QuadC, heringF8QuadC, heringF8Theta, heringF8Theta,
      heringF8Theta, heringF8Theta,
      ← hi (heringBinaryF8Equiv
        (L (heringBinaryF8Equiv.symm a.1,
          heringBinaryF8Equiv.symm a.2)).1),
      ← hi (heringBinaryF8Equiv
        (L (heringBinaryF8Equiv.symm a.1,
          heringBinaryF8Equiv.symm a.2)).2 ^ 2),
      ← hi a.1, ← hi (a.2 ^ 2)]
    simpa [L8, theta8, epsilon8, heringF8TransportPairAddAut,
      heringF8TransportRingAut, heringBinaryF8QuadC,
      ii1Hering31F8Transvection] using congrArg heringBinaryF8Equiv
        (hL (heringBinaryF8Equiv.symm a.1,
          heringBinaryF8Equiv.symm a.2))
  exact heringF8_typeC_no_lift p L8 hL8

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
private theorem heringF8_typeD_obstruction :
    ∀ (i : Fin 3),
      (∀ x : HeringF8, (heringF8Theta i)^[5] x = x) →
      (∃ x : HeringF8, heringF8Theta i x ≠ x) → False := by
  intro i
  fin_cases i <;> decide

private theorem heringF8TransportRingAut_iterate
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8)
    (n : ℕ) (x : HeringF8) :
    (heringF8TransportRingAut theta)^[n] x =
      heringBinaryF8Equiv (theta^[n] (heringBinaryF8Equiv.symm x)) := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      simp [heringF8TransportRingAut]

private theorem heringBinaryF8_typeD_false
    (theta : HeringBinaryF8 ≃+* HeringBinaryF8)
    (hperiod : ∀ x : HeringBinaryF8, theta^[5] x = x)
    (hnontrivial : ∃ x : HeringBinaryF8, theta x ≠ x) : False := by
  let theta8 : HeringF8 ≃+* HeringF8 := heringF8TransportRingAut theta
  obtain ⟨i, hi⟩ := heringF8_ringEquiv_eq_frobenius theta8
  have hfun : heringF8Theta i = theta8 := by
    funext x
    exact (hi x).symm
  have hperiod8 : ∀ x : HeringF8, (heringF8Theta i)^[5] x = x := by
    intro x
    rw [hfun]
    calc
      theta8^[5] x =
          heringBinaryF8Equiv (theta^[5] (heringBinaryF8Equiv.symm x)) :=
        heringF8TransportRingAut_iterate theta 5 x
      _ = x := by rw [hperiod]; simp
  have hnontrivial8 : ∃ x : HeringF8, heringF8Theta i x ≠ x := by
    rcases hnontrivial with ⟨x, hx⟩
    refine ⟨heringBinaryF8Equiv x, ?_⟩
    intro hfix
    apply hx
    apply heringBinaryF8Equiv.injective
    have hthetaFix : theta8 (heringBinaryF8Equiv x) =
        heringBinaryF8Equiv x := (hi _).trans hfix
    simpa [theta8, heringF8TransportRingAut] using hthetaFix
  exact heringF8_typeD_obstruction i hperiod8 hnontrivial8

/-- A fixed transvection of the additive group of `F₈` cannot lift through
the type-A Higman square map. -/
public theorem ii1Hering31F8_typeA_no_lift
    (theta : BinaryGaloisField 3 ≃+* BinaryGaloisField 3)
    (htheta : ∃ x : BinaryGaloisField 3, theta x ≠ x)
    (L : BinaryGaloisField 3 ≃+ BinaryGaloisField 3)
    (hL : ∀ a : BinaryGaloisField 3,
      L a * theta (L a) =
        ii1Hering31F8Transvection (a * theta a)) : False := by
  apply heringBinaryF8_typeA_no_lift theta htheta L
  intro a
  simpa [heringBinaryF8QuadA] using hL a

/-- A fixed transvection of the additive group of `F₈` cannot lift through
any valid type-B Higman square map. -/
public theorem ii1Hering31F8_typeB_no_lift
    (theta : BinaryGaloisField 3 ≃+* BinaryGaloisField 3)
    (epsilon : BinaryGaloisField 3) (hepsilon : epsilon ≠ 0)
    (hanisotropic : ∀ a b : BinaryGaloisField 3, a ≠ 0 → b ≠ 0 →
      a * theta a + epsilon * a * theta b + b * theta b ≠ 0)
    (L : (BinaryGaloisField 3 × BinaryGaloisField 3) ≃+
      (BinaryGaloisField 3 × BinaryGaloisField 3))
    (hL : ∀ a : BinaryGaloisField 3 × BinaryGaloisField 3,
      (L a).1 * theta (L a).1 +
          epsilon * (L a).1 * theta (L a).2 +
          (L a).2 * theta (L a).2 =
        ii1Hering31F8Transvection
          (a.1 * theta a.1 + epsilon * a.1 * theta a.2 +
            a.2 * theta a.2)) : False := by
  apply heringBinaryF8_typeB_no_lift theta epsilon hepsilon
    (by simpa [heringBinaryF8QuadB] using hanisotropic) L
  intro a
  simpa [heringBinaryF8QuadB] using hL a

/-- A fixed transvection of the additive group of `F₈` cannot lift through
any valid type-C Higman square map. -/
public theorem ii1Hering31F8_typeC_no_lift
    (theta : BinaryGaloisField 3 ≃+* BinaryGaloisField 3)
    (epsilon : BinaryGaloisField 3) (hepsilon : epsilon ≠ 0)
    (hthetaSquare : ∀ x : BinaryGaloisField 3,
      theta (theta (x ^ 2)) = x)
    (havoid : ∀ rho : BinaryGaloisField 3,
      epsilon ≠ rho⁻¹ + theta (rho ^ 2) * rho)
    (L : (BinaryGaloisField 3 × BinaryGaloisField 3) ≃+
      (BinaryGaloisField 3 × BinaryGaloisField 3))
    (hL : ∀ a : BinaryGaloisField 3 × BinaryGaloisField 3,
      (L a).1 * theta (L a).1 +
          epsilon * (L a).1 ^ 4 * theta ((L a).2 ^ 2) + (L a).2 ^ 2 =
        ii1Hering31F8Transvection
          (a.1 * theta a.1 + epsilon * a.1 ^ 4 * theta (a.2 ^ 2) +
            a.2 ^ 2)) : False := by
  apply heringBinaryF8_typeC_no_lift theta epsilon hepsilon
    hthetaSquare havoid L
  intro a
  simpa [heringBinaryF8QuadC] using hL a

/-- Type D cannot occur over the binary field of order eight: its required
nontrivial automorphism cannot have period five. -/
public theorem ii1Hering31F8_typeD_false
    (theta : BinaryGaloisField 3 ≃+* BinaryGaloisField 3)
    (hperiod : ∀ x : BinaryGaloisField 3, theta^[5] x = x)
    (hnontrivial : ∃ x : BinaryGaloisField 3, theta x ≠ x) : False :=
  heringBinaryF8_typeD_false theta hperiod hnontrivial

end CFSG.BenderSuzuki
