module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_1
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Unbundled

namespace CFSG
end CFSG
open CFSG
/-!
# Peterfalvi, Section 1, Proposition (1.3)

This file is the Lean target for `PFtest/Blueprint/section1/proposition_1_3.tex`.

Current scope discipline:

* No Lean files outside `PFtest` are imported or read.
* The book-facing conjunction has been split into public main declarations;
  theorem-local core lemmas remain private.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.Section1
universe u
universe v

/-! ## Basic notation for Proposition (1.3) -/

@[expose]
public def scalarProduct (G : Type*) [Finite G] (phi psi : ClassFunction G) : ℂ :=
  (Nat.card G : ℂ)⁻¹ * ∑ g : G, phi g * star (psi g)

public def supportedOn {G : Type*} (phi : ClassFunction G) (A : Set G) : Prop :=
  ∀ g, g ∉ A → phi g = 0

public theorem supportedOn_iff
    {G : Type*} {phi : ClassFunction G} {A : Set G} :
    supportedOn phi A ↔ ∀ g, g ∉ A → phi g = 0 :=
  Iff.rfl

public def classFunctionsOn (G : Type*) (A : Set G) : Submodule ℂ (ClassFunction G) where
  carrier := {phi | supportedOn phi A}
  zero_mem' _ _ := by simp
  add_mem' hphi hpsi g hg := by simp [hphi g hg, hpsi g hg]
  smul_mem' z phi hphi g hg := by simp [hphi g hg]

public theorem mem_classFunctionsOn
    {G : Type*} {A : Set G} {phi : ClassFunction G} :
    phi ∈ classFunctionsOn G A ↔ supportedOn phi A :=
  Iff.rfl


/-! ## Small linear-algebra nodes for Proposition (1.3) -/


private lemma scalarProduct_zero_left
    {H : Type*} [Finite H] (phi : ClassFunction H) :
    scalarProduct H 0 phi = 0 := by
  simp [scalarProduct]


private lemma scalarProduct_add_left
    {H : Type*} [Finite H] (phi1 phi2 psi : ClassFunction H) :
    scalarProduct H (phi1 + phi2) psi =
      scalarProduct H phi1 psi + scalarProduct H phi2 psi := by
  simp [scalarProduct, mul_add, Finset.sum_add_distrib, right_distrib]

private lemma scalarProduct_smul_left
    {H : Type*} [Finite H] (z : ℂ) (phi psi : ClassFunction H) :
    scalarProduct H (z • phi) psi = z * scalarProduct H phi psi := by
  calc
    scalarProduct H (z • phi) psi
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, z * (phi g * star (psi g)) := by
            simp [scalarProduct, mul_assoc]
    _ = (Nat.card H : ℂ)⁻¹ * (z * ∑ g : H, phi g * star (psi g)) := by
          rw [← Finset.mul_sum]
    _ = z * scalarProduct H phi psi := by
          simp [scalarProduct, mul_left_comm]

private lemma scalarProduct_add_right
    {H : Type*} [Finite H] (phi psi1 psi2 : ClassFunction H) :
    scalarProduct H phi (psi1 + psi2) =
      scalarProduct H phi psi1 + scalarProduct H phi psi2 := by
  simp [scalarProduct, mul_add, Finset.sum_add_distrib]

private lemma scalarProduct_smul_right
    {H : Type*} [Finite H] (z : ℂ) (phi psi : ClassFunction H) :
    scalarProduct H phi (z • psi) = scalarProduct H phi psi * star z := by
  calc
    scalarProduct H phi (z • psi)
        = (Nat.card H : ℂ)⁻¹ * ∑ g : H, (phi g * star (psi g)) * star z := by
            unfold scalarProduct
            congr 1
            refine Finset.sum_congr rfl ?_
            intro g hg
            simp [mul_left_comm, mul_comm]
    _ = (Nat.card H : ℂ)⁻¹ * ((∑ g : H, phi g * star (psi g)) * star z) := by
          rw [Finset.sum_mul]
    _ = scalarProduct H phi psi * star z := by
          simp [scalarProduct, mul_left_comm, mul_comm]

private lemma scalarProduct_sub_right
    {H : Type*} [Finite H] (phi psi1 psi2 : ClassFunction H) :
    scalarProduct H phi (psi1 - psi2) =
      scalarProduct H phi psi1 - scalarProduct H phi psi2 := by
  calc
    scalarProduct H phi (psi1 - psi2)
        = scalarProduct H phi (psi1 + (-1 : ℂ) • psi2) := by
            congr 1
            ext g
            simp [sub_eq_add_neg]
    _ = scalarProduct H phi psi1 + scalarProduct H phi ((-1 : ℂ) • psi2) := by
          rw [scalarProduct_add_right]
    _ = scalarProduct H phi psi1 - scalarProduct H phi psi2 := by
          rw [scalarProduct_smul_right]
          simp [sub_eq_add_neg]

lemma scalarProduct_sum_left
    {H I : Type*} [Finite H] [Fintype I]
    (psi : ClassFunction H) (d : I → ℂ) (phi : I → ClassFunction H) :
    scalarProduct H (∑ i, d i • phi i) psi =
      ∑ i, d i * scalarProduct H (phi i) psi := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simp [scalarProduct_zero_left]
  | @insert i s hi hs =>
      simp [hi, scalarProduct_add_left, scalarProduct_smul_left, hs]


/-! ## Proposition (1.3) -/


end CFSG.Section1
