module

import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import Mathlib.Algebra.BigOperators.Ring.Nat
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_8_27
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.example_1_3
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_2_6
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.FixedPointBruhat
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.ThetaEquationExtraction
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.SemidirectProduct
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.FrobeniusKernel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.XI.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.MatrixGroups.Suzuki
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.theorem_1c
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection3.lemma_3_2_a
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Character.Orthogonality

namespace CFSG
end CFSG
open CFSG

/-!
# Suzuki XI.11.15

The Suzuki-group recognition endpoint is isolated from XI.6.1 and XI.9.1.
-/

namespace CFSG.BenderSuzuki
namespace External

open _root_.CFSG.BenderSuzuki.MatrixGroups
open XI1115ThetaEquationExtraction
open scoped Pointwise commutatorElement IsMulCommutative

attribute [local simp] MulAction.subgroup_smul_def Subgroup.orderOf_coe
set_option synthInstance.maxHeartbeats 40000

universe u v

private theorem xi1115_exists_quadratic_refinement
    {V W : Type*}
    [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    [AddCommGroup W] [Module (ZMod 2) W]
    (B : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W)
    (hB_self : ∀ x : V, B x x = 0) :
    ∃ f : V → W, f 0 = 0 ∧
      ∀ x y : V, f (x + y) = f x + f y + B x y := by
  classical
  let d := Module.finrank (ZMod 2) V
  let basis : Module.Basis (Fin d) (ZMod 2) V :=
    Module.finBasis (ZMod 2) V
  have hadd_self (z : W) : z + z = 0 := by
    nth_rw 2 [← ZModModule.neg_eq_self z]
    exact add_neg_cancel z
  have hB_symm (x y : V) : B x y = B y x := by
    have hsum : B x y + B y x = 0 := by
      have h := hB_self (x + y)
      simp only [map_add, LinearMap.add_apply] at h
      rw [hB_self, hB_self] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      B x y = B x y + (B y x + B y x) := by
        rw [hadd_self, add_zero]
      _ = (B x y + B y x) + B y x := by abel
      _ = B y x := by rw [hsum, zero_add]
  let A : V →ₗ[ZMod 2] V →ₗ[ZMod 2] W :=
    basis.constr (S := ZMod 2) fun i =>
      basis.constr (S := ZMod 2) fun j =>
        if i < j then B (basis i) (basis j) else 0
  have hA_basis (i j : Fin d) :
      A (basis i) (basis j) =
        if i < j then B (basis i) (basis j) else 0 := by
    change
      (basis.constr (S := ZMod 2) fun i =>
        basis.constr (S := ZMod 2) fun j =>
          if i < j then B (basis i) (basis j) else 0)
        (basis i) (basis j) = _
    rw [basis.constr_basis, basis.constr_basis]
  have hA_polar : A + LinearMap.flip A = B := by
    apply basis.ext
    intro i
    apply basis.ext
    intro j
    simp only [LinearMap.add_apply, LinearMap.flip_apply]
    rw [hA_basis, hA_basis]
    by_cases hij : i = j
    · subst j
      simp [hB_self]
    · rcases lt_or_gt_of_ne hij with hij | hji
      · have hnji : ¬j < i := not_lt_of_ge hij.le
        simp [hij, hnji]
      · have hnij : ¬i < j := not_lt_of_ge hji.le
        simp [hji, hnij, hB_symm]
  let f : V → W := fun x => A x x
  refine ⟨f, by simp [f], ?_⟩
  intro x y
  have hp := LinearMap.congr_fun (LinearMap.congr_fun hA_polar x) y
  change A x y + A y x = B x y at hp
  change A (x + y) (x + y) = A x x + A y y + B x y
  calc
    A (x + y) (x + y) =
        A x x + A y x + (A x y + A y y) := by
          simp only [map_add, LinearMap.add_apply]
    _ = A x x + A y y + B x y := by rw [← hp]; abel

private theorem xi1115_normalize_typeA_coordinates
    {P : Type*} [Group P] {n : ℕ}
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (pairLift : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n → P)
    (cocycle : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n →
        PFAppendixIII.BinaryGaloisField n)
    (haddLeft : ∀ a b c, cocycle (a + b) c = cocycle a c + cocycle b c)
    (haddRight : ∀ a b c, cocycle a (b + c) = cocycle a b + cocycle a c)
    (hdiag : ∀ a, cocycle a a = a * theta a)
    (hone : pairLift 0 0 = 1)
    (hsurj : ∀ x : P, ∃ a z, x = pairLift a z)
    (hinj : ∀ a z b w, pairLift a z = pairLift b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pairLift a z * pairLift b w =
        pairLift (a + b) (z + w + cocycle a b))
    (quotientCoord : P → PFAppendixIII.BinaryGaloisField n)
    (centerCoord : PFAppendixIII.BinaryGaloisField n → P)
    (hquotientCoord : ∀ a z, quotientCoord (pairLift a z) = a)
    (hcenterCoord : ∀ z, pairLift 0 z = centerCoord z) :
    ∃ pairA : PFAppendixIII.BinaryGaloisField n →
        PFAppendixIII.BinaryGaloisField n → P,
      pairA 0 0 = 1 ∧
      (∀ x : P, ∃ a z, x = pairA a z) ∧
      (∀ a z b w, pairA a z = pairA b w → a = b ∧ z = w) ∧
      (∀ a z b w,
        pairA a z * pairA b w =
          pairA (a + b) (z + w + a * theta b)) ∧
      (∀ a z, quotientCoord (pairA a z) = a) ∧
      ∀ z, pairA 0 z = centerCoord z := by
  classical
  let K := PFAppendixIII.BinaryGaloisField n
  have hzeroLeft (b : K) : cocycle 0 b = 0 := by
    have h := haddLeft 0 0 b
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  have hzeroRight (a : K) : cocycle a 0 = 0 := by
    have h := haddRight a 0 0
    simpa only [zero_add, CharTwo.add_self_eq_zero] using h
  let cocycleL : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K :=
    { toFun := fun a =>
        { toFun := fun b => cocycle a b
          map_add' := haddRight a
          map_smul' := by
            intro c b
            have hc : c = 0 ∨ c = 1 := by
              fin_cases c
              · left; rfl
              · right; rfl
            rcases hc with rfl | rfl
            · simp [hzeroRight]
            · simp }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        exact haddLeft a b c
      map_smul' := by
        intro c a
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · left; rfl
          · right; rfl
        rcases hc with rfl | rfl
        · apply LinearMap.ext
          intro b
          simp [hzeroLeft]
        · simp }
  let thetaL : K →ₗ[ZMod 2] K :=
    theta.toAddEquiv.toLinearEquiv (fun (c : ZMod 2) x => by
      have hc : c = 0 ∨ c = 1 := by
        fin_cases c
        · left; rfl
        · right; rfl
      rcases hc with rfl | rfl <;> simp)
  let target : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K :=
    { toFun := fun a =>
        { toFun := fun b => a * thetaL b
          map_add' := by intro x y; simp [mul_add]
          map_smul' := by
            intro c b
            have hc : c = 0 ∨ c = 1 := by
              fin_cases c
              · left; rfl
              · right; rfl
            rcases hc with rfl | rfl <;> simp }
      map_add' := by
        intro a b
        apply LinearMap.ext
        intro c
        simp [add_mul]
      map_smul' := by
        intro c a
        have hc : c = 0 ∨ c = 1 := by
          fin_cases c
          · left; rfl
          · right; rfl
        rcases hc with rfl | rfl
        · apply LinearMap.ext
          intro b
          simp
        · simp }
  let B : K →ₗ[ZMod 2] K →ₗ[ZMod 2] K := cocycleL + target
  have hB_self (a : K) : B a a = 0 := by
    change cocycle a a + a * theta a = 0
    rw [hdiag]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨f, hf_zero, hf_add⟩ :=
    xi1115_exists_quadratic_refinement B hB_self
  let pairA : K → K → P := fun a z => pairLift a (z + f a)
  refine ⟨pairA, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pairA, hf_zero] using hone
  · intro x
    obtain ⟨a, z, hx⟩ := hsurj x
    refine ⟨a, z - f a, ?_⟩
    simpa [pairA] using hx
  · intro a z b w hab
    have h := hinj a (z + f a) b (w + f b) hab
    rcases h with ⟨rfl, hzw⟩
    refine ⟨rfl, add_right_cancel hzw⟩
  · intro a z b w
    rw [show pairA a z = pairLift a (z + f a) by rfl,
      show pairA b w = pairLift b (w + f b) by rfl, hmul]
    change pairLift (a + b)
        ((z + f a) + (w + f b) + cocycle a b) =
      pairLift (a + b) (z + w + a * theta b + f (a + b))
    congr 1
    rw [hf_add]
    change (z + f a) + (w + f b) + cocycle a b =
      z + w + a * theta b +
        (f a + f b + (cocycle a b + a * theta b))
    nth_rw 2 [← ZModModule.neg_eq_self (a * theta b)]
    abel
  · intro a z
    exact hquotientCoord a (z + f a)
  · intro z
    simpa [pairA, hf_zero] using hcenterCoord z

private theorem xi1115_exists_actor_equivariant_coordinates
    {D P : Type*} [Group D] [Finite D] [Group P]
    [MulDistribMulAction D P]
    (n : ℕ)
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (pair : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n → P)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField n)ˣ)
    (eQ : (P ⧸ Subgroup.center P) ≃*
      Multiplicative (PFAppendixIII.BinaryGaloisField n))
    (eZ : Subgroup.center P ≃*
      Multiplicative (PFAppendixIII.BinaryGaloisField n))
    (hDodd : Odd (Nat.card D))
    (hone : pair 0 0 = 1)
    (hsurj : ∀ x : P, ∃ a z, x = pair a z)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w =
        pair (a + b) (z + w + a * theta b))
    (hquotient : ∀ a z,
      (eQ (QuotientGroup.mk' (Subgroup.center P) (pair a z))).toAdd = a)
    (hcenter : ∀ z,
      pair 0 z = ((eZ.symm (Multiplicative.ofAdd z) :
        Subgroup.center P) : P))
    (hquotientAction : ∀ d : D, ∀ x : P,
      (eQ (QuotientGroup.mk' (Subgroup.center P) (d • x))).toAdd =
        (eD d : PFAppendixIII.BinaryGaloisField n) *
          (eQ (QuotientGroup.mk' (Subgroup.center P) x)).toAdd)
    (hcenterAction : ∀ d : D, ∀ z : PFAppendixIII.BinaryGaloisField n,
      d • ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center P) : P) =
        ((eZ.symm (Multiplicative.ofAdd
          ((eD d : PFAppendixIII.BinaryGaloisField n) *
            theta (eD d : PFAppendixIII.BinaryGaloisField n) * z)) :
              Subgroup.center P) : P)) :
    ∃ pairB : PFAppendixIII.BinaryGaloisField n →
        PFAppendixIII.BinaryGaloisField n → P,
      pairB 0 0 = 1 ∧
      (∀ x : P, ∃ a z, x = pairB a z) ∧
      (∀ a z b w, pairB a z = pairB b w → a = b ∧ z = w) ∧
      (∀ a z b w,
        pairB a z * pairB b w =
          pairB (a + b) (z + w + a * theta b)) ∧
      ∀ d : D, ∀ a z,
        d • pairB a z =
          pairB ((eD d : PFAppendixIII.BinaryGaloisField n) * a)
            ((eD d : PFAppendixIII.BinaryGaloisField n) *
              theta (eD d : PFAppendixIII.BinaryGaloisField n) * z) := by
  classical
  let K := PFAppendixIII.BinaryGaloisField n
  let pairFun : K × K → P := fun az => pair az.1 az.2
  have hpairBijective : Function.Bijective pairFun := by
    constructor
    · intro az bw hab
      exact Prod.ext (hinj az.1 az.2 bw.1 bw.2 hab).1
        (hinj az.1 az.2 bw.1 bw.2 hab).2
    · intro x
      obtain ⟨a, z, hx⟩ := hsurj x
      exact ⟨(a, z), hx.symm⟩
  let pairEquiv : K × K ≃ P := Equiv.ofBijective pairFun hpairBijective
  let lambda : D → K := fun d => (eD d : K)
  let mu : D → K := fun d => lambda d * theta (lambda d)
  let shear : D → K → K := fun d a =>
    (pairEquiv.symm (d • pair a 0)).2
  have hactor_zero (d : D) (a : K) :
      d • pair a 0 = pair (lambda d * a) (shear d a) := by
    let az := pairEquiv.symm (d • pair a 0)
    have heq : pair az.1 az.2 = d • pair a 0 := by
      change pairEquiv az = d • pair a 0
      exact pairEquiv.apply_symm_apply _
    have hfirst : az.1 = lambda d * a := by
      calc
        az.1 =
            (eQ (QuotientGroup.mk' (Subgroup.center P)
              (pair az.1 az.2))).toAdd := (hquotient az.1 az.2).symm
        _ = (eQ (QuotientGroup.mk' (Subgroup.center P)
              (d • pair a 0))).toAdd := by rw [heq]
        _ = lambda d *
              (eQ (QuotientGroup.mk' (Subgroup.center P)
                (pair a 0))).toAdd := hquotientAction d (pair a 0)
        _ = lambda d * a := by rw [hquotient]
    change d • pair a 0 = pair (lambda d * a) az.2
    rw [← hfirst]
    exact heq.symm
  have hpair_split (a z : K) : pair a z = pair a 0 * pair 0 z := by
    rw [hmul]
    simp
  have hactor (d : D) (a z : K) :
      d • pair a z =
        pair (lambda d * a) (shear d a + mu d * z) := by
    rw [hpair_split, smul_mul', hactor_zero, hcenter, hcenterAction,
      ← hcenter, hmul]
    simp [mu, lambda]
  have hshear_add (d : D) (a b : K) :
      shear d (a + b) = shear d a + shear d b := by
    have h := congrArg (fun x : P => d • x) (hmul a 0 b 0)
    change d • (pair a 0 * pair b 0) =
      d • pair (a + b) (0 + 0 + a * theta b) at h
    rw [smul_mul', hactor_zero, hactor_zero, hmul, hactor] at h
    have hz := (hinj _ _ _ _ h).2
    simp only [mul_add] at hz
    have hmu :
        lambda d * a * theta (lambda d * b) =
          mu d * (a * theta b) := by
      simp [mu, map_mul]
      ring
    rw [hmu] at hz
    simp only [mul_zero, zero_add] at hz
    exact (add_right_cancel hz).symm
  have hmu_mul (e d : D) : mu (e * d) = mu e * mu d := by
    simp [mu, lambda, map_mul]
    ring
  have hshear_mul (e d : D) (a : K) :
      shear (e * d) a =
        shear e (lambda d * a) + mu e * shear d a := by
    have h := congrArg (fun x : P => e • x) (hactor_zero d a)
    change e • (d • pair a 0) =
      e • pair (lambda d * a) (shear d a) at h
    rw [← mul_smul, hactor_zero, hactor] at h
    have hz := (hinj _ _ _ _ h).2
    simpa [lambda, map_mul, mul_assoc] using hz
  letI : Fintype D := Fintype.ofFinite D
  let correction : K → K := fun a =>
    ∑ d : D, (mu d)⁻¹ * shear d a
  have hmu_ne (d : D) : mu d ≠ 0 := by
    exact mul_ne_zero (eD d).ne_zero
      ((map_ne_zero theta).mpr (eD d).ne_zero)
  have hcorrection_add (a b : K) :
      correction (a + b) = correction a + correction b := by
    simp only [correction, hshear_add, mul_add, Finset.sum_add_distrib]
  have hsum_const (x : K) : (∑ _d : D, x) = x := by
    rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rcases hDodd with ⟨r, hr⟩
    rw [hr, add_nsmul, mul_nsmul, CharTwo.two_nsmul, nsmul_zero,
      zero_add, one_nsmul]
  have hcorrection_action (d : D) (a : K) :
      correction (lambda d * a) =
        shear d a + mu d * correction a := by
    have hpoint (e : D) :
        (mu e)⁻¹ * shear e (lambda d * a) =
          mu d * ((mu (e * d))⁻¹ * shear (e * d) a) + shear d a := by
      have hs : shear e (lambda d * a) =
          shear (e * d) a + mu e * shear d a := by
        rw [hshear_mul]
        simp only [add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [hs, mul_add]
      have hcoef : (mu e)⁻¹ = mu d * (mu (e * d))⁻¹ := by
        have hinv_product (x y : K) (hy : y ≠ 0) :
            x⁻¹ = y * (x * y)⁻¹ := by
          rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ hy, one_mul]
        rw [hmu_mul]
        exact hinv_product (mu e) (mu d) (hmu_ne d)
      nth_rewrite 1 [hcoef]
      rw [← mul_assoc (mu e)⁻¹ (mu e), inv_mul_cancel₀ (hmu_ne e), one_mul]
      ring
    calc
      correction (lambda d * a) =
          ∑ e : D,
            (mu d * ((mu (e * d))⁻¹ * shear (e * d) a) + shear d a) := by
              apply Finset.sum_congr rfl
              intro e _he
              exact hpoint e
      _ = mu d * (∑ e : D,
            (mu (e * d))⁻¹ * shear (e * d) a) +
            ∑ _e : D, shear d a := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = mu d * correction a + shear d a := by
              have hreindex :
                  (∑ e : D, (mu (e * d))⁻¹ * shear (e * d) a) =
                    correction a := by
                change (∑ e : D, (mu (e * d))⁻¹ * shear (e * d) a) =
                  ∑ e : D, (mu e)⁻¹ * shear e a
                simpa using (Equiv.sum_comp (Equiv.mulRight d)
                  (fun e : D => (mu e)⁻¹ * shear e a))
              rw [hreindex, hsum_const]
      _ = shear d a + mu d * correction a := add_comm _ _
  have hcorrection_zero : correction 0 = 0 := by
    have h := hcorrection_add 0 0
    rw [zero_add] at h
    exact add_left_cancel (h.symm.trans (add_zero (correction 0)).symm)
  let pairB : K → K → P := fun a z => pair a (z + correction a)
  refine ⟨pairB, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pairB, hcorrection_zero] using hone
  · intro x
    obtain ⟨a, z, hx⟩ := hsurj x
    refine ⟨a, z - correction a, ?_⟩
    simpa [pairB] using hx
  · intro a z b w hab
    have h := hinj a (z + correction a) b (w + correction b) hab
    rcases h with ⟨rfl, hzw⟩
    exact ⟨rfl, add_right_cancel hzw⟩
  · intro a z b w
    rw [show pairB a z = pair a (z + correction a) by rfl,
      show pairB b w = pair b (w + correction b) by rfl, hmul]
    change pair (a + b)
        ((z + correction a) + (w + correction b) + a * theta b) =
      pair (a + b) (z + w + a * theta b + correction (a + b))
    congr 1
    rw [hcorrection_add]
    abel
  · intro d a z
    change d • pair a (z + correction a) =
      pair (lambda d * a)
        (mu d * z + correction (lambda d * a))
    rw [hactor, hcorrection_action]
    congr 1
    ring

private theorem xi1115_inverse_actor_coordinates
    {D P : Type*} [Group D] [Group P]
    [MulDistribMulAction D P]
    (n : ℕ)
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (pair : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n → P)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField n)ˣ)
    (hone : pair 0 0 = 1)
    (hsurj : ∀ x : P, ∃ a z, x = pair a z)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w =
        pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z =
        pair ((eD d : PFAppendixIII.BinaryGaloisField n) * a)
          ((eD d : PFAppendixIII.BinaryGaloisField n) *
            theta (eD d : PFAppendixIII.BinaryGaloisField n) * z)) :
    ∃ pair' : PFAppendixIII.BinaryGaloisField n →
        PFAppendixIII.BinaryGaloisField n → P,
      ∃ eD' : D ≃* (PFAppendixIII.BinaryGaloisField n)ˣ,
        pair' 0 0 = 1 ∧
        (∀ x : P, ∃ a z, x = pair' a z) ∧
        (∀ a z b w, pair' a z = pair' b w → a = b ∧ z = w) ∧
        (∀ a z b w,
          pair' a z * pair' b w =
            pair' (a + b) (z + w + a * theta.symm b)) ∧
        (∀ d : D, ∀ a z,
          d • pair' a z =
            pair' ((eD' d : PFAppendixIII.BinaryGaloisField n) * a)
              ((eD' d : PFAppendixIII.BinaryGaloisField n) *
                theta.symm
                  (eD' d : PFAppendixIII.BinaryGaloisField n) * z)) ∧
        (∀ a z, pair' a z =
          pair (theta.symm a) (z + a * theta.symm a)) ∧
        ∀ d : D,
          (eD' d : PFAppendixIII.BinaryGaloisField n) =
            theta (eD d : PFAppendixIII.BinaryGaloisField n) := by
  let pair' : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n → P :=
    fun a z => pair (theta.symm a) (z + a * theta.symm a)
  let eD' : D ≃* (PFAppendixIII.BinaryGaloisField n)ˣ :=
    eD.trans (Units.mapEquiv theta.toMulEquiv)
  refine ⟨pair', eD', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [pair'] using hone
  · intro x
    obtain ⟨c, t, hx⟩ := hsurj x
    refine ⟨theta c, t + theta c * c, ?_⟩
    rw [hx]
    change pair c t =
      pair (theta.symm (theta c))
        ((t + theta c * c) + theta c * theta.symm (theta c))
    rw [theta.symm_apply_apply]
    congr 1
    symm
    calc
      t + theta c * c + theta c * c =
          t + (theta c * c + theta c * c) := by rw [add_assoc]
      _ = t := by rw [CharTwo.add_self_eq_zero, add_zero]
  · intro a z b w hab
    have h := hinj (theta.symm a) (z + a * theta.symm a)
      (theta.symm b) (w + b * theta.symm b) hab
    have hab' : a = b := theta.symm.injective h.1
    subst b
    exact ⟨rfl, add_right_cancel h.2⟩
  · intro a z b w
    dsimp only [pair']
    rw [hmul, theta.apply_symm_apply]
    congr 1
    · exact (map_add theta.symm a b).symm
    · rw [map_add]
      ring_nf
      simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  · intro d a z
    change d • pair (theta.symm a) (z + a * theta.symm a) =
      pair (theta.symm
          ((eD' d : PFAppendixIII.BinaryGaloisField n) * a))
        (((eD' d : PFAppendixIII.BinaryGaloisField n) *
            theta.symm
              (eD' d : PFAppendixIII.BinaryGaloisField n) * z) +
          ((eD' d : PFAppendixIII.BinaryGaloisField n) * a) *
            theta.symm
              ((eD' d : PFAppendixIII.BinaryGaloisField n) * a))
    rw [hactor]
    congr 1
    · simp [eD', map_mul]
    · simp [eD', map_mul]
      ring
  · intro a z
    rfl
  · intro d
    rfl

set_option maxHeartbeats 800000 in
private theorem xi1115_normalize_typeA_central_involution
    {D P : Type*} [Group D] [Finite D] [IsMulCommutative D]
    [Group P] [MulDistribMulAction D P] {n : ℕ}
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (eK : D ≃* (PFAppendixIII.BinaryGaloisField n)ˣ)
    (pairN : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n → P)
    (hone : pairN 0 0 = 1)
    (hsurj : ∀ x : P, ∃ a z, x = pairN a z)
    (hinj : ∀ a z b w, pairN a z = pairN b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pairN a z * pairN b w =
        pairN (a + b) (z + w + a * theta b))
    (haction : ∀ d a z,
      d • pairN a z =
        pairN ((eK d : PFAppendixIII.BinaryGaloisField n) * a)
          ((eK d : PFAppendixIII.BinaryGaloisField n) *
            theta (eK d : PFAppendixIII.BinaryGaloisField n) * z))
    (hregular : PFAppendixIII.ActionRegularOn D P
      (PFAppendixIII.involutions P))
    (j : P) (hj : PFAppendixIII.IsInvolution j) :
    ∃ pairJ : PFAppendixIII.BinaryGaloisField n →
        PFAppendixIII.BinaryGaloisField n → P,
      pairJ 0 0 = 1 ∧
      (∀ x : P, ∃ a z, x = pairJ a z) ∧
      (∀ a z b w, pairJ a z = pairJ b w → a = b ∧ z = w) ∧
      (∀ a z b w,
        pairJ a z * pairJ b w =
          pairJ (a + b) (z + w + a * theta b)) ∧
      (∀ d a z,
        d • pairJ a z =
          pairJ ((eK d : PFAppendixIII.BinaryGaloisField n) * a)
            ((eK d : PFAppendixIII.BinaryGaloisField n) *
              theta (eK d : PFAppendixIII.BinaryGaloisField n) * z)) ∧
      pairJ 0 1 = j := by
  let K := PFAppendixIII.BinaryGaloisField n
  have hbaseNe : pairN 0 1 ≠ 1 := by
    intro h
    have hcoord := hinj 0 1 0 0 (h.trans hone.symm)
    exact one_ne_zero hcoord.2
  have hbaseSq : pairN 0 1 ^ 2 = 1 := by
    rw [pow_two, hmul]
    simpa only [CharTwo.add_self_eq_zero, zero_add, zero_mul] using hone
  have hbaseInv : pairN 0 1 ∈ PFAppendixIII.involutions P :=
    ⟨hbaseNe, hbaseSq⟩
  obtain ⟨d, hd, _⟩ :=
    hregular.2 (pairN 0 1) hbaseInv j hj
  let pairJ : K → K → P := fun a z => d • pairN a z
  refine ⟨pairJ, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [pairJ, hone]
  · intro x
    obtain ⟨a, z, hx⟩ := hsurj (d⁻¹ • x)
    refine ⟨a, z, ?_⟩
    calc
      x = d • (d⁻¹ • x) := (smul_inv_smul d x).symm
      _ = pairJ a z := by rw [hx]
  · intro a z b w hab
    exact hinj a z b w (smul_left_cancel d hab)
  · intro a z b w
    dsimp [pairJ]
    rw [← smul_mul', hmul]
  · intro e a z
    dsimp [pairJ]
    rw [← mul_smul, mul_comm e d, mul_smul, haction]
  · exact hd.symm


set_option maxHeartbeats 800000 in
private theorem xi1115_theta_mobius_equiv_punctured
    {n : ℕ}
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (hfixed : ∀ x : PFAppendixIII.BinaryGaloisField n,
      theta x = x → x = 0 ∨ x = 1) :
    let K := PFAppendixIII.BinaryGaloisField n
    let X := {x : K // x ≠ 0 ∧ x ≠ 1}
    ∃ e : X ≃ X, ∀ x : X,
      (e x : K) = (1 + theta (x : K)) / (1 + (x : K)) := by
  classical
  let K := PFAppendixIII.BinaryGaloisField n
  let X := {x : K // x ≠ 0 ∧ x ≠ 1}
  have hden (x : X) : (1 : K) + x ≠ 0 := by
    intro h
    apply x.2.2
    exact ((eq_neg_of_add_eq_zero_left h).trans
      (CharTwo.neg_eq (x : K))).symm
  have hnum (x : X) : (1 : K) + theta x ≠ 0 := by
    intro h
    have hthetaOne : theta (x : K) = 1 :=
      ((eq_neg_of_add_eq_zero_left h).trans
        (CharTwo.neg_eq (theta (x : K)))).symm
    apply x.2.2
    apply theta.injective
    simpa using hthetaOne
  let mobius : X → X := fun x =>
    ⟨(1 + theta (x : K)) / (1 + (x : K)),
      div_ne_zero (hnum x) (hden x), by
        intro h
        have h' := (div_eq_one_iff_eq (hden x)).mp h
        have htheta : theta (x : K) = x := add_left_cancel h'
        rcases hfixed x htheta with hx | hx
        · exact x.2.1 hx
        · exact x.2.2 hx⟩
  have hmobiusInjective : Function.Injective mobius := by
    intro x y hxy
    have hval := congrArg (fun z : X => (z : K)) hxy
    change (1 + theta (x : K)) / (1 + (x : K)) =
      (1 + theta (y : K)) / (1 + (y : K)) at hval
    let t : K := (1 + (x : K)) / (1 + (y : K))
    have htne : t ≠ 0 := div_ne_zero (hden x) (hden y)
    have htfix : theta t = t := by
      dsimp [t]
      simp only [map_div₀, map_add, map_one]
      field_simp [hden x, hden y, hnum x, hnum y] at hval ⊢
      ring_nf at hval ⊢
      exact hval
    have htOne : t = 1 := (hfixed t htfix).resolve_left htne
    apply Subtype.ext
    dsimp [t] at htOne
    have htOne' := (div_eq_one_iff_eq (hden y)).mp htOne
    exact add_left_cancel htOne'
  have hmobiusBijective : Function.Bijective mobius :=
    (Nat.bijective_iff_injective_and_card mobius).2
      ⟨hmobiusInjective, rfl⟩
  let e : X ≃ X := Equiv.ofBijective mobius hmobiusBijective
  refine ⟨e, ?_⟩
  intro x
  rfl

set_option maxHeartbeats 800000 in
/-- Orbit exclusion normalizes the second coordinate of the distinguished
order-four element.  The only field-theoretic input is that `theta` fixes just
`0` and `1`; the punctured-field Mobius equivalence is constructed above. -/
private theorem xi1115_rho_zero_or_one_of_orbit_exclusion
    {F D : Type*} [Group F] [Group D] [MulDistribMulAction D F]
    {n : ℕ}
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (pair : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n → F)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField n)ˣ)
    (hone : pair 0 0 = 1)
    (hmul : ∀ a z b w,
      pair a z * pair b w =
        pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z =
        pair ((eD d : PFAppendixIII.BinaryGaloisField n) * a)
          ((eD d : PFAppendixIII.BinaryGaloisField n) *
            theta (eD d : PFAppendixIII.BinaryGaloisField n) * z))
    (hfixed : ∀ x : PFAppendixIII.BinaryGaloisField n,
      theta x = x → x = 0 ∨ x = 1)
    (g : F) (rho : PFAppendixIII.BinaryGaloisField n)
    (hg : g = pair 1 rho)
    (hnotOrbit : ∀ h : D, h ≠ 1 →
      g⁻¹ * (h⁻¹ • g) ∉ MulAction.orbit D g) :
    rho = 0 ∨ rho = 1 := by
  let K := PFAppendixIII.BinaryGaloisField n
  by_cases hrho0 : rho = 0
  · exact Or.inl hrho0
  right
  by_contra hrho1
  let X := {x : K // x ≠ 0 ∧ x ≠ 1}
  let c : K := (1 + rho⁻¹)⁻¹
  have hbase : (1 : K) + rho⁻¹ ≠ 0 := by
    intro h
    apply hrho1
    have hinv : rho⁻¹ = 1 :=
      ((eq_neg_of_add_eq_zero_left h).trans
        (CharTwo.neg_eq (rho⁻¹))).symm
    exact inv_eq_one.mp hinv
  have hRhoAdd : (1 : K) + rho ≠ 0 := by
    intro h
    apply hrho1
    exact ((eq_neg_of_add_eq_zero_left h).trans
      (CharTwo.neg_eq rho)).symm
  have hc0 : c ≠ 0 := inv_ne_zero hbase
  have hc1 : c ≠ 1 := by
    intro hc
    have hbaseOne : (1 : K) + rho⁻¹ = 1 := inv_eq_one.mp hc
    have hinvZero : rho⁻¹ = 0 := by
      apply add_left_cancel (a := (1 : K))
      simpa using hbaseOne
    exact inv_ne_zero hrho0 hinvZero
  obtain ⟨mobius, hmobiusSpec⟩ :=
    xi1115_theta_mobius_equiv_punctured theta hfixed
  obtain ⟨mu, hmu⟩ := mobius.surjective (⟨c, hc0, hc1⟩ : X)
  have hratio :
      (1 + theta (mu : K)) / (1 + (mu : K)) = c := by
    calc
      (1 + theta (mu : K)) / (1 + (mu : K)) =
          (mobius mu : K) := (hmobiusSpec mu).symm
      _ = c := congrArg Subtype.val hmu
  have hmu0 : (mu : K) ≠ 0 := mu.2.1
  have hmu1 : (mu : K) ≠ 1 := mu.2.2
  have hdenMu : (1 : K) + (mu : K) ≠ 0 := by
    intro h
    apply hmu1
    exact ((eq_neg_of_add_eq_zero_left h).trans
      (CharTwo.neg_eq (mu : K))).symm
  have hscalar :
      1 + theta (mu : K) =
        rho * ((mu : K) + theta (mu : K)) := by
    have hcFormula : c = rho / (1 + rho) := by
      dsimp [c]
      rw [show (1 : K) + rho⁻¹ = (1 + rho) / rho by
        rw [div_eq_mul_inv, add_mul, one_mul, mul_inv_cancel₀ hrho0]
        exact add_comm _ _]
      rw [inv_div]
    rw [hcFormula] at hratio
    have hcross := (div_eq_div_iff hdenMu hRhoAdd).mp hratio
    have hsum :
        (1 + theta (mu : K)) +
            rho * ((mu : K) + theta (mu : K)) = 0 := by
      calc
        (1 + theta (mu : K)) +
              rho * ((mu : K) + theta (mu : K)) =
            (1 + theta (mu : K)) * (1 + rho) +
              rho * (1 + (mu : K)) := by
                ring_nf
                simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
        _ = rho * (1 + (mu : K)) + rho * (1 + (mu : K)) := by
          rw [hcross]
        _ = 0 := CharTwo.add_self_eq_zero _
    exact (eq_neg_of_add_eq_zero_left hsum).trans
      (CharTwo.neg_eq (rho * ((mu : K) + theta (mu : K))))
  let muUnit : Kˣ := Units.mk0 (mu : K) hmu0
  let h : D := eD.symm muUnit⁻¹
  have heDh : (eD h : K) = (mu : K)⁻¹ := by
    simp [h, muUnit]
  have heDhInv : (eD h⁻¹ : K) = (mu : K) := by
    simp only [map_inv, Units.val_inv_eq_inv_val, heDh, inv_inv]
  have hhne : h ≠ 1 := by
    intro hh
    have heq : (eD h : K) = 1 := by
      simpa using congrArg (fun d : D => (eD d : K)) hh
    exact hmu1 (inv_eq_one.mp (heDh.symm.trans heq))
  let delta : K := 1 + (mu : K)
  have hdelta0 : delta ≠ 0 := hdenMu
  let d : D := eD.symm (Units.mk0 delta hdelta0)
  have heDd : (eD d : K) = delta := by simp [d]
  have hsecond :
      rho + 1 + (mu : K) * theta (mu : K) * rho + theta (mu : K) =
        delta * theta delta * rho := by
    rw [show theta delta = 1 + theta (mu : K) by simp [delta]]
    calc
      rho + 1 + (mu : K) * theta (mu : K) * rho + theta (mu : K) =
          rho + (mu : K) * theta (mu : K) * rho +
            (1 + theta (mu : K)) := by abel
      _ = rho + (mu : K) * theta (mu : K) * rho +
            rho * ((mu : K) + theta (mu : K)) := by rw [hscalar]
      _ = delta * (1 + theta (mu : K)) * rho := by
        dsimp [delta]
        ring
  have hgInv : g⁻¹ = pair 1 (rho + 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hg, hmul]
    calc
      pair (1 + 1) (rho + (rho + 1) + 1 * theta 1) = pair 0 0 := by
        congr 1
        · exact CharTwo.add_self_eq_zero 1
        · rw [map_one, mul_one]
          calc
            rho + (rho + 1) + 1 = (rho + rho) + (1 + 1) := by abel
            _ = 0 := by simp only [CharTwo.add_self_eq_zero]
      _ = 1 := hone
  have hxOrbit : g⁻¹ * (h⁻¹ • g) = d • g := by
    rw [hgInv, hg, hactor, hactor, hmul]
    rw [heDhInv, heDd]
    simp only [one_mul, mul_one]
    rw [hsecond]
  exact hnotOrbit h hhne
    (MulAction.mem_orbit_iff.mpr ⟨d, hxOrbit.symm⟩)


set_option maxHeartbeats 800000 in
private theorem xi1115_theta_factor_nonexceptional
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K) (xi mu : K)
    (hxi : xi ≠ 0)
    (hthetaXiOne : theta xi ≠ 1)
    (hmuNorm :
      mu * theta mu =
        xi⁻¹ ^ 2 * (theta xi)⁻¹ ^ 2 + xi⁻¹ * (theta xi)⁻¹)
    (hfactor :
      mu * (xi + (theta xi)⁻¹) *
          (1 + (theta xi)⁻¹ + xi⁻¹ * (theta xi)⁻¹) =
        (1 + xi⁻¹ ^ 2 * (theta xi)⁻¹) *
          (1 + (theta xi)⁻¹ + xi⁻¹ * (theta xi)⁻¹))
    (hnonexceptional :
      1 + (theta xi)⁻¹ + xi⁻¹ * (theta xi)⁻¹ ≠ 0) :
    theta (theta xi) = xi ^ 2 := by
  have hbase :
      mu * (xi + (theta xi)⁻¹) =
        1 + xi⁻¹ ^ 2 * (theta xi)⁻¹ := by
    exact mul_right_cancel₀ hnonexceptional hfactor
  have hbaseTheta := congrArg theta hbase
  simp only [map_mul, map_add, map_one, map_inv₀, map_pow] at hbaseTheta
  have hprod :
      (mu * theta mu) *
          ((xi + (theta xi)⁻¹) *
            (theta xi + (theta (theta xi))⁻¹)) =
        (1 + xi⁻¹ ^ 2 * (theta xi)⁻¹) *
          (1 + (theta xi)⁻¹ ^ 2 * (theta (theta xi))⁻¹) := by
    calc
      (mu * theta mu) *
          ((xi + (theta xi)⁻¹) *
            (theta xi + (theta (theta xi))⁻¹)) =
          (mu * (xi + (theta xi)⁻¹)) *
            (theta mu *
              (theta xi + (theta (theta xi))⁻¹)) := by ring
      _ = (1 + xi⁻¹ ^ 2 * (theta xi)⁻¹) *
          (1 + (theta xi)⁻¹ ^ 2 * (theta (theta xi))⁻¹) := by
            rw [hbase, hbaseTheta]
  rw [hmuNorm] at hprod
  have hthetaXi : theta xi ≠ 0 := (map_ne_zero theta).mpr hxi
  have hthetaThetaXi : theta (theta xi) ≠ 0 :=
    (map_ne_zero theta).mpr hthetaXi
  field_simp [hxi, hthetaXi, hthetaThetaXi] at hprod
  ring_nf at hprod
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero] at hprod
  have hreduced :
      xi ^ 2 * theta xi ^ 2 + theta xi * theta (theta xi) =
        xi ^ 2 * theta xi + theta xi ^ 2 * theta (theta xi) := by
    calc
      xi ^ 2 * theta xi ^ 2 + theta xi * theta (theta xi) =
          (1 + xi ^ 2 * theta xi ^ 2 +
              xi ^ 2 * theta xi ^ 3 * theta (theta xi) +
                theta xi * theta (theta xi)) -
            (1 + xi ^ 2 * theta xi ^ 3 * theta (theta xi)) := by ring
      _ = (1 + xi ^ 2 * theta xi +
              xi ^ 2 * theta xi ^ 3 * theta (theta xi) +
                theta xi ^ 2 * theta (theta xi)) -
            (1 + xi ^ 2 * theta xi ^ 3 * theta (theta xi)) := by
              rw [hprod]
      _ = xi ^ 2 * theta xi +
          theta xi ^ 2 * theta (theta xi) := by ring
  have hfactored :
      theta xi * (1 + theta xi) *
        (xi ^ 2 + theta (theta xi)) = 0 := by
    calc
      theta xi * (1 + theta xi) *
          (xi ^ 2 + theta (theta xi)) =
        (xi ^ 2 * theta xi ^ 2 + theta xi * theta (theta xi)) +
          (xi ^ 2 * theta xi +
            theta xi ^ 2 * theta (theta xi)) := by ring
      _ = 0 := by rw [hreduced, CharTwo.add_self_eq_zero]
  have hsum : theta (theta xi) + xi ^ 2 = 0 := by
    simpa only [add_comm] using (mul_eq_zero.mp hfactored).resolve_left
      (mul_ne_zero hthetaXi (by
        intro h
        apply hthetaXiOne
        exact ((eq_neg_of_add_eq_zero_left h).trans
          (CharTwo.neg_eq (theta xi))).symm))
  exact (eq_neg_of_add_eq_zero_left hsum).trans (CharTwo.neg_eq (xi ^ 2))

set_option maxHeartbeats 800000 in
private theorem xi1115_theta_relation_transfer
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (hnormInjective : Function.Injective (fun x : K => x * theta x))
    (a xi : K) (ha : a ≠ 0) (hxi : xi ≠ 0)
    (hxiCoordinate :
      theta xi = (1 + a * theta.symm a)⁻¹)
    (hxiRelation : theta (theta xi) = xi ^ 2) :
    theta (theta a) = a ^ 2 := by
  let t : K := theta.symm a
  have ht : t ≠ 0 := (map_ne_zero theta.symm).mpr ha
  have hthetaT : theta t = a := by simp [t]
  have hcoordinateInv :
      1 + a * t = (theta xi)⁻¹ := by
    have h := congrArg Inv.inv hxiCoordinate
    simpa [t] using h.symm
  have hat : a * t = 1 + (theta xi)⁻¹ := by
    calc
      a * t = 0 + a * t := (zero_add _).symm
      _ = (1 + 1) + a * t := by rw [CharTwo.add_self_eq_zero]
      _ = 1 + (1 + a * t) := by ring
      _ = 1 + (theta xi)⁻¹ := by rw [hcoordinateInv]
  have hthetaHat := congrArg theta hat
  simp only [map_mul, map_add, map_one, map_inv₀, hthetaT,
    hxiRelation] at hthetaHat
  have hfirst : theta a * a = (1 + xi⁻¹) ^ 2 := by
    calc
      theta a * a = 1 + (xi ^ 2)⁻¹ := hthetaHat
      _ = (1 + xi⁻¹) ^ 2 := by
        field_simp [hxi]
        ring_nf
        simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have hsecond := congrArg theta hfirst
  simp only [map_mul, map_add, map_one, map_inv₀, map_pow] at hsecond
  have hproduct :
      theta (theta a) * theta a = a ^ 2 * t ^ 2 := by
    calc
      theta (theta a) * theta a = (1 + (theta xi)⁻¹) ^ 2 := hsecond
      _ = (a * t) ^ 2 := (congrArg (fun z : K => z ^ 2) hat).symm
      _ = a ^ 2 * t ^ 2 := by ring
  have hnormInvInjective :
      Function.Injective (fun x : K => x * theta.symm x) := by
    intro x y hxy
    apply hnormInjective
    have h := congrArg theta hxy
    simpa only [map_mul, theta.apply_symm_apply, mul_comm] using h
  let c : K := theta (theta a) / a ^ 2
  have hcNorm : c * theta.symm c = 1 := by
    calc
      c * theta.symm c =
          (theta (theta a) * theta a) /
            (a ^ 2 * t ^ 2) := by
              simp only [c, map_div₀, map_pow, theta.symm_apply_apply, t]
              ring
      _ = 1 := by
        rw [hproduct]
        exact div_self (mul_ne_zero (pow_ne_zero 2 ha) (pow_ne_zero 2 ht))
  have hcOne : c = 1 := by
    apply hnormInvInjective
    simpa using hcNorm
  exact (div_eq_one_iff_eq (pow_ne_zero 2 ha)).mp hcOne

set_option maxHeartbeats 800000 in
private theorem xi1115_theta_exceptional_core
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (hnormInjective : Function.Injective (fun x : K => x * theta x))
    (a xi : K) (ha : a ≠ 0) (hxi : xi ≠ 0)
    (hxiCoordinate :
      theta xi = (1 + a * theta.symm a)⁻¹)
    (hexceptional :
      1 + (theta xi)⁻¹ + xi⁻¹ * (theta xi)⁻¹ = 0) :
    theta (theta a) = xi⁻¹ ∧
      theta (theta (theta a)) = a ∧
        xi⁻¹ = (1 + a) / a := by
  let t : K := theta.symm a
  have ht : t ≠ 0 := (map_ne_zero theta.symm).mpr ha
  have hthetaT : theta t = a := by simp [t]
  have hthetaXi : theta xi ≠ 0 := (map_ne_zero theta).mpr hxi
  have hthetaXiFormula : theta xi = 1 + xi⁻¹ := by
    have hpoly := hexceptional
    field_simp [hxi, hthetaXi] at hpoly
    simp only [add_mul, one_mul, mul_zero] at hpoly
    have hmul : theta xi * xi = xi + 1 := by
      have hzero : theta xi * xi + (xi + 1) = 0 := by
        simpa only [add_assoc] using hpoly
      exact (eq_neg_of_add_eq_zero_left hzero).trans
        (CharTwo.neg_eq (xi + 1))
    calc
      theta xi = (xi + 1) / xi := (eq_div_iff hxi).2 hmul
      _ = 1 + xi⁻¹ := by field_simp [hxi]
  have hxiPlus : 1 + xi ≠ 0 := by
    intro h
    have hxiOne : xi = 1 :=
      ((eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq xi)).symm
    subst xi
    simp only [map_one, inv_one, CharTwo.add_self_eq_zero] at hthetaXiFormula
    exact one_ne_zero hthetaXiFormula
  have hxiPlusComm : xi + 1 ≠ 0 := by simpa [add_comm] using hxiPlus
  have hcoordinateInv :
      1 + a * t = (theta xi)⁻¹ := by
    have h := congrArg Inv.inv hxiCoordinate
    simpa [t] using h.symm
  have hat : a * t = 1 + (theta xi)⁻¹ := by
    calc
      a * t = 0 + a * t := (zero_add _).symm
      _ = (1 + 1) + a * t := by rw [CharTwo.add_self_eq_zero]
      _ = 1 + (1 + a * t) := by ring
      _ = 1 + (theta xi)⁻¹ := by rw [hcoordinateInv]
  have hnormValues : a * t = xi⁻¹ * (theta xi)⁻¹ := by
    calc
      a * t = 1 + (theta xi)⁻¹ := hat
      _ = -(xi⁻¹ * (theta xi)⁻¹) :=
        eq_neg_of_add_eq_zero_left hexceptional
      _ = xi⁻¹ * (theta xi)⁻¹ := CharTwo.neg_eq _
  have htXi : t = xi⁻¹ := by
    apply hnormInjective
    simpa only [hthetaT, map_inv₀, mul_comm] using hnormValues
  have haThetaXiInv : a = (theta xi)⁻¹ := by
    have h := congrArg theta htXi
    simpa only [hthetaT, map_inv₀] using h
  have haFormula : a = (1 + xi⁻¹)⁻¹ := by
    rw [haThetaXiInv, hthetaXiFormula]
  have hthetaA : theta a = 1 + xi := by
    have h := congrArg theta haFormula
    simp only [map_inv₀, map_add, map_one, map_inv₀] at h
    calc
      theta a = (1 + (theta xi)⁻¹)⁻¹ := h
      _ = 1 + xi := by
        rw [hthetaXiFormula]
        field_simp [hxi, hxiPlus, hxiPlusComm]
        ring_nf
        simp only [CharTwo.two_eq_zero, mul_zero, add_zero, inv_one, mul_one]
        exact add_comm xi 1
  have hthetaThetaA : theta (theta a) = xi⁻¹ := by
    have h := congrArg theta hthetaA
    simp only [map_add, map_one] at h
    calc
      theta (theta a) = 1 + theta xi := h
      _ = xi⁻¹ := by
        rw [hthetaXiFormula]
        calc
          1 + (1 + xi⁻¹) = (1 + 1) + xi⁻¹ := by abel
          _ = xi⁻¹ := by rw [CharTwo.add_self_eq_zero, zero_add]
  have hthetaCubeA : theta (theta (theta a)) = a := by
    have h := congrArg theta hthetaThetaA
    simpa only [map_inv₀, haThetaXiInv] using h
  refine ⟨hthetaThetaA, hthetaCubeA, ?_⟩
  have haXi : a * (1 + xi) = xi := by
    rw [haFormula]
    field_simp [hxi, hxiPlus, hxiPlusComm]
    ring_nf
  have hsolve : xi * (1 + a) = a := by
    calc
      xi * (1 + a) = xi + xi * a := by rw [mul_add, mul_one]
      _ = (a + a * xi) + xi * a := by
        rw [mul_add, mul_one] at haXi
        exact congrArg (fun z : K => z + xi * a) haXi.symm
      _ = a := by
        rw [mul_comm xi a, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  apply (eq_div_iff ha).2
  calc
    xi⁻¹ * a = xi⁻¹ * (xi * (1 + a)) := by rw [hsolve]
    _ = (xi⁻¹ * xi) * (1 + a) := by ring
    _ = 1 + a := by rw [inv_mul_cancel₀ hxi, one_mul]

private theorem xi1115_theta_xi_ne_one_of_coordinate
    {K : Type*} [Field K]
    (theta : K ≃+* K) (a xi : K) (ha : a ≠ 0)
    (hxiCoordinate :
      theta xi = (1 + a * theta.symm a)⁻¹) :
    theta xi ≠ 1 := by
  intro hthetaXi
  rw [hthetaXi] at hxiCoordinate
  have h := congrArg Inv.inv hxiCoordinate
  simp only [inv_one, inv_inv] at h
  have hprod : a * theta.symm a = 0 := by
    apply add_left_cancel (a := (1 : K))
    simpa using h.symm
  exact (mul_ne_zero ha ((map_ne_zero theta.symm).mpr ha)) hprod

private theorem xi1115_theta_two_exceptional_quadratic
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K) (a : K)
    (ha : a ≠ 0) (ha1 : a ≠ 1)
    (haExc : theta (theta a) = (1 + a) / a)
    (hbExc :
      theta (theta (a + 1)) = (1 + (a + 1)) / (a + 1)) :
    a ^ 2 + a + 1 = 0 := by
  have hb : a + 1 ≠ 0 := by
    intro h
    have haEq : a = 1 := by
      apply add_right_cancel (b := (1 : K))
      simp only [h, CharTwo.add_self_eq_zero]
    exact ha1 haEq
  have hthetaAdd :
      theta (theta (a + 1)) = theta (theta a) + 1 := by
    simp only [map_add, map_one]
  rw [haExc, hbExc] at hthetaAdd
  field_simp [ha, hb] at hthetaAdd
  ring_nf at hthetaAdd
  have htwo : (2 : K) = 0 := CharTwo.two_eq_zero
  have hthree : (3 : K) = 1 := by
    calc
      (3 : K) = 2 + 1 := by norm_num
      _ = 0 + 1 := by rw [htwo]
      _ = 1 := zero_add 1
  have hquad : a ^ 2 = 1 + a := by
    simpa only [htwo, hthree, mul_zero, mul_one, zero_add, add_zero] using hthetaAdd
  rw [hquad]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, zero_add]

private theorem xi1115_adjoin_add_one_eq_top
    {K : Type*} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (a : K)
    (hgenerate : Algebra.adjoin (ZMod 2) ({a} : Set K) = ⊤) :
    Algebra.adjoin (ZMod 2) ({a + 1} : Set K) = ⊤ := by
  apply top_unique
  rw [← hgenerate]
  apply Algebra.adjoin_le
  intro x hx
  simp only [Set.mem_singleton_iff] at hx
  subst x
  have hsum : (a + 1) + 1 ∈ Algebra.adjoin (ZMod 2) ({a + 1} : Set K) :=
    (Algebra.adjoin (ZMod 2) ({a + 1} : Set K)).add_mem
      (Algebra.subset_adjoin (Set.mem_singleton (a + 1)))
      (Subalgebra.one_mem _)
  simpa [add_assoc, CharTwo.add_self_eq_zero, add_zero] using hsum

private theorem xi1115_quadratic_impossible_of_binary_generator
    (n : ℕ) (hn : 3 ≤ n)
    (a : PFAppendixIII.BinaryGaloisField n)
    (hgenerate :
      Algebra.adjoin (ZMod 2) ({a} : Set
        (PFAppendixIII.BinaryGaloisField n)) = ⊤)
    (hquadratic : a ^ 2 + a + 1 = 0) :
    False := by
  let K := PFAppendixIII.BinaryGaloisField n
  have haSq : a ^ 2 = a + 1 := by
    have hzero : a ^ 2 + (a + 1) = 0 := by
      simpa only [add_assoc] using hquadratic
    exact (eq_neg_of_add_eq_zero_left hzero).trans (CharTwo.neg_eq (a + 1))
  have haFourth : a ^ 4 = a := by
    calc
      a ^ 4 = (a ^ 2) ^ 2 := by ring
      _ = (a + 1) ^ 2 := by rw [haSq]
      _ = a ^ 2 + 1 := by
        ring_nf
        simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
      _ = a := by
        rw [haSq, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  let sigma : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  have hsigmaSq : sigma ^ 2 = 1 := by
    have hmaps :
        (sigma ^ 2).toAlgHom = (1 : K ≃ₐ[ZMod 2] K).toAlgHom := by
      apply AlgHom.ext_of_adjoin_eq_top hgenerate
      intro x hx
      simp only [Set.mem_singleton_iff] at hx
      subst x
      change (a ^ 2) ^ 2 = a
      calc
        (a ^ 2) ^ 2 = a ^ 4 := by ring
        _ = a := haFourth
    apply AlgEquiv.ext
    intro x
    exact DFunLike.congr_fun hmaps x
  have horderDvd : orderOf sigma ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsigmaSq
  have horder : orderOf sigma = n := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    simpa [K, PFAppendixIII.BinaryGaloisField] using
      GaloisField.finrank 2 (by omega : n ≠ 0)
  have hnDvd : n ∣ 2 := horder ▸ horderDvd
  have hnLe : n ≤ 2 := Nat.le_of_dvd (by norm_num) hnDvd
  omega

private theorem xi1115_theta_relation_of_generator
    {K : Type*} [Field K] [Algebra (ZMod 2) K]
    [Algebra.IsAlgebraic (ZMod 2) K]
    (theta : K ≃+* K) (a : K)
    (hgenerate : Algebra.adjoin (ZMod 2) ({a} : Set K) = ⊤)
    (haRelation : theta (theta a) = a ^ 2) :
    ∀ x : K, theta (theta x) = x ^ 2 := by
  let thetaAlg : K ≃ₐ[ZMod 2] K :=
    AlgEquiv.ofRingEquiv (f := theta) (fun z => by
      have hcomp :
          theta.toRingHom.comp (algebraMap (ZMod 2) K) =
            algebraMap (ZMod 2) K := Subsingleton.elim _ _
      exact DFunLike.congr_fun hcomp z)
  let sigma : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  have hthetaAlg_apply (x : K) : thetaAlg x = theta x := by
    rfl
  have hmaps :
      (thetaAlg ^ 2).toAlgHom = sigma.toAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top hgenerate
    intro x hx
    simp only [Set.mem_singleton_iff] at hx
    subst x
    change thetaAlg (thetaAlg a) = a ^ 2
    rw [hthetaAlg_apply, hthetaAlg_apply]
    exact haRelation
  intro x
  have hx := DFunLike.congr_fun hmaps x
  change thetaAlg (thetaAlg x) = x ^ 2 at hx
  rw [hthetaAlg_apply, hthetaAlg_apply] at hx
  exact hx


set_option maxHeartbeats 800000 in
/-- The field-algebra core of Huppert XI.11.14 after setting
`kappa = xi⁻¹`. -/
private theorem xi1115_theta_factor_of_coordinate_equations
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (hnormInjective : Function.Injective (fun x : K => x * theta x))
    (xi mu nu eta epsilon : K)
    (hxi : xi ≠ 0) (hmu : mu ≠ 0)
    (hmuNorm :
      mu * theta mu =
        xi⁻¹ ^ 2 * (theta xi)⁻¹ ^ 2 + xi⁻¹ * (theta xi)⁻¹)
    (hnuNorm :
      nu * theta nu = xi ^ 2 * (theta xi) ^ 2 + xi * theta xi)
    (heta : eta = (1 + xi⁻¹) * (xi + mu⁻¹))
    (hepsilon : epsilon = (1 + xi) * (xi⁻¹ + nu⁻¹))
    (hcoordinate :
      eta + eta * (theta xi)⁻¹ +
          (1 + theta eta) * theta mu =
        epsilon * (theta xi)⁻¹ ^ 2) :
    mu * (xi + (theta xi)⁻¹) *
        (1 + (theta xi)⁻¹ + xi⁻¹ * (theta xi)⁻¹) =
      (1 + xi⁻¹ ^ 2 * (theta xi)⁻¹) *
        (1 + (theta xi)⁻¹ + xi⁻¹ * (theta xi)⁻¹) := by
  have hthetaXi : theta xi ≠ 0 := (map_ne_zero theta).mpr hxi
  have hnuEq : nu = mu * xi ^ 3 := by
    apply hnormInjective
    change nu * theta nu = (mu * xi ^ 3) * theta (mu * xi ^ 3)
    rw [hnuNorm, map_mul, map_pow]
    rw [show
      mu * xi ^ 3 * (theta mu * theta xi ^ 3) =
          (mu * theta mu) * (xi ^ 3 * theta xi ^ 3) by ring,
      hmuNorm]
    field_simp [hxi, hthetaXi]
    ring_nf
  subst eta
  subst epsilon
  rw [hnuEq] at hcoordinate
  simp only [map_mul, map_add, map_one, map_inv₀] at hcoordinate
  field_simp [hxi, hmu, hthetaXi] at hcoordinate ⊢
  ring_nf at hcoordinate ⊢
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero] at hcoordinate ⊢
  have hmuNormScaled :
      xi ^ 3 * theta xi ^ 3 * mu * theta mu =
        xi ^ 3 * theta xi ^ 3 *
          (xi⁻¹ ^ 2 * (theta xi)⁻¹ ^ 2 +
            xi⁻¹ * (theta xi)⁻¹) := by
    calc
      xi ^ 3 * theta xi ^ 3 * mu * theta mu =
          xi ^ 3 * theta xi ^ 3 * (mu * theta mu) := by ring
      _ = _ := by rw [hmuNorm]
  rw [hmuNormScaled] at hcoordinate
  field_simp [hxi, hthetaXi] at hcoordinate
  ring_nf at hcoordinate
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero] at hcoordinate ⊢
  apply sub_eq_zero.mp
  rw [CharTwo.sub_eq_add]
  calc
    (xi ^ 2 * mu + xi ^ 3 * mu + xi ^ 4 * theta xi * mu +
          xi ^ 4 * theta xi ^ 2 * mu) +
        (1 + xi + xi * theta xi + xi ^ 2 * theta xi +
          xi ^ 3 * theta xi + xi ^ 3 * theta xi ^ 2) =
      (xi * theta xi + xi ^ 2 * theta xi + xi ^ 3 * theta xi +
          xi ^ 3 * theta xi ^ 2 + xi ^ 4 * theta xi * mu +
          xi ^ 4 * theta xi ^ 2 * mu) +
        (1 + xi + xi ^ 2 * mu + xi ^ 3 * mu) := by ring
    _ = (1 + xi + xi ^ 2 * mu + xi ^ 3 * mu) +
        (1 + xi + xi ^ 2 * mu + xi ^ 3 * mu) := by rw [hcoordinate]
    _ = 0 := CharTwo.add_self_eq_zero _

set_option maxHeartbeats 800000 in
private theorem xi1115_theta_relation_from_generator_and_translate
    (n : ℕ) (hn : 3 ≤ n)
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (hnormInjective : Function.Injective (fun x => x * theta x))
    (a : PFAppendixIII.BinaryGaloisField n)
    (hgenerate : Algebra.adjoin (ZMod 2) ({a} : Set
      (PFAppendixIII.BinaryGaloisField n)) = ⊤)
    (ha : a ≠ 0) (haOne : a ≠ 1)
    (hdataA : AlignedThetaCoordinateData theta a)
    (hdataB : AlignedThetaCoordinateData theta (a + 1)) :
    ∀ x, theta (theta x) = x ^ 2 := by
  simp only [AlignedThetaCoordinateData] at hdataA hdataB
  obtain ⟨xiA, muA, nuA, etaA, epsilonA, hxiA, hmuA, _hnuA,
      hxiCoordinateA, hmuNormA, hnuNormA, hetaA, hepsilonA,
      hcoordinateA⟩ := hdataA
  obtain ⟨xiB, muB, nuB, etaB, epsilonB, hxiB, hmuB, _hnuB,
      hxiCoordinateB, hmuNormB, hnuNormB, hetaB, hepsilonB,
      hcoordinateB⟩ := hdataB
  have hfactorA := xi1115_theta_factor_of_coordinate_equations theta
    hnormInjective xiA muA nuA etaA epsilonA hxiA hmuA hmuNormA
      hnuNormA hetaA hepsilonA hcoordinateA
  have hfactorB := xi1115_theta_factor_of_coordinate_equations theta
    hnormInjective xiB muB nuB etaB epsilonB hxiB hmuB hmuNormB
      hnuNormB hetaB hepsilonB hcoordinateB
  let exceptionalA : Prop :=
    1 + (theta xiA)⁻¹ + xiA⁻¹ * (theta xiA)⁻¹ = 0
  by_cases hExcA : exceptionalA
  · have haExceptional : theta (theta a) = (1 + a) / a := by
      exact (xi1115_theta_exceptional_core theta hnormInjective a xiA ha
        hxiA hxiCoordinateA hExcA).1.trans
          (xi1115_theta_exceptional_core theta hnormInjective a xiA ha
            hxiA hxiCoordinateA hExcA).2.2
    let exceptionalB : Prop :=
      1 + (theta xiB)⁻¹ + xiB⁻¹ * (theta xiB)⁻¹ = 0
    by_cases hExcB : exceptionalB
    · have hbNe : a + 1 ≠ 0 := by
        intro h
        apply haOne
        exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq (1 : _))
      have hbExceptional :
          theta (theta (a + 1)) = (1 + (a + 1)) / (a + 1) := by
        exact (xi1115_theta_exceptional_core theta hnormInjective (a + 1)
          xiB hbNe hxiB hxiCoordinateB hExcB).1.trans
            (xi1115_theta_exceptional_core theta hnormInjective (a + 1)
              xiB hbNe hxiB hxiCoordinateB hExcB).2.2
      exact False.elim (xi1115_quadratic_impossible_of_binary_generator n hn a
        hgenerate (xi1115_theta_two_exceptional_quadratic theta a ha haOne
          haExceptional hbExceptional))
    · have hbNe : a + 1 ≠ 0 := by
        intro h
        apply haOne
        exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq (1 : _))
      have hbXiRelation := xi1115_theta_factor_nonexceptional theta xiB
        muB hxiB
        (xi1115_theta_xi_ne_one_of_coordinate theta (a + 1) xiB hbNe
          hxiCoordinateB)
        hmuNormB hfactorB hExcB
      have hbRelation := xi1115_theta_relation_transfer theta hnormInjective
        (a + 1) xiB hbNe hxiB hxiCoordinateB hbXiRelation
      exact xi1115_theta_relation_of_generator theta (a + 1)
        (xi1115_adjoin_add_one_eq_top a hgenerate) hbRelation
  · have haXiRelation := xi1115_theta_factor_nonexceptional theta xiA
      muA hxiA
      (xi1115_theta_xi_ne_one_of_coordinate theta a xiA ha hxiCoordinateA)
      hmuNormA hfactorA hExcA
    have haRelation := xi1115_theta_relation_transfer theta hnormInjective a
      xiA ha hxiA hxiCoordinateA haXiRelation
    exact xi1115_theta_relation_of_generator theta a hgenerate haRelation

set_option maxHeartbeats 800000 in
private theorem xi1115_exists_binary_generator_ne_zero_one
    (n : ℕ) (hn : 3 ≤ n) :
    ∃ a : PFAppendixIII.BinaryGaloisField n,
      Algebra.adjoin (ZMod 2) ({a} : Set
        (PFAppendixIII.BinaryGaloisField n)) = ⊤ ∧
      a ≠ 0 ∧ a ≠ 1 := by
  classical
  let K := PFAppendixIII.BinaryGaloisField n
  letI : Fintype K := Fintype.ofFinite K
  obtain ⟨agen, hagen⟩ := IsCyclic.exists_generator (α := Kˣ)
  let a : K := agen
  have ha : a ≠ 0 := agen.ne_zero
  have hgenerateIF :
      IntermediateField.adjoin (ZMod 2) ({a} : Set K) = ⊤ := by
    rw [eq_top_iff]
    intro x _hx
    by_cases hx : x = 0
    · rw [hx]
      exact (IntermediateField.adjoin (ZMod 2) ({a} : Set K)).zero_mem
    · obtain ⟨z, hz⟩ := Set.mem_range.mp (hagen (Units.mk0 x hx))
      rw [show x = (agen : K) ^ z by
        norm_cast
        rw [hz, Units.val_mk0]]
      exact zpow_mem
        (IntermediateField.mem_adjoin_simple_self (ZMod 2) a) z
  have hgenerate : Algebra.adjoin (ZMod 2) ({a} : Set K) = ⊤ :=
    Algebra.adjoin_eq_top_of_primitive_element
      (Algebra.IsAlgebraic.isAlgebraic a) hgenerateIF
  have horder : orderOf agen = Nat.card Kˣ :=
    orderOf_eq_card_of_forall_mem_zpowers hagen
  have hcardUnits : Nat.card Kˣ = 2 ^ n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units]
    have hcardK : Fintype.card K = 2 ^ n := by
      simpa [K, PFAppendixIII.BinaryGaloisField,
        ← Nat.card_eq_fintype_card] using
        GaloisField.card 2 n (by omega)
    rw [hcardK]
  have haOne : a ≠ 1 := by
    intro haOne
    have hagenOne : agen = 1 := Units.ext haOne
    rw [hagenOne, orderOf_one, hcardUnits] at horder
    have hpow : 2 ^ 3 ≤ 2 ^ n := pow_le_pow_right' (by omega) hn
    norm_num at hpow
    omega
  exact ⟨a, hgenerate, ha, haOne⟩

private theorem xi1115_root_embedding_of_standard_coordinates
    {P : Type*} [Group P]
    (m : ℕ) (hm : 0 < m)
    (pi : PFAppendixIII.BinaryGaloisField (2 * m + 1) ≃+*
      PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (hpi_sq : ∀ x, pi (pi x) = x ^ 2)
    (pair : PFAppendixIII.BinaryGaloisField (2 * m + 1) →
      PFAppendixIII.BinaryGaloisField (2 * m + 1) → P)
    (hone : pair 0 0 = 1)
    (hsurj : ∀ x : P, ∃ a z, x = pair a z)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w =
        pair (a + b) (z + w + a * pi b)) :
    ∃ phi : P →* SuzukiMatrixGroup m,
      Function.Injective phi ∧
        ∀ a z,
          ((phi (pair a z) : SuzukiMatrixGroup m) :
            GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
              SuzukiRootGL m a z := by
  classical
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  rcases huppert_blackburn_XI_3_1 m hm pi hpi_sq with
    ⟨_, _, _, _, _, _, _, _, hrootMul, _, _, _, _, _, _⟩
  have hrootMem (a z : K) :
      SuzukiRootGL m a z ∈ SuzukiMatrixGroup m := by
    exact Subgroup.subset_closure (Or.inl ⟨a, z, rfl⟩)
  let pairFun : K × K → P := fun az => pair az.1 az.2
  have hpairBijective : Function.Bijective pairFun := by
    constructor
    · intro az bw hab
      exact Prod.ext (hinj az.1 az.2 bw.1 bw.2 hab).1
        (hinj az.1 az.2 bw.1 bw.2 hab).2
    · intro x
      obtain ⟨a, z, hx⟩ := hsurj x
      exact ⟨(a, z), hx.symm⟩
  let pairEquiv : K × K ≃ P := Equiv.ofBijective pairFun hpairBijective
  let phi : P →* SuzukiMatrixGroup m :=
    { toFun := fun x =>
        ⟨SuzukiRootGL m (pairEquiv.symm x).1 (pairEquiv.symm x).2,
          hrootMem (pairEquiv.symm x).1 (pairEquiv.symm x).2⟩
      map_one' := by
        apply Subtype.ext
        have hcoord : pairEquiv.symm 1 = (0, 0) := by
          apply pairEquiv.injective
          rw [Equiv.apply_symm_apply]
          change 1 = pair 0 0
          exact hone.symm
        rw [hcoord]
        exact suzukiRootGL_zero_zero m
      map_mul' := by
        intro x y
        obtain ⟨az, rfl⟩ := pairEquiv.surjective x
        obtain ⟨bw, rfl⟩ := pairEquiv.surjective y
        rcases az with ⟨a, z⟩
        rcases bw with ⟨b, w⟩
        apply Subtype.ext
        have hcoord :
            pairEquiv.symm (pairEquiv (a, z) * pairEquiv (b, w)) =
              (a + b, z + w + a * pi b) := by
          apply pairEquiv.injective
          rw [Equiv.apply_symm_apply]
          change pair a z * pair b w =
            pair (a + b) (z + w + a * pi b)
          exact hmul a z b w
        simp only [Equiv.symm_apply_apply]
        rw [hcoord]
        exact (hrootMul a z b w).symm }
  refine ⟨phi, ?_, ?_⟩
  · intro x y hxy
    apply pairEquiv.symm.injective
    apply Prod.ext
    · have h01 := congrArg
        (fun A : SuzukiMatrixGroup m =>
          (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 1)) hxy
      simpa [phi, SuzukiRootGL, SuzukiRootMatrix] using h01
    · have h02 := congrArg
        (fun A : SuzukiMatrixGroup m =>
          (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 0 2)) hxy
      simpa [phi, SuzukiRootGL, SuzukiRootMatrix] using h02
  · intro a z
    have hcoord : pairEquiv.symm (pair a z) = (a, z) := by
      apply pairEquiv.injective
      rw [Equiv.apply_symm_apply]
      rfl
    change SuzukiRootGL m (pairEquiv.symm (pair a z)).1
      (pairEquiv.symm (pair a z)).2 = SuzukiRootGL m a z
    rw [hcoord]


private theorem xi1115_pointStabilizer_embedding_of_compatible
    {F D H S : Type*}
    [Group F] [Group D] [Group H] [Group S]
    [Finite D] [MulDistribMulAction D F]
    (eH : F ⋊[MulDistribMulAction.toMulAut D F] D ≃* H)
    (hF2 : IsPGroup 2 F) (hDodd : Odd (Nat.card D))
    (phiF : F →* S) (phiD : D →* S)
    (hphiF : Function.Injective phiF)
    (hphiD : Function.Injective phiD)
    (hcompat : ∀ d : D, ∀ x : F,
      phiF (d • x) = phiD d * phiF x * (phiD d)⁻¹) :
    ∃ phiH : H →* S,
      Function.Injective phiH ∧
        (∀ x : F,
          phiH (eH (SemidirectProduct.inl x)) = phiF x) ∧
        ∀ d : D,
          phiH (eH (SemidirectProduct.inr d)) = phiD d := by
  have hcompat' : ∀ d : D,
      phiF.comp
          (MulDistribMulAction.toMulAut D F d).toMonoidHom =
        (MulAut.conj (phiD d)).toMonoidHom.comp phiF := by
    intro d
    ext x
    exact hcompat d x
  let psi : F ⋊[MulDistribMulAction.toMulAut D F] D →* S :=
    SemidirectProduct.lift phiF phiD hcompat'
  have hpsiKer : ∀ z, psi z = 1 → z = 1 := by
    intro z hz
    have hzprod : phiF z.left * phiD z.right = 1 := by
      rw [← SemidirectProduct.inl_left_mul_inr_right z, map_mul,
        SemidirectProduct.lift_inl, SemidirectProduct.lift_inr] at hz
      exact hz
    have heq : phiF z.left = (phiD z.right)⁻¹ :=
      eq_inv_of_mul_eq_one_left hzprod
    have hrightOdd : Odd (orderOf z.right) :=
      Odd.of_dvd_nat hDodd (orderOf_dvd_natCard z.right)
    have hord : orderOf z.left = orderOf z.right := by
      calc
        orderOf z.left = orderOf (phiF z.left) :=
          (orderOf_injective phiF hphiF z.left).symm
        _ = orderOf ((phiD z.right)⁻¹) := congrArg orderOf heq
        _ = orderOf (phiD z.right) := orderOf_inv _
        _ = orderOf z.right := orderOf_injective phiD hphiD z.right
    have hcop : (orderOf z.left).Coprime (orderOf z.right) :=
      hF2.orderOf_coprime hrightOdd.coprime_two_left z.left
    have hself : (orderOf z.left).Coprime (orderOf z.left) := by
      simpa [hord] using hcop
    have hleftOrder : orderOf z.left = 1 :=
      (Nat.coprime_self _).mp hself
    have hleft : z.left = 1 := orderOf_eq_one_iff.mp hleftOrder
    have hright : z.right = 1 := by
      apply orderOf_eq_one_iff.mp
      rw [← hord, hleftOrder]
    apply SemidirectProduct.ext <;> simp [hleft, hright]
  have hpsi : Function.Injective psi := by
    intro x y hxy
    apply eq_of_mul_inv_eq_one
    apply hpsiKer
    rw [map_mul, map_inv, hxy, mul_inv_cancel]
  let phiH : H →* S := psi.comp eH.symm.toMonoidHom
  refine ⟨phiH, hpsi.comp eH.symm.injective, ?_, ?_⟩
  · intro x
    simp [phiH, psi]
  · intro d
    simp [phiH, psi]

private theorem xi1115_suzukiMatrixGroup_card_formula
    (m : ℕ) (hm : 0 < m) :
    Nat.card (SuzukiMatrixGroup m) =
      ((2 ^ (2 * m + 1)) ^ 2 + 1) *
        (2 ^ (2 * m + 1)) ^ 2 *
          (2 ^ (2 * m + 1) - 1) := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let pi : K ≃+* K := iterateFrobeniusEquiv K 2 (m + 1)
  have hpi : ∀ x : K, pi x = x ^ (2 ^ (m + 1)) := by
    intro x
    exact iterateFrobeniusEquiv_def K 2 (m + 1) x
  rcases huppert_blackburn_XI_3_3 m hm pi hpi with
    ⟨_, _, _, _, _, _, hcard, _⟩
  exact hcard

private theorem xi1115_suzukiTorusGL_mul
    (m : ℕ)
    (x y : (PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ) :
    SuzukiTorusGL m x * SuzukiTorusGL m y =
      SuzukiTorusGL m (x * y) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SuzukiTorusGL, SuzukiTorusMatrix, Matrix.mul_apply,
      Fin.sum_univ_four, mul_pow, mul_comm]

private theorem xi1115_suzukiTorusGL_injective (m : ℕ) :
    Function.Injective (SuzukiTorusGL m) := by
  intro x y hxy
  apply Units.ext
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let frob : K ≃+* K := iterateFrobeniusEquiv K 2 m
  apply frob.injective
  have h11 := congrArg
    (fun A : GL (Fin 4) K =>
      (((A : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) 1 1)) hxy
  have hpow : (x : K) ^ 2 ^ m = (y : K) ^ 2 ^ m := by
    simpa [SuzukiTorusGL, SuzukiTorusMatrix] using h11
  have hfrob : frob (x : K) = frob (y : K) := by
    calc
      frob (x : K) = (x : K) ^ 2 ^ m := by
        simpa [frob] using (iterateFrobeniusEquiv_def (R := K) (p := 2) (n := m) (x : K))
      _ = (y : K) ^ 2 ^ m := hpow
      _ = frob (y : K) := by
        simpa [frob] using (iterateFrobeniusEquiv_def (R := K) (p := 2) (n := m) (y : K)).symm
  exact hfrob
private theorem xi1115_nonsplit_centralizer_numeric_impossible
    (aCard cCard rCard dCard l r e : ℕ)
    (hl : 0 < l)
    (hAcard : aCard = 2 ^ l + 1)
    (hDcard : dCard = 2 ^ l - 1)
    (hCcardPow : cCard = aCard ^ r)
    (hRcard : rCard = 2 ^ e)
    (hCClassCount : (cCard - 1) * 2 = rCard * 2 ^ l)
    (hAcardLtC : aCard < cCard)
    (hAprime : Nat.Prime aCard)
    (hDoneLt : 1 < dCard) : False := by
  have hrTwo : 2 ≤ r := by
    by_contra hr
    have hrlt : r < 2 := Nat.lt_of_not_ge hr
    interval_cases r
    · simp at hCcardPow
      omega
    · simp at hCcardPow
      omega
  have hAodd : Odd aCard := by
    apply hAprime.odd_of_ne_two
    intro htwo
    rw [hAcard] at htwo
    have hpowTwo : 2 ≤ 2 ^ l := by
      have : 1 < 2 ^ l :=
        Nat.one_lt_pow hl.ne' (by norm_num : 1 < (2 : ℕ))
      omega
    omega
  have hPowerSub : aCard ^ r - 1 = 2 ^ (e + l - 1) := by
    have hCountPow :
        (aCard ^ r - 1) * 2 = 2 ^ (e + l - 1) * 2 := by
      calc
        (aCard ^ r - 1) * 2 = (cCard - 1) * 2 := by rw [hCcardPow]
        _ = rCard * 2 ^ l := hCClassCount
        _ = 2 ^ e * 2 ^ l := by rw [hRcard]
        _ = 2 ^ (e + l) := by rw [pow_add]
        _ = 2 ^ (e + l - 1) * 2 := by
          have hel : 1 ≤ e + l := by omega
          exact congrArg (fun k : ℕ => 2 ^ k)
            (Nat.sub_add_cancel hel).symm |>.trans (pow_succ 2 (e + l - 1))
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 2) hCountPow
  have odd_dvd_two_pow_eq_one :
      ∀ {d k : ℕ}, Odd d → d ∣ 2 ^ k → d = 1 := by
    intro d k hd hdiv
    obtain ⟨m, hm, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdiv
    cases m with
    | zero => simp
    | succ m =>
        exact False.elim
          (hd.not_two_dvd_nat (dvd_pow_self 2 (Nat.succ_ne_zero m)))
  have odd_geom_sum_of_odd :
      ∀ {x k : ℕ}, Odd x → Odd k →
        Odd (∑ i ∈ Finset.range k, x ^ i) := by
    intro x k hx hk
    rw [Finset.odd_sum_iff_odd_card_odd]
    simpa [hx.pow] using hk
  have hrEven : Even r := by
    rcases Nat.even_or_odd r with hrEven | hrOdd
    · exact hrEven
    · exfalso
      let S := ∑ i ∈ Finset.range r, aCard ^ i
      have hSodd : Odd S := odd_geom_sum_of_odd hAodd hrOdd
      have hGeom : S * (aCard - 1) = aCard ^ r - 1 := by
        simpa [S] using geom_sum_mul_of_one_le hAprime.one_le r
      have hSdvd : S ∣ 2 ^ (e + l - 1) := by
        refine ⟨aCard - 1, ?_⟩
        exact (hGeom.trans hPowerSub).symm
      have hSone : S = 1 := odd_dvd_two_pow_eq_one hSodd hSdvd
      have hPowSelf : aCard ^ r = aCard := by
        rw [hSone, one_mul] at hGeom
        exact Nat.sub_one_cancel
          (Nat.pow_pos hAprime.pos) hAprime.pos hGeom.symm
      have hrOne : r = 1 :=
        (Nat.pow_eq_self_iff hAprime.one_lt).mp hPowSelf
      omega
  obtain ⟨c, hc⟩ := hrEven
  have hcpos : 0 < c := by omega
  let y := aCard ^ c
  have hyodd : Odd y := hAodd.pow
  have hypos : 0 < y := Nat.pow_pos hAprime.pos
  have hFactor : (y - 1) * (y + 1) = 2 ^ (e + l - 1) := by
    calc
      (y - 1) * (y + 1) = y * y - 1 := by
        rw [mul_comm]
        exact (mul_self_tsub_one y).symm
      _ = y ^ 2 - 1 := by rw [pow_two]
      _ = aCard ^ r - 1 := by simp [y, hc, pow_two, pow_add]
      _ = 2 ^ (e + l - 1) := hPowerSub
  have hyThree : y = 3 := by
    have hLeftDvd : y - 1 ∣ 2 ^ (e + l - 1) :=
      ⟨y + 1, hFactor.symm⟩
    have hRightDvd : y + 1 ∣ 2 ^ (e + l - 1) :=
      ⟨y - 1, by simpa [mul_comm] using hFactor.symm⟩
    obtain ⟨u, huBound, hu⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp hLeftDvd
    obtain ⟨v, hvBound, hv⟩ :=
      (Nat.dvd_prime_pow Nat.prime_two).mp hRightDvd
    have huZero : u ≠ 0 := by
      intro hu0
      rw [hu0, pow_zero] at hu
      rcases hyodd with ⟨z, hz⟩
      omega
    have huv : u ≤ v := by
      apply (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp
      rw [← hu, ← hv]
      omega
    have hPowDvd : 2 ^ u ∣ 2 ^ v := Nat.pow_dvd_pow 2 huv
    have hTwoDvd : 2 ^ u ∣ 2 := by
      have hPlus : 2 ^ u ∣ y + 1 := by simpa [hv] using hPowDvd
      have hMinus : 2 ^ u ∣ y - 1 := by simp [hu]
      convert Nat.dvd_sub hPlus hMinus using 1
      omega
    have hPowTwo : 2 ^ u = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hTwoDvd with hOne | hTwo
      · have hu0 : u = 0 := by simpa using Nat.pow_eq_one.mp hOne
        exact False.elim (huZero hu0)
      · exact hTwo
    omega
  have hApowNine : aCard ^ r = 9 := by
    calc
      aCard ^ r = (aCard ^ c) ^ 2 := by simp [hc, pow_two, pow_add]
      _ = y ^ 2 := by rfl
      _ = 9 := by simp [hyThree]
  have hAthree : aCard = 3 := by
    apply Nat.prime_eq_prime_of_dvd_pow
      (m := 2) hAprime Nat.prime_three
    rw [show 3 ^ 2 = 9 by norm_num, ← hApowNine]
    exact dvd_pow_self aCard (by omega)
  have hDcardOne : dCard = 1 := by omega
  omega
set_option maxHeartbeats 800000 in
private theorem xi1115_torus_embedding
    {D : Type*} [Group D]
    (m : ℕ)
    (eK : D ≃* (PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ) :
    ∃ phiD : D →* SuzukiMatrixGroup m,
      Function.Injective phiD ∧
        ∀ d,
          ((phiD d : SuzukiMatrixGroup m) :
            GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
              SuzukiTorusGL m (eK d) := by
  let phiD : D →* SuzukiMatrixGroup m :=
    { toFun := fun d =>
        ⟨SuzukiTorusGL m (eK d),
          Subgroup.subset_closure (Or.inr (Or.inl ⟨eK d, rfl⟩))⟩
      map_one' := by
        apply Subtype.ext
        change SuzukiTorusGL m (eK 1) = 1
        rw [map_one, suzukiTorusGL_one]
      map_mul' := by
        intro x y
        apply Subtype.ext
        rw [map_mul]
        exact (xi1115_suzukiTorusGL_mul m (eK x) (eK y)).symm }
  refine ⟨phiD, ?_, ?_⟩
  · intro x y hxy
    apply eK.injective
    apply xi1115_suzukiTorusGL_injective m
    exact congrArg Subtype.val hxy
  · intro d
    rfl

private theorem xi1115_root_torus_compatibility
    {D P : Type*} [Group D] [Group P]
    [MulDistribMulAction D P]
    (m : ℕ) (hm : 0 < m)
    (pi : PFAppendixIII.BinaryGaloisField (2 * m + 1) ≃+*
      PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (hpiSq : ∀ x, pi (pi x) = x ^ 2)
    (pair : PFAppendixIII.BinaryGaloisField (2 * m + 1) →
      PFAppendixIII.BinaryGaloisField (2 * m + 1) → P)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ)
    (hsurj : ∀ x : P, ∃ a z, x = pair a z)
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z =
        pair ((eD d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) * a)
          ((eD d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) *
            pi (eD d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) * z))
    (phiF : P →* SuzukiMatrixGroup m)
    (phiD : D →* SuzukiMatrixGroup m)
    (hphiFSpec : ∀ a z,
      ((phiF (pair a z) : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiRootGL m a z)
    (hphiDSpec : ∀ d,
      ((phiD d : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiTorusGL m (eD d)) :
    ∀ d : D, ∀ x : P,
      phiF (d • x) = phiD d * phiF x * (phiD d)⁻¹ := by
  have hpiFormula : ∀ x,
      pi x = x ^ (2 ^ (m + 1)) :=
    (huppert_blackburn_XI_3_1 m hm pi hpiSq).2.1
  intro d x
  obtain ⟨a, z, rfl⟩ := hsurj x
  apply Subtype.ext
  change
    ((phiF (d • pair a z) : SuzukiMatrixGroup m) :
      GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
      ((phiD d : SuzukiMatrixGroup m) :
          GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) *
        ((phiF (pair a z) : SuzukiMatrixGroup m) :
          GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) *
        (((phiD d : SuzukiMatrixGroup m) :
          GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))))⁻¹
  rw [hactor, hphiFSpec, hphiDSpec, hphiFSpec]
  exact (suzukiTorusGL_conj_root m pi hpiSq hpiFormula a z (eD d)).symm

private theorem xi1115_standard_bruhat_of_coordinate_embeddings_with_weyl_spec
    {D P : Type*} [Group D] [Group P]
    (m : ℕ) (hm : 0 < m)
    (pi : PFAppendixIII.BinaryGaloisField (2 * m + 1) ≃+*
      PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (hpiSq : ∀ x, pi (pi x) = x ^ 2)
    (pair : PFAppendixIII.BinaryGaloisField (2 * m + 1) →
      PFAppendixIII.BinaryGaloisField (2 * m + 1) → P)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ)
    (hsurj : ∀ x : P, ∃ a z, x = pair a z)
    (phiF : P →* SuzukiMatrixGroup m)
    (phiD : D →* SuzukiMatrixGroup m)
    (hphiFSpec : ∀ a z,
      ((phiF (pair a z) : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiRootGL m a z)
    (hphiDSpec : ∀ d,
      ((phiD d : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiTorusGL m (eD d)) :
    let B := phiF.range ⊔ phiD.range
    ∃ wstd : SuzukiMatrixGroup m,
      ((wstd : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiWeylGL m ∧
        wstd * wstd = 1 ∧
        ∀ x : SuzukiMatrixGroup m,
          x ∈ B ∨
            ∃ h₁ h₂ : B,
              x = (h₁ : SuzukiMatrixGroup m) * wstd *
                (h₂ : SuzukiMatrixGroup m) := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  let FGL : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ a b : K, A = SuzukiRootGL m a b}
  let HGL : Subgroup (GL (Fin 4) K) :=
    Subgroup.closure {A | ∃ u : Kˣ, A = SuzukiTorusGL m u}
  let BGL : Subgroup (GL (Fin 4) K) := FGL ⊔ HGL
  let B : Subgroup (SuzukiMatrixGroup m) := phiF.range ⊔ phiD.range
  have hpiFormula : ∀ x, pi x = x ^ (2 ^ (m + 1)) :=
    (huppert_blackburn_XI_3_1 m hm pi hpiSq).2.1
  have hFGLLe : FGL ≤ SuzukiMatrixGroup m := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inl hA)
  have hHGLLe : HGL ≤ SuzukiMatrixGroup m := by
    rw [Subgroup.closure_le]
    intro A hA
    exact Subgroup.subset_closure (Or.inr (Or.inl hA))
  have hBGLLe : BGL ≤ SuzukiMatrixGroup m :=
    sup_le hFGLLe hHGLLe
  have hFmem (x : SuzukiMatrixGroup m) :
      x ∈ phiF.range ↔ (x : GL (Fin 4) K) ∈ FGL := by
    constructor
    · rintro ⟨y, rfl⟩
      obtain ⟨a, z, hy⟩ := hsurj y
      rw [hy, hphiFSpec]
      exact Subgroup.subset_closure ⟨a, z, rfl⟩
    · intro hx
      rcases (suzukiRootGL_mem_closure_iff
        m pi hpiSq hpiFormula (x : GL (Fin 4) K)).mp hx with
        ⟨a, z, hxaz⟩
      refine ⟨pair a z, ?_⟩
      apply Subtype.ext
      rw [hphiFSpec]
      exact hxaz.symm
  have hHmem (x : SuzukiMatrixGroup m) :
      x ∈ phiD.range ↔ (x : GL (Fin 4) K) ∈ HGL := by
    constructor
    · rintro ⟨d, rfl⟩
      rw [hphiDSpec]
      exact Subgroup.subset_closure ⟨eD d, rfl⟩
    · intro hx
      rcases (suzukiTorusGL_mem_closure_iff
        m (x : GL (Fin 4) K)).mp hx with ⟨u, hxu⟩
      refine ⟨eD.symm u, ?_⟩
      apply Subtype.ext
      rw [hphiDSpec, eD.apply_symm_apply]
      exact hxu.symm
  have hnormal : HGL ≤ Subgroup.normalizer FGL :=
    suzukiTorusClosure_le_normalizer_rootClosure
      m pi hpiSq hpiFormula
  have hBmem (x : SuzukiMatrixGroup m) :
      x ∈ B ↔ (x : GL (Fin 4) K) ∈ BGL := by
    constructor
    · intro hx
      have hBLe :
          B ≤ BGL.comap (SuzukiMatrixGroup m).subtype := by
        refine sup_le ?_ ?_
        · intro y hy
          exact (show FGL ≤ BGL from le_sup_left) ((hFmem y).1 hy)
        · intro y hy
          exact (show HGL ≤ BGL from le_sup_right) ((hHmem y).1 hy)
      exact hBLe hx
    · intro hx
      have hxprod :
          (x : GL (Fin 4) K) ∈
            (FGL : Set (GL (Fin 4) K)) *
              (HGL : Set (GL (Fin 4) K)) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left FGL HGL hnormal]
        exact hx
      rcases hxprod with ⟨f, hf, h, hh, hfh⟩
      let fS : SuzukiMatrixGroup m := ⟨f, hFGLLe hf⟩
      let hS : SuzukiMatrixGroup m := ⟨h, hHGLLe hh⟩
      have hxfh : x = fS * hS := by
        apply Subtype.ext
        exact hfh.symm
      rw [hxfh]
      exact B.mul_mem
        ((show phiF.range ≤ B from le_sup_left) ((hFmem fS).2 hf))
        ((show phiD.range ≤ B from le_sup_right) ((hHmem hS).2 hh))
  let wstd : SuzukiMatrixGroup m :=
    ⟨SuzukiWeylGL m,
      Subgroup.subset_closure (Or.inr (Or.inr rfl))⟩
  refine ⟨wstd, rfl, ?_, ?_⟩
  · apply Subtype.ext
    exact suzukiWeylGL_mul_self m
  · intro x
    rcases suzukiMatrixGroup_bruhat_decomposition
      m pi hpiSq hpiFormula (x : GL (Fin 4) K) x.property with
      hxB | ⟨b, f, hb, hf, hxbf⟩
    · exact Or.inl ((hBmem x).2 hxB)
    · let bS : SuzukiMatrixGroup m := ⟨b, hBGLLe hb⟩
      let fS : SuzukiMatrixGroup m := ⟨f, hFGLLe hf⟩
      let bB : B := ⟨bS, (hBmem bS).2 hb⟩
      let fB : B :=
        ⟨fS, (show phiF.range ≤ B from le_sup_left) ((hFmem fS).2 hf)⟩
      refine Or.inr ⟨bB, fB, ?_⟩
      apply Subtype.ext
      exact hxbf


set_option maxHeartbeats 800000 in
private theorem xi1115_suzukiWeyl_root_weyl_bruhat_explicit
    (m : ℕ)
    (pi : PFAppendixIII.BinaryGaloisField (2 * m + 1) ≃+*
      PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (hpiSq : ∀ x, pi (pi x) = x ^ 2)
    (hpiFormula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (a b : PFAppendixIII.BinaryGaloisField (2 * m + 1)) :
    let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
    let n : K := a * b + pi a * a ^ 2 + pi b
    ∀ hn : n ≠ 0,
      let s : K := a * pi a + b
      let c : K := n⁻¹ * s
      let d : K := n⁻¹ * a + c * pi c
      let e : K := n⁻¹ * b
      let f : K := n⁻¹ * a
      let uval : K := pi n * n⁻¹ ^ 2
      let u : Kˣ := Units.mk0 uval
        (mul_ne_zero ((map_ne_zero pi).2 hn)
          (pow_ne_zero _ (inv_ne_zero hn)))
      SuzukiWeylGL m * SuzukiRootGL m a b * SuzukiWeylGL m =
        SuzukiRootGL m c d * SuzukiTorusGL m u *
          SuzukiWeylGL m * SuzukiRootGL m e f := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  dsimp only
  let n : K := a * b + pi a * a ^ 2 + pi b
  intro hn
  let s : K := a * pi a + b
  let c : K := n⁻¹ * s
  let d : K := n⁻¹ * a + c * pi c
  let e : K := n⁻¹ * b
  let f : K := n⁻¹ * a
  let uval : K := pi n * n⁻¹ ^ 2
  have huval : uval ≠ 0 :=
    mul_ne_zero ((map_ne_zero pi).2 hn)
      (pow_ne_zero _ (inv_ne_zero hn))
  let u : Kˣ := Units.mk0 uval huval
  have hpin : pi n ≠ 0 := (map_ne_zero pi).2 hn
  have hpiUval : pi uval = (n * (pi n)⁻¹) ^ 2 := by
    dsimp only [uval]
    simp only [map_mul, map_pow, map_inv₀, hpiSq]
    ring
  have huPow : (u : K) ^ (2 ^ m) = n * (pi n)⁻¹ := by
    apply CharTwo.sq_injective
    calc
      ((u : K) ^ (2 ^ m)) ^ 2 = (u : K) ^ (2 ^ (m + 1)) := by
        rw [show 2 ^ (m + 1) = 2 ^ m * 2 by rw [pow_succ], pow_mul]
      _ = pi (u : K) := (hpiFormula (u : K)).symm
      _ = (n * (pi n)⁻¹) ^ 2 := hpiUval
  rcases suzukiWeyl_root_weyl_bruhat
      m pi hpiSq hpiFormula a b hn with
    ⟨c', d', e', f', u', hgauss⟩
  have huOuterInv :
      (((u' : K) ^ (1 + 2 ^ m))⁻¹) = n := by
    have h30 := congrArg
      (fun A : GL (Fin 4) K =>
        ((A : Matrix (Fin 4) (Fin 4) K) 3 0)) hgauss
    simp [n, SuzukiWeylGL, SuzukiWeylMatrix, SuzukiRootGL,
      SuzukiRootMatrix, SuzukiTorusGL, SuzukiTorusMatrix,
      Matrix.mul_apply, Fin.sum_univ_four, hpiFormula, pow_add] at h30 ⊢
    linear_combination h30.symm
  have h31 := congrArg
    (fun A : GL (Fin 4) K =>
      ((A : Matrix (Fin 4) (Fin 4) K) 3 1)) hgauss
  have h32 := congrArg
    (fun A : GL (Fin 4) K =>
      ((A : Matrix (Fin 4) (Fin 4) K) 3 2)) hgauss
  have h20 := congrArg
    (fun A : GL (Fin 4) K =>
      ((A : Matrix (Fin 4) (Fin 4) K) 2 0)) hgauss
  have h10 := congrArg
    (fun A : GL (Fin 4) K =>
      ((A : Matrix (Fin 4) (Fin 4) K) 1 0)) hgauss
  have h21 := congrArg
    (fun A : GL (Fin 4) K =>
      ((A : Matrix (Fin 4) (Fin 4) K) 2 1)) hgauss
  simp [SuzukiWeylGL, SuzukiWeylMatrix, SuzukiRootGL,
    SuzukiRootMatrix, SuzukiTorusGL, SuzukiTorusMatrix,
    Matrix.mul_apply, Fin.sum_univ_four, pow_add] at h31 h32 h20 h10 h21
  have huOuter :
      (((u' : K) ^ (2 ^ m))⁻¹) * (u' : K)⁻¹ = n := by
    simpa [pow_add] using huOuterInv
  rw [huOuter] at h31 h32 h20 h10 h21
  have he : e' = e := by
    apply mul_left_cancel₀ hn
    calc
      n * e' = b := h31.symm
      _ = n * e := by
        dsimp only [e]
        rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  have hf : f' = f := by
    apply mul_left_cancel₀ hn
    calc
      n * f' = a := h32.symm
      _ = n * f := by
        dsimp only [f]
        rw [← mul_assoc, mul_inv_cancel₀ hn, one_mul]
  have h20' : s = c' * n := by
    dsimp only [s]
    rw [hpiFormula]
    simpa [pow_succ] using h20
  have hc : c' = c := by
    apply mul_right_cancel₀ hn
    calc
      c' * n = s := h20'.symm
      _ = c * n := by
        dsimp only [c]
        calc
          s = (n⁻¹ * n) * s := by rw [inv_mul_cancel₀ hn, one_mul]
          _ = n⁻¹ * s * n := by ring
  have h10' : a = (c' * pi c' + d') * n := by
    rw [hpiFormula]
    simpa [pow_succ] using h10
  have hsum : c * pi c + d' = n⁻¹ * a := by
    apply mul_right_cancel₀ hn
    calc
      (c * pi c + d') * n = a := by simpa [hc] using h10'.symm
      _ = (n⁻¹ * a) * n := by
        calc
          a = (n⁻¹ * n) * a := by rw [inv_mul_cancel₀ hn, one_mul]
          _ = (n⁻¹ * a) * n := by ring
  have hd : d' = d := by
    dsimp only [d]
    calc
      d' = (c * pi c + c * pi c) + d' := by
        rw [CharTwo.add_self_eq_zero, zero_add]
      _ = c * pi c + (c * pi c + d') := by abel
      _ = c * pi c + n⁻¹ * a := by rw [hsum]
      _ = n⁻¹ * a + c * pi c := by abel
  have hpoly21 : s * b + pi n = pi a * n := by
    dsimp only [s, n]
    simp only [map_add, map_mul, map_pow, hpiSq]
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero _ 2
    linear_combination (b ^ 2) * htwo
  have h21' : pi a = c' * n * e' + ((u' : K) ^ (2 ^ m))⁻¹ := by
    rw [hpiFormula]
    simpa [pow_succ] using h21
  have huPrimePowInv : ((u' : K) ^ (2 ^ m))⁻¹ = pi n * n⁻¹ := by
    have hrewrite : c' * n * e' = s * n⁻¹ * b := by
      rw [hc, he]
      dsimp only [c, e]
      field_simp [hn]
    rw [hrewrite] at h21'
    have hcharTwo : (x : K) → x + x = 0 := CharTwo.add_self_eq_zero
    have hpoly21' : pi a * n + s * b = pi n := by
      calc
        pi a * n + s * b = (s * b + pi n) + s * b := by rw [hpoly21]
        _ = (s * b + s * b) + pi n := by abel
        _ = pi n := by rw [hcharTwo, zero_add]
    have hscaled : pi a + s * n⁻¹ * b = pi n * n⁻¹ := by
      apply mul_right_cancel₀ hn
      calc
        (pi a + s * n⁻¹ * b) * n =
            pi a * n + s * (n⁻¹ * n) * b := by ring
        _ = pi a * n + s * b := by rw [inv_mul_cancel₀ hn, mul_one]
        _ = pi n := hpoly21'
        _ = (pi n * n⁻¹) * n := by
          rw [mul_assoc, inv_mul_cancel₀ hn, mul_one]
    calc
      ((u' : K) ^ (2 ^ m))⁻¹ = ((u' : K) ^ (2 ^ m))⁻¹ + 0 := by rw [add_zero]
      _ = ((u' : K) ^ (2 ^ m))⁻¹ +
          (s * n⁻¹ * b + s * n⁻¹ * b) := by rw [hcharTwo]
      _ =
          (s * n⁻¹ * b + ((u' : K) ^ (2 ^ m))⁻¹) + s * n⁻¹ * b := by
            abel
      _ = pi a + s * n⁻¹ * b := by rw [← h21']
      _ = pi n * n⁻¹ := hscaled
  have huPrimePow : (u' : K) ^ (2 ^ m) = n * (pi n)⁻¹ := by
    apply inv_injective
    rw [huPrimePowInv]
    field_simp [hn, hpin]
  have hu : u' = u := by
    apply Units.ext
    let frob : K ≃+* K := iterateFrobeniusEquiv K 2 m
    apply frob.injective
    change (u' : K) ^ (2 ^ m) = (u : K) ^ (2 ^ m)
    exact huPrimePow.trans huPow.symm
  rw [hc, hd, he, hf, hu] at hgauss
  exact hgauss

private theorem xi1115_standard_suzuki_swap_formula
    {D P : Type*} [Group D] [Group P]
    (m : ℕ)
    (pi : PFAppendixIII.BinaryGaloisField (2 * m + 1) ≃+*
      PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (hpiSq : ∀ x, pi (pi x) = x ^ 2)
    (hpiFormula : ∀ x, pi x = x ^ (2 ^ (m + 1)))
    (pair : PFAppendixIII.BinaryGaloisField (2 * m + 1) →
      PFAppendixIII.BinaryGaloisField (2 * m + 1) → P)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ)
    (phiF : P →* SuzukiMatrixGroup m)
    (phiD : D →* SuzukiMatrixGroup m)
    (hphiFSpec : ∀ a z,
      ((phiF (pair a z) : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiRootGL m a z)
    (hphiDSpec : ∀ d,
      ((phiD d : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiTorusGL m (eD d))
    (wstd : SuzukiMatrixGroup m)
    (hwstd :
      ((wstd : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiWeylGL m)
    (a b : PFAppendixIII.BinaryGaloisField (2 * m + 1)) :
    let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
    let n : K := a * b + pi a * a ^ 2 + pi b
    ∀ hn : n ≠ 0,
      let s : K := a * pi a + b
      let c : K := n⁻¹ * s
      let d : K := n⁻¹ * a + c * pi c
      let e : K := n⁻¹ * b
      let f : K := n⁻¹ * a
      let uval : K := pi n * n⁻¹ ^ 2
      let u : Kˣ := Units.mk0 uval
        (mul_ne_zero ((map_ne_zero pi).2 hn)
          (pow_ne_zero _ (inv_ne_zero hn)))
      phiF (pair c d) * phiD (eD.symm u) * wstd * phiF (pair e f) =
        wstd * phiF (pair a b) * wstd := by
  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  dsimp only
  let n : K := a * b + pi a * a ^ 2 + pi b
  intro hn
  let s : K := a * pi a + b
  let c : K := n⁻¹ * s
  let d : K := n⁻¹ * a + c * pi c
  let e : K := n⁻¹ * b
  let f : K := n⁻¹ * a
  let uval : K := pi n * n⁻¹ ^ 2
  have huval : uval ≠ 0 :=
    mul_ne_zero ((map_ne_zero pi).2 hn)
      (pow_ne_zero _ (inv_ne_zero hn))
  let u : Kˣ := Units.mk0 uval huval
  apply Subtype.ext
  change
    ((phiF (pair c d) : SuzukiMatrixGroup m) : GL (Fin 4) K) *
          ((phiD (eD.symm u) : SuzukiMatrixGroup m) : GL (Fin 4) K) *
        (wstd : GL (Fin 4) K) *
      ((phiF (pair e f) : SuzukiMatrixGroup m) : GL (Fin 4) K) =
    (wstd : GL (Fin 4) K) *
        ((phiF (pair a b) : SuzukiMatrixGroup m) : GL (Fin 4) K) *
      (wstd : GL (Fin 4) K)
  rw [hphiFSpec, hphiDSpec, eD.apply_symm_apply, hwstd,
    hphiFSpec, hphiFSpec]
  exact (xi1115_suzukiWeyl_root_weyl_bruhat_explicit
    m pi hpiSq hpiFormula a b hn).symm


set_option maxHeartbeats 1200000 in
private theorem xi1115_aligned_suzuki_embedding_package
    {D P : Type*} [Group D] [Group P]
    [MulDistribMulAction D P]
    (m : ℕ) (hm : 0 < m)
    (pi : PFAppendixIII.BinaryGaloisField (2 * m + 1) ≃+*
      PFAppendixIII.BinaryGaloisField (2 * m + 1))
    (hpiSq : ∀ x, pi (pi x) = x ^ 2)
    (pair : PFAppendixIII.BinaryGaloisField (2 * m + 1) →
      PFAppendixIII.BinaryGaloisField (2 * m + 1) → P)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ)
    (hone : pair 0 0 = 1)
    (hsurj : ∀ x : P, ∃ a z, x = pair a z)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w =
        pair (a + b) (z + w + a * pi b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z =
        pair ((eD d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) * a)
          ((eD d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) *
            pi (eD d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) * z)) :
    ∃ phiF : P →* SuzukiMatrixGroup m,
      Function.Injective phiF ∧
        (∀ a z,
          ((phiF (pair a z) : SuzukiMatrixGroup m) :
            GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
              SuzukiRootGL m a z) ∧
        ∃ phiD : D →* SuzukiMatrixGroup m,
          Function.Injective phiD ∧
            (∀ d,
              ((phiD d : SuzukiMatrixGroup m) :
                GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
                  SuzukiTorusGL m (eD d)) ∧
            (∀ d : D, ∀ x : P,
              phiF (d • x) = phiD d * phiF x * (phiD d)⁻¹) ∧
            ∃ wstd : SuzukiMatrixGroup m,
              ((wstd : SuzukiMatrixGroup m) :
                GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
                  SuzukiWeylGL m ∧
                wstd * wstd = 1 ∧
                (∀ x : SuzukiMatrixGroup m,
                  x ∈ phiF.range ⊔ phiD.range ∨
                    ∃ h₁ h₂ : ↥(phiF.range ⊔ phiD.range),
                      x = (h₁ : SuzukiMatrixGroup m) * wstd *
                        (h₂ : SuzukiMatrixGroup m)) ∧
                ∀ a z : PFAppendixIII.BinaryGaloisField (2 * m + 1),
                  let n := a * z + pi a * a ^ 2 + pi z
                  ∀ hn : n ≠ 0,
                    let s := a * pi a + z
                    let c := n⁻¹ * s
                    let d := n⁻¹ * a + c * pi c
                    let e := n⁻¹ * z
                    let f := n⁻¹ * a
                    let uval := pi n * n⁻¹ ^ 2
                    let u := Units.mk0 uval
                      (mul_ne_zero ((map_ne_zero pi).2 hn)
                        (pow_ne_zero _ (inv_ne_zero hn)))
                    phiF (pair c d) * phiD (eD.symm u) * wstd *
                        phiF (pair e f) =
                      wstd * phiF (pair a z) * wstd := by
  have hpiFormula : ∀ x,
      pi x = x ^ (2 ^ (m + 1)) :=
    (huppert_blackburn_XI_3_1 m hm pi hpiSq).2.1
  rcases xi1115_root_embedding_of_standard_coordinates
      m hm pi hpiSq pair hone hsurj hinj hmul with
    ⟨phiF, hphiF, hphiFSpec⟩
  rcases xi1115_torus_embedding m eD with
    ⟨phiD, hphiD, hphiDSpec⟩
  have hcompat := xi1115_root_torus_compatibility
    m hm pi hpiSq pair eD hsurj hactor phiF phiD
      hphiFSpec hphiDSpec
  rcases xi1115_standard_bruhat_of_coordinate_embeddings_with_weyl_spec
      m hm pi hpiSq pair eD hsurj phiF phiD hphiFSpec hphiDSpec with
    ⟨wstd, hwstd, hwstdSq, hBruhat⟩
  refine ⟨phiF, hphiF, hphiFSpec, phiD, hphiD, hphiDSpec,
    hcompat, wstd, hwstd, hwstdSq, hBruhat, ?_⟩
  intro a z
  dsimp only
  intro hn
  exact xi1115_standard_suzuki_swap_formula
    m pi hpiSq hpiFormula pair eD phiF phiD hphiFSpec hphiDSpec
      wstd hwstd a z hn

private theorem xi1115_standard_weyl_torus_relation
    {D : Type*} [Group D]
    (m : ℕ)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ)
    (phiD : D →* SuzukiMatrixGroup m)
    (hphiDSpec : ∀ d,
      ((phiD d : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiTorusGL m (eD d))
    (wstd : SuzukiMatrixGroup m)
    (hwstd :
      ((wstd : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiWeylGL m) :
    ∀ d : D, wstd * phiD d = phiD d⁻¹ * wstd := by
  intro d
  apply Subtype.ext
  change
    (wstd : GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) *
        (phiD d : GL (Fin 4)
          (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
      (phiD d⁻¹ : GL (Fin 4)
          (PFAppendixIII.BinaryGaloisField (2 * m + 1))) *
        (wstd : GL (Fin 4)
          (PFAppendixIII.BinaryGaloisField (2 * m + 1)))
  rw [hwstd, hphiDSpec, hphiDSpec, map_inv]
  calc
    SuzukiWeylGL m * SuzukiTorusGL m (eD d) =
        (SuzukiWeylGL m * SuzukiTorusGL m (eD d) * SuzukiWeylGL m) *
          SuzukiWeylGL m := by
            rw [mul_assoc, suzukiWeylGL_mul_self, mul_one]
    _ = SuzukiTorusGL m (eD d)⁻¹ * SuzukiWeylGL m := by
      rw [suzukiWeylGL_conj_torus]

private theorem xi1115_standard_weyl_not_in_borel
    {F D : Type*} [Group F] [Group D] [MulDistribMulAction D F]
    (m : ℕ)
    (pair : PFAppendixIII.BinaryGaloisField (2 * m + 1) →
      PFAppendixIII.BinaryGaloisField (2 * m + 1) → F)
    (hsurj : ∀ x : F, ∃ a z, x = pair a z)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField (2 * m + 1))ˣ)
    (phiF : F →* SuzukiMatrixGroup m)
    (phiD : D →* SuzukiMatrixGroup m)
    (hcompat : ∀ d : D, ∀ x : F,
      phiF (d • x) = phiD d * phiF x * (phiD d)⁻¹)
    (hphiFSpec : ∀ a z,
      ((phiF (pair a z) : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiRootGL m a z)
    (hphiDSpec : ∀ d,
      ((phiD d : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiTorusGL m (eD d))
    (wstd : SuzukiMatrixGroup m)
    (hwstd :
      ((wstd : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) =
          SuzukiWeylGL m) :
    wstd ∉ phiF.range ⊔ phiD.range := by
  have hnormal : phiD.range ≤ Subgroup.normalizer phiF.range := by
    rintro y ⟨d, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨d • x, hcompat d x⟩
    · rintro ⟨x, hx⟩
      refine ⟨d⁻¹ • x, ?_⟩
      rw [hcompat, map_inv, inv_inv, hx]
      group
  intro hwB
  have hwProd : wstd ∈
      (phiF.range : Set (SuzukiMatrixGroup m)) *
        (phiD.range : Set (SuzukiMatrixGroup m)) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left
      phiF.range phiD.range hnormal]
    exact hwB
  rcases hwProd with ⟨f, hf, d, hd, hfd⟩
  rcases hf with ⟨x, rfl⟩
  rcases hd with ⟨y, rfl⟩
  obtain ⟨a, z, hxPair⟩ := hsurj x
  have hvalue : wstd = phiF x * phiD y := hfd.symm
  rw [hxPair] at hvalue
  have hentry := congrArg
    (fun q : SuzukiMatrixGroup m =>
      ((((q : SuzukiMatrixGroup m) :
        GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) :
          Matrix (Fin 4) (Fin 4)
            (PFAppendixIII.BinaryGaloisField (2 * m + 1))) 3 0))
    hvalue
  rw [hwstd] at hentry
  change
    (((SuzukiWeylGL m :
      GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) :
        Matrix (Fin 4) (Fin 4)
          (PFAppendixIII.BinaryGaloisField (2 * m + 1))) 3 0) =
      (((((phiF (pair a z) : SuzukiMatrixGroup m) :
          GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) *
        ((phiD y : SuzukiMatrixGroup m) :
          GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) :
            GL (Fin 4) (PFAppendixIII.BinaryGaloisField (2 * m + 1))) :
              Matrix (Fin 4) (Fin 4)
                (PFAppendixIII.BinaryGaloisField (2 * m + 1))) 3 0) at hentry
  rw [hphiFSpec, hphiDSpec] at hentry
  simp [SuzukiWeylGL, SuzukiWeylMatrix, SuzukiRootGL,
    SuzukiRootMatrix, SuzukiTorusGL, SuzukiTorusMatrix,
    Matrix.mul_apply, Fin.sum_univ_four] at hentry

private theorem xi1115_kernel_card_twoPower
    {H : Type*} [Group H] [Finite H]
    (F : Subgroup H) (hFne : F ≠ ⊥) (hF2 : IsPGroup 2 F) :
    ∃ f : ℕ, 0 < f ∧ Nat.card F = 2 ^ f := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).mpr hFne
  exact hF2.nontrivial_iff_card.mp inferInstance

private theorem xi1115_complement_card_odd
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hFnoncomm : ¬ IsMulCommutative F) :
    Odd (Nat.card D) := by
  apply Nat.not_even_iff_odd.mp
  intro hDcardEven
  apply hFnoncomm
  have htwoD : 2 ∣ Nat.card D := even_iff_two_dvd.mp hDcardEven
  obtain ⟨t, htorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := D) 2 htwoD
  have htne : t ≠ 1 := by
    intro ht
    subst t
    simp at htorder
  have htsq : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  have htsq_H : (t : H) ^ 2 = 1 := by
    simpa using congrArg Subtype.val htsq
  letI : F.Normal := hFrob.normal
  let phi : MulAut F := MulAut.conjNormal (H := F) (t : H)
  have hphi_sq : phi ^ 2 = 1 := by
    change (MulAut.conjNormal (H := F) (t : H)) ^ 2 = 1
    rw [← map_pow, htsq_H, map_one]
  have hphi_involutive : Function.Involutive phi := by
    intro x
    have hx := congrArg (fun psi : MulAut F => psi x) hphi_sq
    simpa [pow_two] using hx
  have hphi_fixedPointFree : MonoidHom.FixedPointFree phi := by
    intro x hx
    have hconj :
        (t : H) * (x : H) * (t : H)⁻¹ = (x : H) := by
      simpa [phi] using congrArg Subtype.val hx
    have hcomm : (t : H) * (x : H) = (x : H) * (t : H) := by
      calc
        (t : H) * (x : H) =
            ((t : H) * (x : H) * (t : H)⁻¹) * (t : H) := by
              simp [mul_assoc]
        _ = (x : H) * (t : H) := by rw [hconj]
    have hcent :=
      (lemma_3_1 F D
        hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob t htne
    have hxcent : (x : H) ∈ elementCentralizerIn F (t : H) :=
      ⟨x.property,
        Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    rw [hcent] at hxcent
    exact Subtype.ext (Subgroup.mem_bot.mp hxcent)
  exact ⟨⟨fun x y =>
    (hphi_fixedPointFree.commute_all_of_involutive
      hphi_involutive x y).eq⟩⟩

private theorem xi1115_actor_card_dvd_group_card_sub_one
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V]
    [MulDistribMulAction A V]
    (hfree : ∀ a : A, a ≠ 1 → ∀ v : V, a • v = v → v = 1) :
    Nat.card A ∣ Nat.card V - 1 := by
  classical
  let V0 := {v : V // v ≠ 1}
  letI : MulAction A V0 :=
    { smul := fun a v => ⟨a • (v : V), by
        intro h
        apply v.2
        have h' := congrArg (fun x : V => a⁻¹ • x) h
        simpa using h'⟩
      one_smul := by
        intro v
        apply Subtype.ext
        change (1 : A) • (v : V) = (v : V)
        simp
      mul_smul := by
        intro a b v
        apply Subtype.ext
        change (a * b) • (v : V) = a • (b • (v : V))
        rw [mul_smul] }
  have hstab : ∀ v : V0, MulAction.stabilizer A v = ⊥ := by
    intro v
    rw [eq_bot_iff]
    intro a ha
    have hav : a • v = v := by
      simpa [MulAction.mem_stabilizer_iff] using ha
    by_contra ha1
    have hane : a ≠ 1 := by
      intro h
      apply ha1
      simp [h]
    exact v.2 (hfree a hane (v : V) (congrArg Subtype.val hav))
  have hcard := Nat.card_congr (MulAction.selfEquivOrbitsQuotientProd hstab)
  have hcardV0 : Nat.card V0 = Nat.card V - 1 := by
    letI : Fintype V := Fintype.ofFinite V
    letI : Fintype V0 := Fintype.ofFinite V0
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    change Fintype.card {v : V // v ≠ 1} = Fintype.card V - 1
    simp
  rw [hcardV0, Nat.card_prod] at hcard
  exact ⟨Nat.card (Quotient (MulAction.orbitRel A V0)), by
    rw [mul_comm]
    exact hcard⟩


private theorem xi1115_complement_card_dvd_kernel_card_sub_one
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D) :
    Nat.card D ∣ Nat.card F - 1 := by
  letI : F.Normal := hFrob.normal
  letI : MulDistribMulAction D F :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D F
      (Subgroup.le_normalizer_of_normal (H := F))
  apply xi1115_actor_card_dvd_group_card_sub_one
  intro d hd f hfix
  have hconj : (d : H) * (f : H) * (d : H)⁻¹ = (f : H) := by
    simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val hfix
  have hcomm : (d : H) * (f : H) = (f : H) * (d : H) := by
    have h := congrArg (fun x : H => x * (d : H)) hconj
    simpa [mul_assoc] using h
  have hfcent : (f : H) ∈ elementCentralizerIn F (d : H) :=
    ⟨f.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
  have hcent : elementCentralizerIn F (d : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob d hd
  have hfbot : (f : H) ∈ (⊥ : Subgroup H) := by
    simpa [hcent] using hfcent
  exact Subtype.ext (by simpa using hfbot)

private theorem xi1115_action_parameters_core
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    Fintype.card Omega = Nat.card F + 1 ∧
      Nat.card (MulAction.stabilizer G a) =
        Nat.card F * Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∧
      Nat.card G = Fintype.card Omega * Nat.card F * Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∧
      Nat.card
          (MulAction.stabilizer (MulAction.stabilizer G a)
            (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∣
        Nat.card F - 1 := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change Fintype.card Omega = Nat.card F + 1 ∧
    Nat.card H = Nat.card F * Nat.card D ∧
    Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D ∧
    Nat.card D ∣ Nat.card F - 1
  have hOmegaCard : 1 < Fintype.card Omega :=
    Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
  let n := Fintype.card Omega - 1
  have hdegree : Fintype.card Omega = n + 1 := by
    dsimp [n]
    omega
  have hFcard : Nat.card F = n :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      n hdegree htwo a b hab F hFrob
  have hOmegaEq : Fintype.card Omega = Nat.card F + 1 := by
    rw [hFcard, ← hdegree]
  have hHcard : Nat.card H = Nat.card F * Nat.card D :=
    hFrob.isComplement'.card_mul_card.symm
  have hGcard : Nat.card G = Fintype.card Omega * Nat.card F * Nat.card D := by
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hindex : H.index = Fintype.card Omega := by
      calc
        H.index = Nat.card Omega := MulAction.index_stabilizer_of_transitive G a
        _ = Fintype.card Omega := Nat.card_eq_fintype_card
    have hmul := H.card_mul_index
    rw [hindex] at hmul
    calc
      Nat.card G = Nat.card H * Fintype.card Omega := hmul.symm
      _ = Fintype.card Omega * Nat.card F * Nat.card D := by
        rw [hHcard]
        ac_rfl
  have hdiv : Nat.card D ∣ Nat.card F - 1 := by
    letI : F.Normal := hFrob.normal
    letI : MulDistribMulAction D F :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer D F
        (Subgroup.le_normalizer_of_normal (H := F))
    apply xi1115_actor_card_dvd_group_card_sub_one
    intro d hd f hfix
    have hconj : (d : H) * (f : H) * (d : H)⁻¹ = (f : H) := by
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
        congrArg Subtype.val hfix
    have hcomm : (d : H) * (f : H) = (f : H) * (d : H) := by
      have h := congrArg (fun x : H => x * (d : H)) hconj
      simpa [mul_assoc] using h
    have hfcent : (f : H) ∈ elementCentralizerIn F (d : H) :=
      ⟨f.property, Subgroup.mem_centralizer_singleton_iff.mpr hcomm.symm⟩
    have hcent : elementCentralizerIn F (d : H) = ⊥ :=
      (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
        hFrob.normal hFrob.isComplement').mp hFrob d hd
    have hfbot : (f : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hfcent
    exact Subtype.ext (by simpa using hfbot)
  exact ⟨hOmegaEq, hHcard, hGcard, hdiv⟩

/-- Membership in the ambient image of a two-point stabilizer is exactly
fixing both distinguished points. -/
private theorem xi1115_twoPointStabilizer_map_mem_iff
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b) (g : G) :
    g ∈
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype ↔
      g • a = a ∧ g • b = b := by
  constructor
  · rintro ⟨h, hhD, rfl⟩
    exact ⟨h.property,
      congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hhD)⟩
  · rintro ⟨hga, hgb⟩
    let h : MulAction.stabilizer G a := ⟨g, hga⟩
    let d : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) :=
      ⟨h, by
        rw [MulAction.mem_stabilizer_iff]
        apply Subtype.ext
        exact hgb⟩
    exact ⟨d, d.property, rfl⟩

/-- An ambient normalizer element outside the two-point stabilizer
interchanges the two distinguished points. -/
private theorem xi1115_twoPointStabilizer_normalizer_notMem_swaps
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (x : G)
    (hxnorm :
      x ∈ Subgroup.normalizer
        (((MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype : Subgroup G) : Set G))
    (hxnot :
      x ∉
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype) :
    x • a = b ∧ x • b = a := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  obtain ⟨z, hz⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.complement_ne_bot
  let zg : G := ((z : H) : G)
  have hzgD : zg ∈ Dg := by
    exact ⟨(z : H), z.property, rfl⟩
  have hzgne : zg ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hzga : zg • a = a := (z : H).property
  have hzgb : zg • b = b :=
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp z.property)
  have hxconjD : x * zg * x⁻¹ ∈ Dg :=
    (Subgroup.mem_normalizer_iff.mp (by simpa [H, D, Dg] using hxnorm) zg).mp hzgD
  have hxconjne : x * zg * x⁻¹ ≠ 1 := by
    intro h
    apply hzgne
    have := congrArg (fun q : G => x⁻¹ * q * x) h
    simpa [mul_assoc] using this
  have hxconjfix :=
    (xi1115_twoPointStabilizer_map_mem_iff a b hab (x * zg * x⁻¹)).mp (by
      simpa [H, D, Dg] using hxconjD)
  have himage (c : Omega) (hzc : zg • c = c) :
      x • c = a ∨ x • c = b := by
    by_cases hca : x • c = a
    · exact Or.inl hca
    by_cases hcb : x • c = b
    · exact Or.inr hcb
    exfalso
    apply
      (hat_most_two_fixed_points
        (x * zg * x⁻¹) hxconjne a b (x • c)
        hab (Ne.symm hca) (Ne.symm hcb))
    refine ⟨hxconjfix.1, hxconjfix.2, ?_⟩
    calc
      (x * zg * x⁻¹) • (x • c) = x • (zg • c) := by
        simp only [mul_smul, inv_smul_smul]
      _ = x • c := by rw [hzc]
  have hxa := himage a hzga
  have hxb := himage b hzgb
  rcases hxa with hxa | hxa
  · have hxb' : x • b = b := by
      rcases hxb with hxba | hxbb
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxa, hxba]
      · exact hxbb
    exfalso
    apply hxnot
    apply (xi1115_twoPointStabilizer_map_mem_iff a b hab x).mpr
    exact ⟨hxa, hxb'⟩
  · have hxb' : x • b = a := by
      rcases hxb with hxba | hxbb
      · exact hxba
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxa, hxbb]
    exact ⟨hxa, hxb'⟩

/-- The ambient normalizer of a nontrivial two-point stabilizer has index two
over that stabilizer: its elements either fix or interchange the two points. -/
private theorem xi1115_twoPointStabilizer_normalizer_index_two
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg := D.map H.subtype
    (Dg.subgroupOf (Subgroup.normalizer (Dg : Set G))).index = 2 := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change Dsub.index = 2
  obtain ⟨z, hz⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.complement_ne_bot
  let zg : G := ((z : H) : G)
  have hzgD : zg ∈ Dg := by
    exact ⟨(z : H), z.property, rfl⟩
  have hzgne : zg ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact h
  have hzga : zg • a = a := (z : H).property
  have hzgb : zg • b = b :=
    congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp z.property)
  obtain ⟨s, hsa, hsb⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo) hab hab.symm
  have hsinva : s⁻¹ • a = b := by
    rw [← hsb, inv_smul_smul]
  have hsinvb : s⁻¹ • b = a := by
    rw [← hsa, inv_smul_smul]
  have hsT : s ∈ T := by
    rw [show T = Subgroup.normalizer (Dg : Set G) from rfl,
      Subgroup.mem_normalizer_iff]
    intro g
    rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
      simpa [H, D, Dg] using xi1115_twoPointStabilizer_map_mem_iff a b hab g]
    rw [show s * g * s⁻¹ ∈ Dg ↔
        (s * g * s⁻¹) • a = a ∧ (s * g * s⁻¹) • b = b by
      simpa [H, D, Dg] using
        xi1115_twoPointStabilizer_map_mem_iff a b hab (s * g * s⁻¹)]
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hsinva, hgb, hsb]
      · simp only [mul_smul, hsinvb, hga, hsa]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = s⁻¹ • ((s * g * s⁻¹) • (s • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = s⁻¹ • ((s * g * s⁻¹) • b) := by rw [hsa]
          _ = s⁻¹ • b := by rw [hcgb]
          _ = a := hsinvb
      · calc
          g • b = s⁻¹ • ((s * g * s⁻¹) • (s • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = s⁻¹ • ((s * g * s⁻¹) • a) := by rw [hsb]
          _ = s⁻¹ • a := by rw [hcga]
          _ = b := hsinva
  let sT : T := ⟨s, hsT⟩
  have hsTnot : sT ∉ Dsub := by
    intro hsD
    have hsDg : s ∈ Dg := hsD
    have hsfix :=
      (xi1115_twoPointStabilizer_map_mem_iff a b hab s).mp (by
        simpa [H, D, Dg] using hsDg)
    exact hab (hsfix.1.symm.trans hsa)
  apply Subgroup.index_eq_two_iff_exists_notMem_and.mpr
  refine ⟨sT, hsTnot, ?_⟩
  intro x
  by_cases hxD : (x : G) ∈ Dg
  · exact Or.inr hxD
  · have hxswap :
        (x : G) • a = b ∧ (x : G) • b = a := by
      exact xi1115_twoPointStabilizer_normalizer_notMem_swaps
        hat_most_two_fixed_points a b hab F hFrob (x : G)
        (by exact x.property) (by exact hxD)
    left
    change ((x * sT : T) : G) ∈ Dg
    apply (xi1115_twoPointStabilizer_map_mem_iff a b hab ((x * sT : T) : G)).mpr
    constructor
    · change ((x : G) * s) • a = a
      rw [mul_smul, hsa, hxswap.2]
    · change ((x : G) * s) • b = b
      rw [mul_smul, hsb, hxswap.1]

/-- When the two-point stabilizer has odd order, its index-two ambient
normalizer contains an involution interchanging the two points. -/
private theorem xi1115_odd_twoPointStabilizer_exists_swap_involution
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    ∃ s : G, s ^ 2 = 1 ∧ s • a = b ∧ s • b = a := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      xi1115_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  letI : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  have hcop : (Nat.card Dsub).Coprime Dsub.index := by
    rw [hindex, hDsubcard]
    simpa [D] using hodd.coprime_two_right
  obtain ⟨C, hC⟩ := Subgroup.exists_left_complement'_of_coprime hcop
  have hCcard : Nat.card C = 2 :=
    hC.index_eq_card.symm.trans hindex
  have hCnontrivial : Nontrivial C :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  letI : Nontrivial C := hCnontrivial
  obtain ⟨c, hcne⟩ := exists_ne (1 : C)
  have hcnotD : (c : T) ∉ Dsub := by
    intro hcD
    have hcone : (c : T) = 1 :=
      Subgroup.disjoint_def.mp hC.disjoint c.property hcD
    apply hcne
    exact Subtype.ext hcone
  have hcpowC : c ^ 2 = 1 := by
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa [hCcard] using orderOf_dvd_natCard c
  have hcpowG : (((c : C) : T) : G) ^ 2 = 1 := by
    simpa using congrArg (fun q : C => (((q : C) : T) : G)) hcpowC
  have hcswap :
      (((c : C) : T) : G) • a = b ∧
        (((c : C) : T) : G) • b = a := by
    apply xi1115_twoPointStabilizer_normalizer_notMem_swaps
      hat_most_two_fixed_points a b hab F hFrob
    · exact (c : T).property
    · intro hcDg
      apply hcnotD
      exact hcDg
  exact ⟨(((c : C) : T) : G), hcpowG, hcswap⟩

/-- The normalizer of a nontrivial subgroup of the two-point stabilizer
already normalizes the whole two-point stabilizer.  This is the fixed-point
argument used in XI.1.5 before applying Burnside transfer. -/
private theorem xi1115_zassenhaus_twoPointSubgroup_normalizer_le
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (Q : Subgroup G)
    (hQle :
      Q ≤
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype)
    (hQne : Q ≠ ⊥) :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer
        (((MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
            (MulAction.stabilizer G a).subtype : Subgroup G) : Set G) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  change Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (Dg : Set G)
  intro x hx
  obtain ⟨⟨z, hzQ⟩, hzne⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hQne
  have hzD : z ∈ Dg := by simpa [H, D, Dg] using hQle hzQ
  have hzfix : z • a = a ∧ z • b = b :=
    (xi1115_twoPointStabilizer_map_mem_iff a b hab z).mp (by
      simpa [H, D, Dg] using hzD)
  have hxzQ : x * z * x⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp hx z).mp hzQ
  have hxzD : x * z * x⁻¹ ∈ Dg := by
    simpa [H, D, Dg] using hQle hxzQ
  have hxzne : x * z * x⁻¹ ≠ 1 := by
    intro h
    apply hzne
    have := congrArg (fun q : G => x⁻¹ * q * x) h
    simpa [mul_assoc] using this
  have hxzfix :
      (x * z * x⁻¹) • a = a ∧ (x * z * x⁻¹) • b = b :=
    (xi1115_twoPointStabilizer_map_mem_iff a b hab (x * z * x⁻¹)).mp (by
      simpa [H, D, Dg] using hxzD)
  have himage (c : Omega) (hzc : z • c = c) :
      x • c = a ∨ x • c = b := by
    by_cases hca : x • c = a
    · exact Or.inl hca
    by_cases hcb : x • c = b
    · exact Or.inr hcb
    exfalso
    apply
      (hat_most_two_fixed_points (x * z * x⁻¹) hxzne a b (x • c)
        hab (Ne.symm hca) (Ne.symm hcb))
    refine ⟨hxzfix.1, hxzfix.2, ?_⟩
    calc
      (x * z * x⁻¹) • (x • c) = x • (z • c) := by
        simp only [mul_smul, inv_smul_smul]
      _ = x • c := by rw [hzc]
  have hxa := himage a hzfix.1
  have hxb := himage b hzfix.2
  have hxpair :
      (x • a = a ∧ x • b = b) ∨ (x • a = b ∧ x • b = a) := by
    rcases hxa with hxaa | hxab
    · left
      refine ⟨hxaa, ?_⟩
      rcases hxb with hxba | hxbb
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxaa, hxba]
      · exact hxbb
    · right
      refine ⟨hxab, ?_⟩
      rcases hxb with hxba | hxbb
      · exact hxba
      · exfalso
        apply hab
        apply (MulAction.toPerm x).injective
        change x • a = x • b
        rw [hxab, hxbb]
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
    simpa [H, D, Dg] using xi1115_twoPointStabilizer_map_mem_iff a b hab g]
  rw [show x * g * x⁻¹ ∈ Dg ↔
      (x * g * x⁻¹) • a = a ∧ (x * g * x⁻¹) • b = b by
    simpa [H, D, Dg] using
      xi1115_twoPointStabilizer_map_mem_iff a b hab (x * g * x⁻¹)]
  rcases hxpair with ⟨hxa, hxb⟩ | ⟨hxa, hxb⟩
  · have hxinva : x⁻¹ • a = a := by
      calc
        x⁻¹ • a = x⁻¹ • (x • a) := congrArg (fun y => x⁻¹ • y) hxa.symm
        _ = a := inv_smul_smul x a
    have hxinvb : x⁻¹ • b = b := by
      calc
        x⁻¹ • b = x⁻¹ • (x • b) := congrArg (fun y => x⁻¹ • y) hxb.symm
        _ = b := inv_smul_smul x b
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hxinva, hga, hxa]
      · simp only [mul_smul, hxinvb, hgb, hxb]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = x⁻¹ • ((x * g * x⁻¹) • (x • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • a) := by rw [hxa]
          _ = x⁻¹ • a := by rw [hcga]
          _ = a := hxinva
      · calc
          g • b = x⁻¹ • ((x * g * x⁻¹) • (x • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • b) := by rw [hxb]
          _ = x⁻¹ • b := by rw [hcgb]
          _ = b := hxinvb
  · have hxinva : x⁻¹ • a = b := by rw [← hxb, inv_smul_smul]
    have hxinvb : x⁻¹ • b = a := by rw [← hxa, inv_smul_smul]
    constructor
    · rintro ⟨hga, hgb⟩
      constructor
      · simp only [mul_smul, hxinva, hgb, hxb]
      · simp only [mul_smul, hxinvb, hga, hxa]
    · rintro ⟨hcga, hcgb⟩
      constructor
      · calc
          g • a = x⁻¹ • ((x * g * x⁻¹) • (x • a)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • b) := by rw [hxa]
          _ = x⁻¹ • b := by rw [hcgb]
          _ = a := hxinvb
      · calc
          g • b = x⁻¹ • ((x * g * x⁻¹) • (x • b)) := by
            simp only [mul_smul, inv_smul_smul]
          _ = x⁻¹ • ((x * g * x⁻¹) • a) := by rw [hxb]
          _ = x⁻¹ • a := by rw [hcga]
          _ = b := hxinva

/-- For odd two-point-stabilizer order, its index-two ambient normalizer is a
Z-group.  This packages the coprime extension step in XI.1.5. -/
private theorem xi1115_odd_twoPointNormalizer_isZGroup
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg : Subgroup G := D.map H.subtype
    IsZGroup (Subgroup.normalizer (Dg : Set G)) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change IsZGroup T
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      xi1115_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  letI : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  letI : IsZGroup D :=
    isZGroup_of_frobenius_complement_of_odd F D (by simpa [D] using hFrob) hodd
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eD : Dsub ≃* D := eDsub.trans eDg.symm
  letI : IsZGroup Dsub :=
    IsZGroup.of_injective (f := eD.toMonoidHom) eD.injective
  have hquotCard : Nat.card (T ⧸ Dsub) = 2 := by
    rw [← Dsub.index_eq_card]
    exact hindex
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclic (T ⧸ Dsub) :=
    isCyclic_of_card_dvd_prime (by rw [hquotCard])
  have hcop : (Nat.card Dsub).Coprime (Nat.card (T ⧸ Dsub)) := by
    rw [hDsubcard, hquotCard]
    simpa [D] using hodd.coprime_two_right
  exact isZGroup_of_coprime
    (f := Dsub.subtype) (f' := QuotientGroup.mk' Dsub)
    (by simp) hcop

/-- XI.1.5, cyclicity part: in a simple Zassenhaus group the odd two-point
stabilizer is cyclic. -/
private theorem xi1115_odd_twoPointStabilizer_cyclic_and_commutator_eq
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    let H := MulAction.stabilizer G a
    let D := MulAction.stabilizer H
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    let Dg : Subgroup G := D.map H.subtype
    let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
    IsCyclic D ∧ commutator T = Dg.subgroupOf T := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change IsCyclic D ∧ commutator T = Dsub
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      xi1115_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  letI : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  have hDgcard : Nat.card Dg = Nat.card D := by
    simpa [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H.subtype) H.subtype_injective)
  have hDsubcard : Nat.card Dsub = Nat.card D := by
    calc
      Nat.card Dsub = Nat.card Dg :=
        natCard_subgroupOf_eq Dg T Subgroup.le_normalizer
      _ = Nat.card D := hDgcard
  have hTcard : Nat.card T = 2 * Nat.card D := by
    calc
      Nat.card T = Nat.card Dsub * Dsub.index := Dsub.card_mul_index.symm
      _ = 2 * Nat.card D := by rw [hDsubcard, hindex]; omega
  letI : IsZGroup T := by
    simpa [H, D, Dg, T] using
      xi1115_odd_twoPointNormalizer_isZGroup
        htwo hat_most_two_fixed_points a b hab F hFrob hodd
  have hcommCyclic : IsCyclic (commutator T) :=
    IsZGroup.isCyclic_commutator T
  have hquotCard : Nat.card (T ⧸ Dsub) = 2 := by
    rw [← Dsub.index_eq_card]
    exact hindex
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : IsCyclic (T ⧸ Dsub) :=
    isCyclic_of_card_dvd_prime (by rw [hquotCard])
  letI : CommGroup (T ⧸ Dsub) := IsCyclic.commGroup
  have hcommLe : commutator T ≤ Dsub := by
    simpa using
      (Abelianization.commutator_subset_ker (QuotientGroup.mk' Dsub))
  have hnoOddPrime :
      ∀ q : ℕ, q.Prime → q ≠ 2 → ¬ q ∣ (commutator T).index := by
    intro q hq hqne hqindex
    letI : Fact q.Prime := ⟨hq⟩
    have hqT : q ∣ Nat.card T :=
      hqindex.trans (commutator T).index_dvd_card
    have hqcommNot : ¬ q ∣ Nat.card (commutator T) := by
      apply hq.coprime_iff_not_dvd.mp
      exact Nat.Coprime.of_dvd_left hqindex
        (IsZGroup.coprime_commutator_index T).symm
    let Qd : Sylow q D := default
    let iotaD : D →* G := H.subtype.comp D.subtype
    have hiotaD : Function.Injective iotaD :=
      H.subtype_injective.comp D.subtype_injective
    let Qg : Subgroup G := (Qd : Subgroup D).map iotaD
    have hDgRange : iotaD.range = Dg := by
      ext x
      constructor
      · rintro ⟨d, rfl⟩
        exact ⟨(d : H), d.property, rfl⟩
      · rintro ⟨d, hdD, rfl⟩
        exact ⟨⟨d, hdD⟩, rfl⟩
    have hDgMapTop : Subgroup.map iotaD (⊤ : Subgroup D) = Dg := by
      calc
        Subgroup.map iotaD (⊤ : Subgroup D) = iotaD.range := by
          ext x
          constructor
          · rintro ⟨d, _hd, rfl⟩
            exact ⟨d, rfl⟩
          · rintro ⟨d, rfl⟩
            exact ⟨d, trivial, rfl⟩
        _ = Dg := hDgRange
    have hQgDg : Qg ≤ Dg := by
      simpa [Qg, hDgRange] using
        (Subgroup.map_le_range iotaD (Qd : Subgroup D))
    have hQgT : Qg ≤ T := hQgDg.trans Subgroup.le_normalizer
    have hQgP : IsPGroup q Qg := Qd.isPGroup'.map iotaD
    let QTsub : Subgroup T := Qg.subgroupOf T
    have hQTsubP : IsPGroup q QTsub :=
      hQgP.of_equiv (Subgroup.subgroupOfEquivOfLe hQgT).symm
    have hrelQD : Qg.relIndex Dg = Qd.index := by
      rw [show Qg = Subgroup.map iotaD (Qd : Subgroup D) from rfl,
        ← hDgMapTop,
        Subgroup.relIndex_map_map_of_injective
          (Qd : Subgroup D) (⊤ : Subgroup D) hiotaD,
        Subgroup.relIndex_top_right]
    have hrelQT : Qg.relIndex T = Qd.index * 2 := by
      calc
        Qg.relIndex T = Qg.relIndex Dg * Dg.relIndex T :=
          (Subgroup.relIndex_mul_relIndex Qg Dg T hQgDg
            Subgroup.le_normalizer).symm
        _ = Qd.index * Dsub.index := by rw [hrelQD]; rfl
        _ = Qd.index * 2 := by rw [hindex]
    have hQTsubIndex : QTsub.index = Qd.index * 2 := by
      change Qg.relIndex T = Qd.index * 2
      exact hrelQT
    have hqQTsubIndex : ¬ q ∣ QTsub.index := by
      rw [hQTsubIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqQd | hq2
      · exact Qd.not_dvd_index hqQd
      · rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with hq1 | hq2eq
        · exact hq.ne_one hq1
        · exact hqne hq2eq
    let QT : Sylow q T := hQTsubP.toSylow hqQTsubIndex
    have hQTcoe : (QT : Subgroup T) = QTsub :=
      IsPGroup.toSylow_coe hQTsubP hqQTsubIndex
    have hnormalizerCentralT :
        Subgroup.normalizer ((QTsub : Subgroup T) : Set T) ≤
          Subgroup.centralizer (QTsub : Set T) := by
      rcases Sylow.normalizer_le_centralizer_or_le_commutator QT with hcent | hle
      · have hQTcoe_set : (QT : Set T) = (QTsub : Set T) := by
          simpa using congrArg (fun (s : Subgroup T) => (s : Set T)) hQTcoe
        simpa [hQTcoe_set] using hcent
      · exfalso
        apply hqcommNot
        exact (QT.dvd_card_of_dvd_card hqT).trans
          (Subgroup.card_dvd_of_le hle)
    obtain ⟨hOmegaCard, _hHcard, hGcard, hDdvd⟩ :=
      xi1115_action_parameters_core htwo a b hab F hFrob
    have hqD : q ∣ Nat.card D := by
      have hq2D : q ∣ 2 * Nat.card D := by
        rw [← hTcard]
        exact hqT
      rcases hq.dvd_mul.mp hq2D with hq2 | hqD
      · rcases (Nat.dvd_prime Nat.prime_two).mp hq2 with hq1 | hq2eq
        · exact (hq.ne_one hq1).elim
        · exact (hqne hq2eq).elim
      · exact hqD
    have hqFsub : q ∣ Nat.card F - 1 := hqD.trans (by simpa [D] using hDdvd)
    have hFcardGt : 1 < Nat.card F :=
      (Subgroup.nontrivial_iff_ne_bot F).2 hFrob.kernel_ne_bot |>
        Finite.one_lt_card_iff_nontrivial.mpr
    have hqFnot : ¬ q ∣ Nat.card F := by
      intro hqF
      have hqone : q ∣ 1 := by
        have := Nat.dvd_sub hqF hqFsub
        convert this using 1; omega
      exact hq.not_dvd_one hqone
    have hqFplusNot : ¬ q ∣ Nat.card F + 1 := by
      intro hqFplus
      have hqtwo : q ∣ 2 := by
        have := Nat.dvd_sub hqFplus hqFsub
        convert this using 1; omega
      rcases (Nat.dvd_prime Nat.prime_two).mp hqtwo with hq1 | hq2eq
      · exact hq.ne_one hq1
      · exact hqne hq2eq
    have hDgIndex : Dg.index = (Nat.card F + 1) * Nat.card F := by
      apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := D))
      calc
        Nat.card D * Dg.index = Nat.card Dg * Dg.index := by rw [hDgcard]
        _ = Nat.card G := Dg.card_mul_index
        _ = Fintype.card Omega * Nat.card F * Nat.card D := by
          simpa [D] using hGcard
        _ = Nat.card D * ((Nat.card F + 1) * Nat.card F) := by
          rw [hOmegaCard]
          ring
    have hqDgIndex : ¬ q ∣ Dg.index := by
      rw [hDgIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqFplus | hqF
      · exact hqFplusNot hqFplus
      · exact hqFnot hqF
    have hiotaKer : iotaD.ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff iotaD).mpr hiotaD
    have hQgIndex : Qg.index = Qd.index * Dg.index := by
      calc
        Qg.index =
            ((Qd : Subgroup D) ⊔ iotaD.ker).index * iotaD.range.index :=
          Subgroup.index_map (Qd : Subgroup D) iotaD
        _ = Qd.index * Dg.index := by
          rw [hiotaKer, sup_bot_eq, hDgRange]
    have hqQgIndex : ¬ q ∣ Qg.index := by
      rw [hQgIndex]
      intro hqmul
      rcases hq.dvd_mul.mp hqmul with hqQd | hqDg
      · exact Qd.not_dvd_index hqQd
      · exact hqDgIndex hqDg
    let QG : Sylow q G := hQgP.toSylow hqQgIndex
    have hQGcoe : (QG : Subgroup G) = Qg :=
      IsPGroup.toSylow_coe hQgP hqQgIndex
    have hqG : q ∣ Nat.card G :=
      hqT.trans (Subgroup.card_subgroup_dvd_card T)
    have hQgNe : Qg ≠ ⊥ := by
      rw [← hQGcoe]
      exact Sylow.ne_bot_of_dvd_card QG hqG
    have hnormalizerLeT : Subgroup.normalizer (Qg : Set G) ≤ T := by
      simpa [H, D, Dg, T] using
        xi1115_zassenhaus_twoPointSubgroup_normalizer_le
          hat_most_two_fixed_points a b hab Qg hQgDg hQgNe
    have hnormalizerCentralG :
        Subgroup.normalizer (Qg : Set G) ≤
          Subgroup.centralizer (Qg : Set G) := by
      intro x hx
      let xT : T := ⟨x, hnormalizerLeT hx⟩
      have hxNormT : xT ∈ Subgroup.normalizer (QTsub : Set T) := by
        rw [Subgroup.mem_normalizer_iff] at hx ⊢
        intro y
        change ((y : T) : G) ∈ Qg ↔
          (((xT * y * xT⁻¹ : T) : G) ∈ Qg)
        exact hx ((y : T) : G)
      have hxCentT : xT ∈ Subgroup.centralizer (QTsub : Set T) :=
        hnormalizerCentralT hxNormT
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let yT : T := ⟨y, hQgT hy⟩
      have hyQT : yT ∈ QTsub := hy
      have hcommT :=
        (Subgroup.mem_centralizer_iff.mp hxCentT) yT hyQT
      exact congrArg Subtype.val hcommT
    have hcentralG :
        Subgroup.normalizer ((QG : Subgroup G) : Set G) ≤
          Subgroup.centralizer ((QG : Subgroup G) : Set G) := by
      simpa [hQGcoe] using hnormalizerCentralG
    have hcomp := MonoidHom.ker_transferSylow_isComplement' QG hcentralG
    let K : Subgroup G := (MonoidHom.transferSylow QG hcentralG).ker
    have hQGne : (QG : Subgroup G) ≠ ⊥ :=
      Sylow.ne_bot_of_dvd_card QG hqG
    obtain ⟨s, _hsq, hsa, _hsb⟩ :=
      xi1115_odd_twoPointStabilizer_exists_swap_involution
        htwo hat_most_two_fixed_points a b hab F hFrob hodd
    have hQGtop : (QG : Subgroup G) ≠ ⊤ := by
      intro htop
      have hsQg : s ∈ Qg := by
        rw [← hQGcoe, htop]
        trivial
      have hsfix :=
        (xi1115_twoPointStabilizer_map_mem_iff a b hab s).mp (hQgDg hsQg)
      exact hab (hsfix.1.symm.trans hsa)
    by_cases hKbot : K = ⊥
    · apply hQGtop
      apply Subgroup.isComplement'_bot_left.mp
      simpa [K, hKbot] using hcomp
    · have hKtop : K = ⊤ := hsimple K inferInstance hKbot
      apply hQGne
      apply Subgroup.isComplement'_top_left.mp
      simpa [K, hKtop] using hcomp
  have htwoDvd : 2 ∣ (commutator T).index := by
    rw [← hindex]
    exact Subgroup.index_dvd_of_le hcommLe
  have hcommIndexDvd : (commutator T).index ∣ 2 * Nat.card D := by
    rw [← hTcard]
    exact (commutator T).index_dvd_card
  obtain ⟨m, hm⟩ := htwoDvd
  have hmDvd : m ∣ Nat.card D := by
    obtain ⟨r, hr⟩ := hcommIndexDvd
    refine ⟨r, ?_⟩
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 by omega)
    calc
      2 * Nat.card D = (commutator T).index * r := hr
      _ = (2 * m) * r := by rw [hm]
      _ = 2 * (m * r) := by ring
  have hmOne : m = 1 := by
    by_contra hmne
    obtain ⟨q, hq, hqm⟩ := Nat.exists_prime_and_dvd hmne
    have hqD : q ∣ Nat.card D := hqm.trans hmDvd
    have hqne : q ≠ 2 := by
      intro hqeq
      subst q
      exact (Nat.not_even_iff_odd.mpr (by simpa [D] using hodd))
        (even_iff_two_dvd.mpr (by simpa [D] using hqD))
    exact hnoOddPrime q hq hqne
      (hqm.trans (by rw [hm]; exact dvd_mul_left m 2))
  have hcommIndex : (commutator T).index = 2 := by
    rw [hm, hmOne]
  have hcommCard : Nat.card (commutator T) = Nat.card Dsub := by
    apply Nat.eq_of_mul_eq_mul_right (show 0 < 2 by omega)
    calc
      Nat.card (commutator T) * 2 = Nat.card T := by
        rw [← hcommIndex]
        exact (commutator T).card_mul_index
      _ = Nat.card Dsub * 2 := by
        rw [← hindex]
        exact Dsub.card_mul_index.symm
  have hcommEq : commutator T = Dsub :=
    Subgroup.eq_of_le_of_card_ge hcommLe (by rw [hcommCard])
  have hDsubCyclic : IsCyclic Dsub := by
    rw [hcommEq] at hcommCyclic
    exact hcommCyclic
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eD : Dsub ≃* D := eDsub.trans eDg.symm
  exact ⟨isCyclic_of_surjective eD eD.surjective, hcommEq⟩

/-- Any element interchanging the distinguished points normalizes their
pointwise stabilizer. -/
private theorem xi1115_swap_mem_twoPointStabilizer_normalizer
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (a b : Omega) (hab : a ≠ b) (s : G)
    (hsa : s • a = b) (hsb : s • b = a) :
    s ∈ Subgroup.normalizer
      (((MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)).map
          (MulAction.stabilizer G a).subtype : Subgroup G) : Set G) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  have hsinva : s⁻¹ • a = b := by
    calc
      s⁻¹ • a = s⁻¹ • (s • b) := by rw [hsb]
      _ = b := inv_smul_smul s b
  have hsinvb : s⁻¹ • b = a := by
    calc
      s⁻¹ • b = s⁻¹ • (s • a) := by rw [hsa]
      _ = a := inv_smul_smul s a
  change s ∈ Subgroup.normalizer (Dg : Set G)
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [show g ∈ Dg ↔ g • a = a ∧ g • b = b by
    simpa [H, D, Dg] using xi1115_twoPointStabilizer_map_mem_iff a b hab g]
  rw [show s * g * s⁻¹ ∈ Dg ↔
      (s * g * s⁻¹) • a = a ∧ (s * g * s⁻¹) • b = b by
    simpa [H, D, Dg] using
      xi1115_twoPointStabilizer_map_mem_iff a b hab (s * g * s⁻¹)]
  constructor
  · rintro ⟨hga, hgb⟩
    constructor
    · simp only [mul_smul, hsinva, hgb, hsb]
    · simp only [mul_smul, hsinvb, hga, hsa]
  · rintro ⟨hcga, hcgb⟩
    constructor
    · calc
        g • a = s⁻¹ • ((s * g * s⁻¹) • (s • a)) := by
          simp only [mul_smul, inv_smul_smul]
        _ = s⁻¹ • ((s * g * s⁻¹) • b) := by rw [hsa]
        _ = s⁻¹ • b := by rw [hcgb]
        _ = a := hsinvb
    · calc
        g • b = s⁻¹ • ((s * g * s⁻¹) • (s • b)) := by
          simp only [mul_smul, inv_smul_smul]
        _ = s⁻¹ • ((s * g * s⁻¹) • a) := by rw [hsb]
        _ = s⁻¹ • a := by rw [hcga]
        _ = b := hsinva


/-- XI.1.5, cyclicity part: in a simple Zassenhaus group the odd two-point
stabilizer is cyclic. -/
private theorem xi1115_odd_twoPointStabilizer_isCyclic
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))) :
    IsCyclic
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :=
  (xi1115_odd_twoPointStabilizer_cyclic_and_commutator_eq
    htwo hat_most_two_fixed_points hsimple a b hab F hFrob hodd).1

private theorem xi1115_isMulCommutative_sup_of_le_centralizer
    {Q : Type*} [Group Q] {A B : Subgroup Q}
    (hAcomm : IsMulCommutative A) (hBcomm : IsMulCommutative B)
    (hBcentral : B ≤ Subgroup.centralizer (A : Set Q)) :
    IsMulCommutative (A ⊔ B : Subgroup Q) := by
  rw [Subgroup.sup_eq_closure]
  haveI : IsMulCommutative (Subgroup.closure ((A : Set Q) ∪ (B : Set Q))) :=
    Subgroup.isMulCommutative_closure (by
      intro x hx y hy _
      rcases hx with hxA | hxB
      · rcases hy with hyA | hyB
        · exact setLike_mul_comm
            (s := A) hxA hyA
        · exact Subgroup.mem_centralizer_iff.mp (hBcentral hyB) x hxA
      · rcases hy with hyA | hyB
        · exact (Subgroup.mem_centralizer_iff.mp (hBcentral hxB) y hyA).symm
        · exact setLike_mul_comm
            (s := B) hxB hyB)
  exact inferInstance

/-- XI.1.5, inversion part: every element interchanging the two points acts
by inversion on the odd cyclic two-point stabilizer. -/
private theorem xi1115_odd_twoPointStabilizer_swap_inverts
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hsimple : ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hodd :
      Odd (Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (s : G) (hsa : s • a = b) (hsb : s • b = a) :
    ∀ x : MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
      s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
        ((((x⁻¹ : MulAction.stabilizer
          (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
            MulAction.stabilizer G a) : G)) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Dg : Subgroup G := D.map H.subtype
  let T : Subgroup G := Subgroup.normalizer (Dg : Set G)
  let Dsub : Subgroup T := Dg.subgroupOf T
  change ∀ x : D, s * (((x : H) : G)) * s⁻¹ = (((x⁻¹ : D) : H) : G)
  have hindex : Dsub.index = 2 := by
    simpa [H, D, Dg, T, Dsub] using
      xi1115_twoPointStabilizer_normalizer_index_two
        htwo hat_most_two_fixed_points a b hab F hFrob
  letI : Dsub.Normal := Subgroup.normal_of_index_eq_two hindex
  obtain ⟨hDcyclic, hcommEq⟩ :=
    xi1115_odd_twoPointStabilizer_cyclic_and_commutator_eq
      htwo hat_most_two_fixed_points hsimple a b hab F hFrob hodd
  let eDg : D ≃* Dg :=
    Subgroup.equivMapOfInjective D H.subtype H.subtype_injective
  let eDsub : Dsub ≃* Dg :=
    Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer
  let eDDsub : D ≃* Dsub := eDg.trans eDsub.symm
  letI : IsCyclic D := hDcyclic
  letI : IsCyclic Dsub :=
    isCyclic_of_surjective eDDsub eDDsub.surjective
  letI : CommGroup Dsub := IsCyclic.commGroup
  have hDsubComm : IsMulCommutative Dsub := inferInstance
  have hDsubcard : Nat.card Dsub = Nat.card D :=
    Nat.card_congr eDDsub.symm.toEquiv
  obtain ⟨c, hcSq, hca, hcb⟩ :=
    xi1115_odd_twoPointStabilizer_exists_swap_involution
      htwo hat_most_two_fixed_points a b hab F hFrob hodd
  have hcTmem : c ∈ T := by
    simpa [H, D, Dg, T] using
      xi1115_swap_mem_twoPointStabilizer_normalizer a b hab c hca hcb
  let cT : T := ⟨c, hcTmem⟩
  have hcTnotD : cT ∉ Dsub := by
    intro hcD
    have hcDg : c ∈ Dg := hcD
    have hcfix :=
      (xi1115_twoPointStabilizer_map_mem_iff a b hab c).mp hcDg
    exact hab (hcfix.1.symm.trans hca)
  have hcTne : cT ≠ 1 := by
    intro hcOne
    apply hcTnotD
    simp [hcOne]
  have hcTSq : cT ^ 2 = 1 := by
    apply Subtype.ext
    exact hcSq
  let R : Subgroup T := Subgroup.zpowers cT
  letI : IsCyclic R := inferInstance
  letI : CommGroup R := IsCyclic.commGroup
  have hRcomm : IsMulCommutative R := inferInstance
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcTorder : orderOf cT = 2 := orderOf_eq_prime hcTSq hcTne
  have hRcard : Nat.card R = 2 := by
    simp [R, hcTorder]

  have hsup : Dsub ⊔ R = ⊤ := by
    apply top_unique
    intro x _hx
    by_cases hxD : (x : T) ∈ Dsub
    · exact Subgroup.mem_sup_left hxD
    · have hxswap :
          ((x : T) : G) • a = b ∧ ((x : T) : G) • b = a := by
        have hxnotDg : ((x : T) : G) ∉ Dg := by
          intro hxDg
          exact hxD hxDg
        exact xi1115_twoPointStabilizer_normalizer_notMem_swaps
          hat_most_two_fixed_points a b hab F hFrob ((x : T) : G)
          (by exact x.property) hxnotDg
      have hxcDg : (((x * cT : T) : G)) ∈ Dg := by
        apply (xi1115_twoPointStabilizer_map_mem_iff a b hab ((x * cT : T) : G)).mpr
        constructor
        · change (((x : T) : G) * c) • a = a
          rw [mul_smul, hca, hxswap.2]
        · change (((x : T) : G) * c) • b = b
          rw [mul_smul, hcb, hxswap.1]
      have hxcD : x * cT ∈ Dsub := by
        simpa [Dsub, Subgroup.mem_subgroupOf] using hxcDg
      have hcR : cT ∈ R := Subgroup.mem_zpowers cT
      have hcMul : cT * cT = 1 := by simpa [pow_two] using hcTSq
      have hxrepr : x = (x * cT) * cT := by
        rw [mul_assoc, hcMul, mul_one]
      rw [hxrepr]
      exact (Dsub ⊔ R).mul_mem
        (Subgroup.mem_sup_left hxcD) (Subgroup.mem_sup_right hcR)
  have hRnormD : R ≤ Subgroup.normalizer (Dsub : Set T) := by
    simp [Dsub.normalizer_eq_top]
  let N : Subgroup T := ⁅Dsub, R⁆
  haveI : N.Normal := by
    have hNnormal := commutator_normal_in_sup Dsub R
    have hsupLe : Dsub ⊔ R ≤ Subgroup.normalizer (N : Set T) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (H := N) (K := Dsub ⊔ R)
          (by simpa [N] using commutator_le_sup Dsub R)).mp
        (by simpa [N] using hNnormal)
    have htopLe : (⊤ : Subgroup T) ≤ Subgroup.normalizer (N : Set T) := by
      simpa [hsup] using hsupLe
    exact Subgroup.normalizer_eq_top_iff.mp (top_unique htopLe)
  let pi : T →* T ⧸ N := QuotientGroup.mk' N
  let A : Subgroup (T ⧸ N) := Dsub.map pi
  let B : Subgroup (T ⧸ N) := R.map pi
  have hAcomm : IsMulCommutative A := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    rcases x.property with ⟨xT, hxD, hx⟩
    rcases y.property with ⟨yT, hyD, hy⟩
    change (x : T ⧸ N) * y = y * x
    rw [← hx, ← hy]
    exact congrArg pi
      (setLike_mul_comm
        (s := Dsub) hxD hyD)
  have hBcomm : IsMulCommutative B := by
    refine ⟨⟨fun x y => ?_⟩⟩
    apply Subtype.ext
    rcases x.property with ⟨xT, hxR, hx⟩
    rcases y.property with ⟨yT, hyR, hy⟩
    change (x : T ⧸ N) * y = y * x
    rw [← hx, ← hy]
    exact congrArg pi
      (setLike_mul_comm
        (s := R) hxR hyR)
  have hBcentralA : B ≤ Subgroup.centralizer (A : Set (T ⧸ N)) := by
    intro rbar hrbar
    rcases hrbar with ⟨r, hrR, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro dbar hdbar
    rcases hdbar with ⟨d, hdD, rfl⟩
    have hdrN : ⁅d, r⁆ ∈ N :=
      Subgroup.commutator_mem_commutator
        (H₁ := Dsub) (H₂ := R) hdD hrR
    have hcomm : Commute (pi d) (pi r) := by
      apply commutatorElement_eq_one_iff_commute.mp
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff ⁅d, r⁆).2 hdrN
    exact hcomm.eq
  have hABtop : A ⊔ B = ⊤ := by
    calc
      A ⊔ B = Subgroup.map pi (Dsub ⊔ R) :=
        (Subgroup.map_sup Dsub R pi).symm
      _ = Subgroup.map pi ⊤ := by rw [hsup]
      _ = pi.range := (MonoidHom.range_eq_map pi).symm
      _ = ⊤ := MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N)
  have hquotComm : IsMulCommutative (T ⧸ N) := by
    have h := xi1115_isMulCommutative_sup_of_le_centralizer hAcomm hBcomm hBcentralA
    rw [hABtop] at h
    letI : IsMulCommutative (⊤ : Subgroup (T ⧸ N)) := h
    refine ⟨⟨fun x y => ?_⟩⟩
    have hxy :
        (⟨x, trivial⟩ : (⊤ : Subgroup (T ⧸ N))) * ⟨y, trivial⟩ =
          ⟨y, trivial⟩ * ⟨x, trivial⟩ := mul_comm _ _
    exact congrArg Subtype.val hxy
  have hcommLeN : commutator T ≤ N :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := N)).mp
      hquotComm
  have hNleComm : N ≤ commutator T := by
    exact Subgroup.commutator_mono le_top le_top
  have hNeqD : N = Dsub :=
    (le_antisymm hNleComm hcommLeN).trans hcommEq
  letI : Subgroup.Normalizes R Dsub := ⟨hRnormD⟩
  letI : MulDistribMulAction R Dsub :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer R Dsub hRnormD
  have hactionMap :
      (commutatorAction (A := R) (G := Dsub)).map Dsub.subtype = N := by
    simpa [N] using
      commutatorAction_subgroup_conj_map_eq_commutator Dsub R hRnormD
  have hactionTop : commutatorAction (A := R) (G := Dsub) = ⊤ := by
    apply Subgroup.map_injective Dsub.subtype_injective
    calc
      Subgroup.map Dsub.subtype (commutatorAction (A := R) (G := Dsub)) = N :=
        hactionMap
      _ = Dsub := hNeqD
      _ = Dsub.subtype.range := (Dsub.range_subtype).symm
      _ = Subgroup.map Dsub.subtype ⊤ := MonoidHom.range_eq_map Dsub.subtype
  have hcop : (Nat.card R).Coprime (Nat.card Dsub) := by
    rw [hRcard, hDsubcard]
    exact (by simpa [D] using hodd.coprime_two_right.symm)
  have hcompl :
      IsCompl (fixedPointSubgroup R Dsub)
        (commutatorAction (A := R) (G := Dsub)) :=
    isCompl_fixedPointSubgroup_commutatorAction_of_solvable_coprime_of_isMulCommutative
      (Group.isSolvable_of_comm hDsubComm.is_comm.comm) hcop hDsubComm
  have hfixedBot : fixedPointSubgroup R Dsub = ⊥ := by
    apply bot_unique
    have hle := hcompl.disjoint.le_bot
    simpa [hactionTop] using hle
  have hcNorm : cT ∈ Subgroup.normalizer (Dsub : Set T) := by
    rw [Dsub.normalizer_eq_top]
    trivial
  let cN : Subgroup.normalizer (Dsub : Set T) := ⟨cT, hcNorm⟩
  let phi : MulAut Dsub := Dsub.normalizerMonoidHom cN
  have hphiSq : phi ^ 2 = 1 := by
    change (Dsub.normalizerMonoidHom cN) ^ 2 = 1
    have hcNSq : cN ^ 2 = 1 := by
      apply Subtype.ext
      exact hcTSq
    rw [← map_pow, hcNSq, map_one]
  have hphiInv : Function.Involutive phi := by
    intro x
    have hx := congrArg (fun psi : MulAut Dsub => psi x) hphiSq
    simpa [pow_two] using hx
  have hphiFree : MonoidHom.FixedPointFree phi := by
    intro x hx
    have hconjFix : cT * (x : T) * cT⁻¹ = (x : T) := by
      simpa [phi, cN, Subgroup.normalizerMonoidHom_apply_apply_coe] using
        congrArg Subtype.val hx
    have hccomm : Commute cT (x : T) := by
      apply commutatorElement_eq_one_iff_commute.mp
      simp [commutatorElement_def, hconjFix]
    have hxFixed : x ∈ fixedPointSubgroup R Dsub := by
      change ∀ r : R, r • x = x
      intro r
      rcases Subgroup.mem_zpowers_iff.mp r.property with ⟨k, hk⟩
      have hrcomm : Commute (r : T) (x : T) := by
        rw [← hk]
        exact hccomm.zpow_left k
      apply Subtype.ext
      change (r : T) * (x : T) * (r : T)⁻¹ = (x : T)
      rw [hrcomm.eq]
      simp [mul_assoc]
    have hxBot : x ∈ (⊥ : Subgroup Dsub) := by
      simpa [hfixedBot] using hxFixed
    exact Subgroup.mem_bot.mp hxBot
  have hphiEqInv : ⇑phi = fun x : Dsub => x⁻¹ :=
    hphiFree.coe_eq_inv_of_involutive hphiInv
  have hcInverts (x : Dsub) :
      cT * (x : T) * cT⁻¹ = ((x⁻¹ : Dsub) : T) := by
    have hx := congrArg Subtype.val (congrFun hphiEqInv x)
    simpa [phi, cN, Subgroup.normalizerMonoidHom_apply_apply_coe] using hx
  have hsTmem : s ∈ T := by
    simpa [H, D, Dg, T] using
      xi1115_swap_mem_twoPointStabilizer_normalizer a b hab s hsa hsb
  let sT : T := ⟨s, hsTmem⟩
  intro x
  let xDg : Dg := ⟨((x : H) : G), ⟨(x : H), x.property, rfl⟩⟩
  let xT : T := ⟨(xDg : G), Subgroup.le_normalizer xDg.property⟩
  let xDsub : Dsub := ⟨xT, xDg.property⟩
  have hscDg : (((sT * cT : T) : G)) ∈ Dg := by
    apply (xi1115_twoPointStabilizer_map_mem_iff a b hab ((sT * cT : T) : G)).mpr
    constructor
    · change (s * c) • a = a
      rw [mul_smul, hca, hsb]
    · change (s * c) • b = b
      rw [mul_smul, hcb, hsa]
  let dT : Dsub := ⟨sT * cT, by simpa [Dsub, Subgroup.mem_subgroupOf] using hscDg⟩
  have hcMul : cT * cT = 1 := by simpa [pow_two] using hcTSq
  have hsEq : sT = (dT : T) * cT := by
    change sT = (sT * cT) * cT
    rw [mul_assoc, hcMul, mul_one]
  have hdcomm : Commute (dT : T) (xDsub : T) := by
    exact setLike_mul_comm
      (s := Dsub) dT.property xDsub.property
  have hcalc :
      sT * (xDsub : T) * sT⁻¹ = ((xDsub⁻¹ : Dsub) : T) := by
    calc
      sT * (xDsub : T) * sT⁻¹ =
          ((dT : T) * cT) * (xDsub : T) * ((dT : T) * cT)⁻¹ := by
        rw [← hsEq]
      _ = (dT : T) * (cT * (xDsub : T) * cT⁻¹) * (dT : T)⁻¹ := by
        group
      _ = (dT : T) * ((xDsub⁻¹ : Dsub) : T) * (dT : T)⁻¹ := by
        rw [hcInverts]
      _ = ((xDsub⁻¹ : Dsub) : T) := by
        have hdcommInv : Commute (dT : T) ((xDsub⁻¹ : Dsub) : T) := by
          simpa using hdcomm.inv_right
        rw [hdcommInv.eq]
        simp [mul_assoc]
  have hcalcG := congrArg (fun z : T => (z : G)) hcalc
  simpa [sT, xDsub, xDg] using hcalcG

private theorem xi1115_involution_uniqueFixedPoint
    {G Omega : Type*} [Group G] [MulAction G Omega] [Fintype Omega]
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (t : G) (htorder : orderOf t = 2) :
    ∃! x : Omega, t • x = x := by
  classical
  let sigma : Function.End Omega := fun x => t • x
  have htne : t ≠ 1 := (orderOf_eq_prime_iff.mp htorder).2
  have htsq : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  have hsigmasq : sigma ^ 2 = 1 := by
    funext x
    change t • (t • x) = x
    rw [← mul_smul, ← pow_two, htsq, one_smul]
  have hcardLe : Fintype.card (Function.fixedPoints sigma) ≤ 2 := by
    by_contra h
    have hlt : 2 < Fintype.card (Function.fixedPoints sigma) := by omega
    rcases Fintype.two_lt_card_iff.mp hlt with ⟨x, y, z, hxy, hxz, hyz⟩
    apply hatMostTwoFixedPoints t htne x y z
      (fun h => hxy (Subtype.ext h))
      (fun h => hxz (Subtype.ext h))
      (fun h => hyz (Subtype.ext h))
    exact ⟨x.property, y.property, z.property⟩
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod : Fintype.card Omega ≡
      Fintype.card (Function.fixedPoints sigma) [MOD 2] := by
    apply Equiv.Perm.card_fixedPoints_modEq (p := 2) (n := 1)
    simpa using hsigmasq
  have hcardEq : Fintype.card (Function.fixedPoints sigma) = 1 := by
    have hoddmod : Fintype.card Omega % 2 = 1 := Nat.odd_iff.mp hdegreeOdd
    change Fintype.card Omega % 2 =
      Fintype.card (Function.fixedPoints sigma) % 2 at hmod
    omega
  rw [Fintype.card_eq_one_iff] at hcardEq
  obtain ⟨x, hxuniq⟩ := hcardEq
  refine ⟨x, x.property, ?_⟩
  intro y hy
  exact congrArg Subtype.val (hxuniq ⟨y, hy⟩)

private theorem xi1115_exists_central_involution
    {F : Type*} [Group F] [Finite F]
    (hFne : Nontrivial F) (hF2 : IsPGroup 2 F) :
    ∃ z : Subgroup.center F, orderOf z = 2 := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Nontrivial F := hFne
  letI : Nontrivial (Subgroup.center F) := hF2.center_nontrivial
  have hZ2 : IsPGroup 2 (Subgroup.center F) :=
    hF2.to_subgroup (Subgroup.center F)
  obtain ⟨k, hkpos, hcard⟩ := hZ2.nontrivial_iff_card.mp inferInstance
  have hdvd : 2 ∣ Nat.card (Subgroup.center F) := by
    rw [hcard]
    exact dvd_pow_self 2 hkpos.ne'
  exact exists_prime_orderOf_dvd_card' 2 hdvd
private theorem xi1115_product_order_odd_of_involution_centralizers_inf_bot
    {G : Type*} [Group G] [Finite G]
    (t u : G) (htsq : t ^ 2 = 1) (husq : u ^ 2 = 1)
    (hcent : Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({u} : Set G) = ⊥) :
    Odd (orderOf (t * u)) := by
  apply Nat.not_even_iff_odd.mp
  intro heven
  obtain ⟨k, hk⟩ := heven
  have horderPos : 0 < orderOf (t * u) := orderOf_pos (t * u)
  have hkpos : 0 < k := by omega
  let r : G := t * u
  let z : G := r ^ k
  have hrorder : orderOf r = k + k := by
    simpa [two_mul] using hk
  have hklt : k < orderOf r := by omega
  have hz_ne : z ≠ 1 :=
    pow_ne_one_of_lt_orderOf hkpos.ne' hklt
  have hrpow : r ^ (k + k) = 1 := by
    rw [← hrorder]
    exact pow_orderOf_eq_one r
  have hzsq : z ^ 2 = 1 := by
    dsimp [z]
    rw [← pow_mul, show k * 2 = k + k by omega, hrpow]
  have hzinv : z⁻¹ = z := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hzsq
  have htinv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using htsq
  have huinv : u⁻¹ = u := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using husq
  have htr : t * r * t⁻¹ = r⁻¹ := by
    dsimp [r]
    rw [htinv, mul_inv_rev, htinv, huinv]
    have htt : t * t = 1 := by simpa [pow_two] using htsq
    simp [← mul_assoc, htt]
  have hsem : SemiconjBy t r r⁻¹ := by
    change t * r = r⁻¹ * t
    have htt : t * t = 1 := by simpa [pow_two] using htsq
    have h := congrArg (fun x : G => x * t) htr
    simpa [mul_assoc, htinv, htt] using h
  have htz : t * z * t⁻¹ = z⁻¹ := by
    have hp := hsem.pow_right k
    have hp' := congrArg (fun x : G => x * t⁻¹) hp.eq
    simpa [z, inv_pow, mul_assoc] using hp'
  have htz' : t * z * t⁻¹ = z := by rw [htz, hzinv]
  have hcommT : z * t = t * z := by
    have h := congrArg (fun x : G => x * t) htz'
    simpa [mul_assoc] using h.symm
  have hcommR : z * r = r * z :=
    (Commute.refl r).pow_left k
  have hut : u = t * r := by
    dsimp [r]
    have htt : t * t = 1 := by simpa [pow_two] using htsq
    rw [← mul_assoc, htt, one_mul]
  have hcommU : z * u = u * z := by
    rw [hut]
    calc
      z * (t * r) = (z * t) * r := (mul_assoc z t r).symm
      _ = (t * z) * r := by rw [hcommT]
      _ = t * (z * r) := mul_assoc t z r
      _ = t * (r * z) := by rw [hcommR]
      _ = (t * r) * z := (mul_assoc t r z).symm
  have hzmem : z ∈ Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({u} : Set G) := by
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr hcommT, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcommU
  have hzbot : z ∈ (⊥ : Subgroup G) := by simpa [hcent] using hzmem
  exact hz_ne (by simpa using hzbot)

private theorem xi1115_isConj_of_involutions_odd_product
    {G : Type*} [Group G]
    (t u : G) (htsq : t ^ 2 = 1) (husq : u ^ 2 = 1)
    (hodd : Odd (orderOf (t * u))) :
    IsConj t u := by
  rw [isConj_iff]
  obtain ⟨m, hm⟩ := hodd
  let r : G := t * u
  let k : ℕ := m + 1
  have htinv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using htsq
  have huinv : u⁻¹ = u := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using husq
  have htt : t * t = 1 := by simpa [pow_two] using htsq
  have hsem : SemiconjBy t r r⁻¹ := by
    change t * (t * u) = (t * u)⁻¹ * t
    rw [mul_inv_rev, htinv, huinv, ← mul_assoc, htt, one_mul,
      mul_assoc, htt, mul_one]
  have htrk : t * r ^ k = (r ^ k)⁻¹ * t := by
    have hp := hsem.pow_right k
    simpa [inv_pow] using hp.eq
  have hrpow : r ^ (2 * m + 1) = 1 := by
    have hp := pow_orderOf_eq_one r
    simpa [r, hm] using hp
  have htwoK : 2 * k = (2 * m + 1) + 1 := by
    dsimp [k]
    omega
  have hrTwoK : r ^ (2 * k) = r := by
    rw [htwoK, pow_succ, hrpow, one_mul]
  refine ⟨(r ^ k)⁻¹, ?_⟩
  calc
    (r ^ k)⁻¹ * t * ((r ^ k)⁻¹)⁻¹ = (r ^ k)⁻¹ * t * r ^ k := by simp
    _ = (t * r ^ k) * r ^ k := by rw [htrk]
    _ = t * r ^ (2 * k) := by
      rw [mul_assoc, ← pow_add, show k + k = 2 * k by omega]
    _ = t * r := by rw [hrTwoK]
    _ = u := by
      dsimp [r]
      rw [← mul_assoc, htt, one_mul]
/-- A normal subgroup of a Frobenius group with solvable kernel either lies in
that kernel or contains it. -/
private theorem xi1115_frobenius_normal_subgroup_le_kernel_or_kernel_le
    {H : Type*} [Group H] [Finite H]
    (F D N : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hN : N.Normal) (hF2 : IsPGroup 2 F) :
    N ≤ F ∨ F ≤ N := by
  by_cases hFN : F ≤ N
  · exact Or.inr hFN
  · left
    letI : N.Normal := hN
    have hFsolv : Group.IsSolvable F := by
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      letI : Group.IsNilpotent F := IsPGroup.isNilpotent hF2
      exact IsNilpotent.to_isSolvable
    exact lemma_3_2_a F D N hFrob hFsolv hFN

private theorem xi1115_frobeniusKernel_uniqueFixedPoint
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (z : F) (hzne : z ≠ 1) :
    ∀ c : Omega,
      ((((z : MulAction.stabilizer G a) : G) • c = c) ↔ c = a) := by
  intro c
  constructor
  · intro hzc
    by_contra hca
    let cSub : SubMulAction.ofStabilizer G a := ⟨c, hca⟩
    have hzcSub :
        (z : MulAction.stabilizer G a) • cSub = cSub := by
      exact Subtype.ext hzc
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hstab_multi :
        MulAction.IsMultiplyPretransitive
            (MulAction.stabilizer G a)
            (SubMulAction.ofStabilizer G a) 1 :=
      (SubMulAction.ofStabilizer.isMultiplyPretransitive
        (G := G) (a := a)).mp htwo
    have hpretrans :
        MulAction.IsPretransitive
          (MulAction.stabilizer G a)
          (SubMulAction.ofStabilizer G a) :=
      (MulAction.is_one_pretransitive_iff
        (G := MulAction.stabilizer G a)
        (α := SubMulAction.ofStabilizer G a)).mp hstab_multi
    have hregular :
        ∀ x y : SubMulAction.ofStabilizer G a,
          ∃! f : F, (f : MulAction.stabilizer G a) • x = y :=
      huppert_blackburn_XI_regular_of_isComplement_stabilizer
        hFrob.isComplement' hpretrans
    obtain ⟨k, _hk, hunique⟩ := hregular cSub cSub
    have hzk : z = k := hunique z hzcSub
    have honek : (1 : F) = k := hunique 1 (by simp)
    exact hzne (hzk.trans honek.symm)
  · intro hca
    rw [hca]
    exact (z : MulAction.stabilizer G a).property


private theorem xi1115_frobenius_not_mem_kernel_conjugate_mem_complement
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    {x : H} (hxnotF : x ∉ F) :
    ∃ a : F, ∃ r : D,
      (a : H)⁻¹ * x * (a : H) = (r : H) := by
  classical
  letI : F.Normal := hFrob.normal
  have hxSup : x ∈ F ⊔ D := by
    simp [hFrob.isComplement'.sup_eq_top]
  rcases (Subgroup.mem_sup_of_normal_left (s := F) (t := D) (x := x)).1 hxSup with
    ⟨k, hkF, r, hrD, hkr⟩
  let rD : D := ⟨r, hrD⟩
  have hrne : rD ≠ 1 := by
    intro hr1
    apply hxnotF
    rw [← hkr]
    have hr_eq : r = 1 := by
      simpa [rD] using congrArg Subtype.val hr1
    simp [hr_eq, hkF]
  have hcent : elementCentralizerIn F (rD : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob rD hrne
  let delta : F → F := fun a =>
    ⟨(a : H) * r * (a : H)⁻¹ * r⁻¹, by
      have hconjF : r * (a : H)⁻¹ * r⁻¹ ∈ F :=
        hFrob.normal.conj_mem ((a : H)⁻¹) (F.inv_mem a.2) r
      simpa [mul_assoc] using F.mul_mem a.2 hconjF⟩
  have hdelta_inj : Function.Injective delta := by
    intro a b hab
    have habH :
        (a : H) * r * (a : H)⁻¹ * r⁻¹ =
          (b : H) * r * (b : H)⁻¹ * r⁻¹ :=
      congrArg Subtype.val hab
    have hcomm :
        (b : H)⁻¹ * (a : H) * r =
          r * ((b : H)⁻¹ * (a : H)) := by
      have hab1 :
          (a : H) * r * (a : H)⁻¹ =
            (b : H) * r * (b : H)⁻¹ := by
        simpa [mul_assoc] using congrArg (fun t : H => t * r) habH
      have hab2 := congrArg (fun t : H => (b : H)⁻¹ * t * (a : H)) hab1
      simpa [mul_assoc] using hab2
    let c : F :=
      ⟨(b : H)⁻¹ * (a : H), F.mul_mem (F.inv_mem b.2) a.2⟩
    have hcCent : (c : H) ∈ elementCentralizerIn F (rD : H) := by
      refine ⟨c.2, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (by simpa [c, rD] using hcomm)
    have hcBot : (c : H) ∈ (⊥ : Subgroup H) := by
      simpa [hcent] using hcCent
    have hc_eq : (c : H) = 1 := by simpa using hcBot
    apply Subtype.ext
    have := congrArg (fun t : H => (b : H) * t) hc_eq
    simpa [c, mul_assoc] using this
  have hdelta_surj : Function.Surjective delta :=
    Finite.surjective_of_injective hdelta_inj
  rcases hdelta_surj ⟨k, hkF⟩ with ⟨a, ha⟩
  have haH : (a : H) * r * (a : H)⁻¹ * r⁻¹ = k :=
    congrArg Subtype.val ha
  have hconj_x : (a : H)⁻¹ * x * (a : H) = r := by
    rw [← hkr]
    have hk_eq : k = (a : H) * r * (a : H)⁻¹ * r⁻¹ := haH.symm
    rw [hk_eq]
    group
  exact ⟨a, rD, by simpa [rD] using hconj_x⟩

/-- The centralizer in a Frobenius group of a nonidentity kernel element is
contained in the kernel. -/
private theorem xi1115_frobenius_kernel_centralizer_le
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (z : F) (hzne : z ≠ 1) :
    Subgroup.centralizer ({(z : H)} : Set H) ≤ F := by
  intro x hx
  by_contra hxF
  obtain ⟨a, r, hconj⟩ :=
    xi1115_frobenius_not_mem_kernel_conjugate_mem_complement
      F D hFrob hxF
  let za : F :=
    ⟨(a : H)⁻¹ * (z : H) * (a : H), by
      simpa using hFrob.normal.conj_mem (z : H) z.property (a : H)⁻¹⟩
  have hza_ne : za ≠ 1 := by
    intro hza
    apply hzne
    apply Subtype.ext
    have hzaH : (a : H)⁻¹ * (z : H) * (a : H) = 1 :=
      congrArg Subtype.val hza
    have := congrArg (fun y : H => (a : H) * y * (a : H)⁻¹) hzaH
    simpa [za, mul_assoc] using this
  have hxcomm : x * (z : H) = (z : H) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hrcomm : (r : H) * (za : H) = (za : H) * (r : H) := by
    rw [← hconj]
    dsimp [za]
    calc
      (a : H)⁻¹ * x * (a : H) * ((a : H)⁻¹ * (z : H) * (a : H)) =
          (a : H)⁻¹ * (x * (z : H)) * (a : H) := by group
      _ = (a : H)⁻¹ * ((z : H) * x) * (a : H) := by rw [hxcomm]
      _ = (a : H)⁻¹ * (z : H) * (a : H) *
          ((a : H)⁻¹ * x * (a : H)) := by group
  have hzaCent : (za : H) ∈ elementCentralizerIn F (r : H) :=
    ⟨za.property, Subgroup.mem_centralizer_singleton_iff.mpr hrcomm.symm⟩
  have hrne : r ≠ 1 := by
    intro hr
    have hrH : (r : H) = 1 := congrArg Subtype.val hr
    have hconjOne : (a : H)⁻¹ * x * (a : H) = 1 := hconj.trans hrH
    have := congrArg (fun y : H => (a : H) * y * (a : H)⁻¹) hconjOne
    have hxone : x = 1 := by simpa [mul_assoc] using this
    exact hxF (by simp [hxone])
  have hcent : elementCentralizerIn F (r : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob r hrne
  have hzaOne : za = 1 := by
    apply Subtype.ext
    have : (za : H) ∈ (⊥ : Subgroup H) := by simpa [hcent] using hzaCent
    simpa using this
  exact hza_ne hzaOne

private theorem xi1115_frobeniusKernel_ambient_centralizer_le
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (z : F) (hzne : z ≠ 1) :
    Subgroup.centralizer
        ({(((z : MulAction.stabilizer G a) : G))} : Set G) ≤
      F.map (MulAction.stabilizer G a).subtype := by
  intro x hx
  have hxcomm :
      x * (((z : MulAction.stabilizer G a) : G)) =
        (((z : MulAction.stabilizer G a) : G)) * x :=
    Subgroup.mem_centralizer_singleton_iff.mp hx
  have hzfixXa :
      (((z : MulAction.stabilizer G a) : G)) • (x • a) = x • a := by
    calc
      (((z : MulAction.stabilizer G a) : G)) • (x • a) =
          ((((z : MulAction.stabilizer G a) : G)) * x) • a := by
            rw [mul_smul]
      _ = (x * (((z : MulAction.stabilizer G a) : G))) • a := by
        rw [hxcomm]
      _ = x • ((((z : MulAction.stabilizer G a) : G)) • a) := by
        rw [mul_smul]
      _ = x • a := by rw [(z : MulAction.stabilizer G a).property]
  have hxa : x • a = a :=
    (xi1115_frobeniusKernel_uniqueFixedPoint
      htwo a b hab F hFrob z hzne (x • a)).mp hzfixXa
  let xa : MulAction.stabilizer G a := ⟨x, hxa⟩
  have hxaCent :
      xa ∈ Subgroup.centralizer
        ({(z : MulAction.stabilizer G a)} : Set (MulAction.stabilizer G a)) := by
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    apply Subtype.ext
    exact hxcomm
  have hxaF : xa ∈ F :=
    xi1115_frobenius_kernel_centralizer_le
      F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))
      hFrob z hzne hxaCent
  exact ⟨xa, hxaF, rfl⟩
private theorem xi1115_frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
    {H X : Type*} [Group H] [Finite H] [MulAction H X]
    (htrans : MulAction.IsPretransitive H X) (a : X)
    (F : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer H a)) (x : H) :
    x ∈ F ↔ x = 1 ∨ ∀ y : X, x • y ≠ y := by
  letI : MulAction.IsPretransitive H X := htrans
  constructor
  · intro hx
    by_cases hxone : x = 1
    · exact Or.inl hxone
    right
    intro y hxy
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq H a y
    have hfix : (g⁻¹ * x * g) • a = a := by
      calc
        (g⁻¹ * x * g) • a = g⁻¹ • (x • (g • a)) := by
          simp only [mul_smul]
        _ = g⁻¹ • (x • y) := by rw [hg]
        _ = g⁻¹ • y := by rw [hxy]
        _ = a := by rw [← hg, inv_smul_smul]
    have hmemD : g⁻¹ * x * g ∈ MulAction.stabilizer H a :=
      MulAction.mem_stabilizer_iff.mpr hfix
    have hmemF : g⁻¹ * x * g ∈ F := by
      simpa using hFrob.normal.conj_mem x hx g⁻¹
    have hconjOne : g⁻¹ * x * g = 1 :=
      Subgroup.disjoint_def.mp hFrob.isComplement'.disjoint hmemF hmemD
    apply hxone
    have := congrArg (fun z : H => g * z * g⁻¹) hconjOne
    simpa [mul_assoc] using this
  · rintro (rfl | hfree)
    · simp
    by_contra hxF
    obtain ⟨f, r, hconj⟩ :=
      xi1115_frobenius_not_mem_kernel_conjugate_mem_complement
        F (MulAction.stabilizer H a) hFrob hxF
    have hxEq : x = (f : H) * (r : H) * (f : H)⁻¹ := by
      have := congrArg (fun z : H => (f : H) * z * (f : H)⁻¹) hconj
      simpa [mul_assoc] using this
    apply hfree ((f : H) • a)
    calc
      x • ((f : H) • a) =
          ((f : H) * (r : H) * (f : H)⁻¹) • ((f : H) • a) := by
            rw [hxEq]
      _ = (f : H) • ((r : H) • a) := by
        simp only [mul_smul, inv_smul_smul]
      _ = (f : H) • a := by
        rw [MulAction.mem_stabilizer_iff.mp r.property]


private theorem xi1115_involution_mem_frobeniusKernel_of_fixedPoint
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (t : G) (htorder : orderOf t = 2) (htfix : t • a = a) :
    (⟨t, htfix⟩ : MulAction.stabilizer G a) ∈ F := by
  letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let tA : MulAction.stabilizer G a := ⟨t, htfix⟩
  let bA : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  have hstabMulti :
      MulAction.IsMultiplyPretransitive
        (MulAction.stabilizer G a) (SubMulAction.ofStabilizer G a) 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  have hpretrans :
      MulAction.IsPretransitive
        (MulAction.stabilizer G a) (SubMulAction.ofStabilizer G a) :=
    (MulAction.is_one_pretransitive_iff
      (G := MulAction.stabilizer G a)
      (α := SubMulAction.ofStabilizer G a)).mp hstabMulti
  apply (xi1115_frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
    hpretrans bA F (by simpa [bA] using hFrob) tA).mpr
  right
  intro y hty
  obtain ⟨c, hcfix, hcunique⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints t htorder
  have hyfix : t • (y : Omega) = (y : Omega) :=
    congrArg Subtype.val hty
  have hyc : (y : Omega) = c := hcunique (y : Omega) hyfix
  have hac : a = c := hcunique a htfix
  exact y.property (hyc.trans hac.symm)
private theorem xi1115_frobenius_kernel_map_normal_of_ambient_normal
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (N : Subgroup G) (hN : N.Normal) (a : X)
    (K : Subgroup N) (htrans : MulAction.IsPretransitive N X)
    (hFrob : IsFrobeniusGroupWithKernelComplement K
      (MulAction.stabilizer N a)) :
    (K.map N.subtype).Normal := by
  let Kmap : Subgroup G := K.map N.subtype
  change Kmap.Normal
  refine ⟨?_⟩
  intro x hx g
  rcases hx with ⟨k, hkK, hkx⟩
  have hxN : x ∈ N := by
    rw [← hkx]
    exact k.property
  let yN : N := ⟨g * x * g⁻¹, hN.conj_mem x hxN g⟩
  have hyK : yN ∈ K := by
    apply (xi1115_frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
      htrans a K hFrob yN).2
    rcases (xi1115_frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
      htrans a K hFrob k).1 hkK with hkone | hkfree
    · left
      apply Subtype.ext
      have hxone : x = 1 := by
        calc
          x = (k : G) := hkx.symm
          _ = 1 := by simpa using congrArg Subtype.val hkone
      simp [yN, hxone]
    · right
      intro z hyfix
      apply hkfree (g⁻¹ • z)
      have hyfixG : (g * x * g⁻¹) • z = z := by
        simpa [yN] using hyfix
      have hkxG : (k : G) = x := hkx
      change (k : G) • (g⁻¹ • z) = g⁻¹ • z
      rw [hkxG]
      calc
        x • (g⁻¹ • z) = (x * g⁻¹) • z := by rw [mul_smul]
        _ = (g⁻¹ * (g * x * g⁻¹)) • z := by group
        _ = g⁻¹ • ((g * x * g⁻¹) • z) := by rw [mul_smul]
        _ = g⁻¹ • z := by rw [hyfixG]
  exact ⟨yN, hyK, rfl⟩


private theorem xi1115_distinctFixedPoint_involution_centralizers_inf_eq_bot
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (t u : G) (htorder : orderOf t = 2) (huorder : orderOf u = 2)
    (x y : Omega) (hxy : x ≠ y)
    (htfix : t • x = x) (hufix : u • y = y) :
    Subgroup.centralizer ({t} : Set G) ⊓
      Subgroup.centralizer ({u} : Set G) = ⊥ := by
  obtain ⟨Fx, hFx⟩ :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
      htwo hatMostTwoFixedPoints hnoRegularNormal x y hxy
  obtain ⟨Fy, hFy⟩ :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_exists
      htwo hatMostTwoFixedPoints hnoRegularNormal y x hxy.symm
  let tx : MulAction.stabilizer G x := ⟨t, htfix⟩
  let uy : MulAction.stabilizer G y := ⟨u, hufix⟩
  have htxFx : tx ∈ Fx :=
    xi1115_involution_mem_frobeniusKernel_of_fixedPoint
      htwo hdegreeOdd hatMostTwoFixedPoints
      x y hxy Fx hFx t htorder htfix
  have huyFy : uy ∈ Fy :=
    xi1115_involution_mem_frobeniusKernel_of_fixedPoint
      htwo hdegreeOdd hatMostTwoFixedPoints
      y x hxy.symm Fy hFy u huorder hufix
  let tFx : Fx := ⟨tx, htxFx⟩
  let uFy : Fy := ⟨uy, huyFy⟩
  have htne : t ≠ 1 := (orderOf_eq_prime_iff.mp htorder).2
  have hune : u ≠ 1 := (orderOf_eq_prime_iff.mp huorder).2
  have htFxne : tFx ≠ 1 := by
    intro h
    apply htne
    exact congrArg (fun z : Fx => (((z : MulAction.stabilizer G x) : G))) h
  have huFyne : uFy ≠ 1 := by
    intro h
    apply hune
    exact congrArg (fun z : Fy => (((z : MulAction.stabilizer G y) : G))) h
  have hCt :
      Subgroup.centralizer ({t} : Set G) ≤
        Fx.map (MulAction.stabilizer G x).subtype := by
    simpa [tFx, tx] using
      xi1115_frobeniusKernel_ambient_centralizer_le
        htwo x y hxy Fx hFx tFx htFxne
  have hCu :
      Subgroup.centralizer ({u} : Set G) ≤
        Fy.map (MulAction.stabilizer G y).subtype := by
    simpa [uFy, uy] using
      xi1115_frobeniusKernel_ambient_centralizer_le
        htwo y x hxy.symm Fy hFy uFy huFyne
  rw [eq_bot_iff]
  intro g hg
  have hgFx := hCt hg.1
  have hgFy := hCu hg.2
  rcases hgFx with ⟨gx, hgxFx, hgx⟩
  rcases hgFy with ⟨gy, hgyFy, hgy⟩
  have hgFixY : g • y = y := by
    rw [← hgy]
    exact gy.property
  have hgxD :
      gx ∈ MulAction.stabilizer (MulAction.stabilizer G x)
        (⟨y, hxy.symm⟩ : SubMulAction.ofStabilizer G x) := by
    apply MulAction.mem_stabilizer_iff.mpr
    apply Subtype.ext
    change ((MulAction.stabilizer G x).subtype gx) • y = y
    rw [hgx]
    exact hgFixY
  have hgxBot : gx ∈ (⊥ : Subgroup (MulAction.stabilizer G x)) :=
    Subgroup.disjoint_def.mp hFx.isComplement'.disjoint hgxFx hgxD
  have hgxOne : gx = 1 := by
    apply Subtype.ext
    simpa using hgxBot
  have hgOne : g = 1 := by
    rw [← hgx]
    exact congrArg Subtype.val hgxOne
  simp [hgOne]

private theorem xi1115_distinctFixedPoint_involutions_isConj
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (t u : G) (htorder : orderOf t = 2) (huorder : orderOf u = 2)
    (x y : Omega) (hxy : x ≠ y)
    (htfix : t • x = x) (hufix : u • y = y) :
    IsConj t u := by
  have htsq : t ^ 2 = 1 := by
    rw [← htorder]
    exact pow_orderOf_eq_one t
  have husq : u ^ 2 = 1 := by
    rw [← huorder]
    exact pow_orderOf_eq_one u
  have hcent :=
    xi1115_distinctFixedPoint_involution_centralizers_inf_eq_bot
      htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
      t u htorder huorder x y hxy htfix hufix
  exact xi1115_isConj_of_involutions_odd_product t u htsq husq
    (xi1115_product_order_odd_of_involution_centralizers_inf_bot
      t u htsq husq hcent)
private theorem xi1115_all_involutions_isConj
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (s : G) (hsorder : orderOf s = 2) (hsa : s • a = b) :
    ∀ t : G, orderOf t = 2 → IsConj t s := by
  letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨c, hscfix, _hcunique⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints s hsorder
  have hca : c ≠ a := by
    intro hca
    have hsafix : s • a = a := by simpa [hca] using hscfix
    exact hab (hsafix.symm.trans hsa)
  intro t htorder
  obtain ⟨x, htxfix, _hxunique⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints t htorder
  by_cases hxc : x = c
  · obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G c a
    let v : G := g * s * g⁻¹
    have hsv : IsConj s v := by
      rw [isConj_iff]
      exact ⟨g, rfl⟩
    have hssq : s ^ 2 = 1 := by
      rw [← hsorder]
      exact pow_orderOf_eq_one s
    have hsne : s ≠ 1 := (orderOf_eq_prime_iff.mp hsorder).2
    have hvsq : v ^ 2 = 1 := by
      dsimp [v]
      calc
        (g * s * g⁻¹) ^ 2 = g * s ^ 2 * g⁻¹ := by
          rw [pow_two, pow_two]
          group
        _ = 1 := by rw [hssq]; simp
    have hvne : v ≠ 1 := by
      intro hv
      apply hsne
      have h := congrArg (fun z : G => g⁻¹ * z * g) hv
      simpa [v, mul_assoc] using h
    have hvorder : orderOf v = 2 := orderOf_eq_prime hvsq hvne
    have hvfix : v • a = a := by
      dsimp [v]
      calc
        (g * s * g⁻¹) • a = g • (s • (g⁻¹ • a)) := by simp only [mul_smul]
        _ = g • (s • c) := by rw [← hg, inv_smul_smul]
        _ = g • c := by rw [hscfix]
        _ = a := hg
    have htfixC : t • c = c := by simpa [hxc] using htxfix
    have htv : IsConj t v :=
      xi1115_distinctFixedPoint_involutions_isConj
        htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
        t v htorder hvorder c a hca htfixC hvfix
    exact htv.trans hsv.symm
  · exact xi1115_distinctFixedPoint_involutions_isConj
      htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
      t s htorder hsorder x c hxc htxfix hscfix
private theorem xi1115_sameFixedPoint_involutions_commute
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (t u : G) (htorder : orderOf t = 2) (huorder : orderOf u = 2)
    (x : Omega) (htfix : t • x = x) (hufix : u • x = x) :
    Commute t u := by
  letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo
  letI : MulAction.IsPretransitive G Omega :=
    MulAction.isPretransitive_of_is_two_pretransitive
  obtain ⟨k, hkx⟩ := MulAction.exists_smul_eq G x a
  let t' : G := k * t * k⁻¹
  let u' : G := k * u * k⁻¹
  have hkinva : k⁻¹ • a = x := by
    calc
      k⁻¹ • a = k⁻¹ • (k • x) := by rw [hkx]
      _ = x := inv_smul_smul k x
  have ht'fix : t' • a = a := by
    dsimp [t']
    calc
      (k * t * k⁻¹) • a = k • (t • (k⁻¹ • a)) := by
        simp only [mul_smul]
      _ = k • (t • x) := by rw [hkinva]
      _ = k • x := by rw [htfix]
      _ = a := hkx
  have hu'fix : u' • a = a := by
    dsimp [u']
    calc
      (k * u * k⁻¹) • a = k • (u • (k⁻¹ • a)) := by
        simp only [mul_smul]
      _ = k • (u • x) := by rw [hkinva]
      _ = k • x := by rw [hufix]
      _ = a := hkx
  have ht'order : orderOf t' = 2 := by
    exact ((MulAut.conj k).orderOf_eq t).trans htorder
  have hu'order : orderOf u' = 2 := by
    exact ((MulAut.conj k).orderOf_eq u).trans huorder
  let tH : MulAction.stabilizer G a := ⟨t', ht'fix⟩
  let uH : MulAction.stabilizer G a := ⟨u', hu'fix⟩
  have htFmem : tH ∈ F :=
    xi1115_involution_mem_frobeniusKernel_of_fixedPoint
      htwo hdegreeOdd hatMostTwoFixedPoints a b hab F hFrob
      t' ht'order ht'fix
  have huFmem : uH ∈ F :=
    xi1115_involution_mem_frobeniusKernel_of_fixedPoint
      htwo hdegreeOdd hatMostTwoFixedPoints a b hab F hFrob
      u' hu'order hu'fix
  let tF : F := ⟨tH, htFmem⟩
  let uF : F := ⟨uH, huFmem⟩
  have htForder : orderOf tF = 2 := by
    calc
      orderOf tF = orderOf tH := Subgroup.orderOf_mk _ _
      _ = orderOf t' := Subgroup.orderOf_mk _ _
      _ = 2 := ht'order
  have htFinv : PFAppendixIII.IsInvolution tF :=
    (orderOf_eq_prime_iff.mp htForder).symm
  have hinvolutions := (Higman.theorem1_involutions_center hFSuzuki).1
  have htFcenter : tF ∈ Subgroup.center F := by
    exact ((Set.ext_iff.mp hinvolutions tF).mp htFinv).1
  have hcommF : tF * uF = uF * tF :=
    (Subgroup.mem_center_iff.mp htFcenter uF).symm
  have hcommConj : t' * u' = u' * t' := by
    simpa [tF, uF, tH, uH] using congrArg
      (fun z : F => (((z : F) : MulAction.stabilizer G a) : G)) hcommF
  have hback := congrArg (fun z : G => k⁻¹ * z * k) hcommConj
  simpa [Commute, SemiconjBy, t', u', mul_assoc] using hback
private theorem xi1115_stronglyReal_sq_ne_one_order_odd
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (x : G) (hxStrong : PFAppendixIII.IsStronglyReal x)
    (hxsq : x ^ 2 ≠ 1) :
    Odd (orderOf x) := by
  rcases hxStrong with ⟨t, u, htInv, huInv, rfl⟩
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime htInv.sq_eq_one htInv.ne_one
  have huorder : orderOf u = 2 :=
    orderOf_eq_prime huInv.sq_eq_one huInv.ne_one
  obtain ⟨p, htfix, _htuniq⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints t htorder
  obtain ⟨q, hufix, _huuniq⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints u huorder
  by_cases hpq : p = q
  · subst q
    have hcomm : Commute t u :=
      xi1115_sameFixedPoint_involutions_commute
        htwo hdegreeOdd hatMostTwoFixedPoints a b hab F hFrob hFSuzuki
        t u htorder huorder p htfix hufix
    have htt : t * t = 1 := by simpa [pow_two] using htInv.sq_eq_one
    have huu : u * u = 1 := by simpa [pow_two] using huInv.sq_eq_one
    have hprodSq : (t * u) ^ 2 = 1 := by
      rw [pow_two]
      calc
        (t * u) * (t * u) = t * (u * t) * u := by group
        _ = t * (t * u) * u := by rw [hcomm.eq.symm]
        _ = (t * t) * (u * u) := by group
        _ = 1 := by rw [htt, huu, one_mul]
    exact (hxsq hprodSq).elim
  · have hcent :=
      xi1115_distinctFixedPoint_involution_centralizers_inf_eq_bot
        htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
        t u htorder huorder p q hpq htfix hufix
    exact xi1115_product_order_odd_of_involution_centralizers_inf_bot
      t u htInv.sq_eq_one huInv.sq_eq_one hcent
private theorem xi1115_frobeniusKernel_involutions_D_orbit
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (s : G) (hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s) :
    ∃ z : F,
      orderOf z = 2 ∧ z ∈ Subgroup.center F ∧
        ∀ w : F, orderOf w = 2 →
          ∃! d : MulAction.stabilizer (MulAction.stabilizer G a)
              (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
            (d : MulAction.stabilizer G a) *
                (z : MulAction.stabilizer G a) *
              (d : MulAction.stabilizer G a)⁻¹ =
                (w : MulAction.stabilizer G a) := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  letI : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).mpr hFrob.kernel_ne_bot
  obtain ⟨zC, hzCorder⟩ :=
    xi1115_exists_central_involution (F := F) inferInstance hF2
  let z : F := (zC : F)
  have hzorder : orderOf z = 2 := by
    calc
      orderOf z = orderOf (zC : F) := rfl
      _ = orderOf zC := (Subgroup.orderOf_coe (zC : Subgroup.center F))
      _ = 2 := hzCorder
  have hzcenter : z ∈ Subgroup.center F := zC.property
  refine ⟨z, hzorder, hzcenter, ?_⟩
  intro w hworder
  have hzorderG : orderOf (((z : F) : H) : G) = 2 := by
    simpa [Subgroup.orderOf_mk] using hzorder
  have hworderG : orderOf (((w : F) : H) : G) = 2 := by
    simpa [Subgroup.orderOf_mk] using hworder
  have hzwConj :
      IsConj (((z : F) : H) : G) (((w : F) : H) : G) :=
    (hallInvolutionsConj (((z : F) : H) : G) hzorderG).trans
      (hallInvolutionsConj (((w : F) : H) : G) hworderG).symm
  obtain ⟨g, hg⟩ := isConj_iff.mp hzwConj
  have hzfixGa :
      (((z : F) : H) : G) • (g⁻¹ • a) = g⁻¹ • a := by
    calc
      (((z : F) : H) : G) • (g⁻¹ • a) =
          g⁻¹ • ((g * (((z : F) : H) : G) * g⁻¹) • a) := by
            simp only [mul_smul]
            rw [inv_smul_smul]
      _ = g⁻¹ • ((((w : F) : H) : G) • a) := by rw [hg]
      _ = g⁻¹ • a := by rw [(w : H).property]
  have hzneq : z ≠ 1 := (orderOf_eq_prime_iff.mp hzorder).2
  have hginvFix : g⁻¹ • a = a :=
    (xi1115_frobeniusKernel_uniqueFixedPoint
      htwo a b hab F hFrob z hzneq (g⁻¹ • a)).mp hzfixGa
  have hgfix : g • a = a := by
    have h := congrArg (fun x : Omega => g • x) hginvFix
    simpa using h.symm
  let gH : H := ⟨g, hgfix⟩
  letI : F.Normal := hFrob.normal
  have hgSup : gH ∈ F ⊔ D := by
    rw [show F ⊔ D = ⊤ by simpa [D] using hFrob.isComplement'.sup_eq_top]
    simp
  rcases (Subgroup.mem_sup_of_normal_left
    (s := F) (t := D) (x := gH)).mp hgSup with
    ⟨k, hkF, d, hdD, hkd⟩
  let kF : F := ⟨k, hkF⟩
  let dD : D := ⟨d, hdD⟩
  let zd : F :=
    ⟨d * (z : H) * d⁻¹, by
      simpa using hFrob.normal.conj_mem (z : H) z.property d⟩
  have hzdCenter : zd ∈ Subgroup.center F := by
    rw [Subgroup.mem_center_iff]
    intro f
    let f' : F :=
      ⟨d⁻¹ * (f : H) * d, by
        simpa using hFrob.normal.conj_mem (f : H) f.property d⁻¹⟩
    have hcomm : (f' : F) * z = z * f' :=
      (Subgroup.mem_center_iff.mp hzcenter) f'
    apply Subtype.ext
    have hcommH := congrArg (fun q : F => (q : H)) hcomm
    dsimp [f', zd] at hcommH ⊢
    have h := congrArg (fun q : H => d * q * d⁻¹) hcommH
    simpa [mul_assoc] using h
  have hkComm : k * (zd : H) = (zd : H) * k := by
    have := (Subgroup.mem_center_iff.mp hzdCenter) kF
    exact congrArg (fun q : F => (q : H)) this
  have hgConjH : gH * (z : H) * gH⁻¹ = (w : H) := by
    apply Subtype.ext
    exact hg
  have hdConj : d * (z : H) * d⁻¹ = (w : H) := by
    calc
      d * (z : H) * d⁻¹ = (zd : H) := rfl
      _ = k * (zd : H) * k⁻¹ := by
        rw [hkComm]
        simp [mul_assoc]
      _ = (k * d) * (z : H) * (k * d)⁻¹ := by
        dsimp [zd]
        group
      _ = gH * (z : H) * gH⁻¹ := by rw [hkd]
      _ = (w : H) := hgConjH
  refine ⟨dD, by simpa [D, dD] using hdConj, ?_⟩
  intro e he
  let q : D := e⁻¹ * dD
  have hqConj :
      (q : H) * (z : H) * (q : H)⁻¹ = (z : H) := by
    have he' :
        (e : H) * (z : H) * (e : H)⁻¹ = (w : H) := by
      simpa [D] using he
    have hd' :
        (dD : H) * (z : H) * (dD : H)⁻¹ = (w : H) := by
      simpa [D, dD] using hdConj
    dsimp [q]
    calc
      ((e : H)⁻¹ * (dD : H)) * (z : H) *
          ((e : H)⁻¹ * (dD : H))⁻¹ =
            (e : H)⁻¹ * ((dD : H) * (z : H) * (dD : H)⁻¹) *
              (e : H) := by group
      _ = (e : H)⁻¹ * (w : H) * (e : H) := by rw [hd']
      _ = (z : H) := by
        have h := congrArg (fun r : H => (e : H)⁻¹ * r * (e : H)) he'
        simpa [mul_assoc] using h.symm
  have hqComm : (q : H) * (z : H) = (z : H) * (q : H) := by
    have h := congrArg (fun r : H => r * (q : H)) hqConj
    simpa [mul_assoc] using h
  have hqCent :
      (q : H) ∈ Subgroup.centralizer ({(z : H)} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hqComm
  have hqF : (q : H) ∈ F :=
    xi1115_frobenius_kernel_centralizer_le F D
      (by simpa [D] using hFrob) z hzneq hqCent
  have hqBot : (q : H) ∈ (⊥ : Subgroup H) :=
    Subgroup.disjoint_def.mp hFrob.isComplement'.disjoint hqF q.property
  have hqOne : q = 1 := by
    apply Subtype.ext
    simpa using hqBot
  apply Subtype.ext
  have hqOneH := congrArg (fun r : D => (r : H)) hqOne
  dsimp [q] at hqOneH
  have h := congrArg (fun r : H => (e : H) * r) hqOneH
  simpa [mul_assoc] using h.symm
private theorem xi1115_normal_stabilizer_contains_frobeniusKernel
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    let H := MulAction.stabilizer G a
    F ≤ N.comap H.subtype := by
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let Na : Subgroup H := N.comap H.subtype
  change F ≤ Na
  letI : N.Normal := hNnormal
  letI : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  letI : MulAction.IsQuasiPreprimitive G X :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints N X ≠ Set.univ := by
    intro hfixed
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hn_one : n = 1 :=
      (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X)) n (by
        intro x
        have hx : x ∈ MulAction.fixedPoints N X := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp hx ⟨n, hn⟩)
    exact Subgroup.mem_bot.mpr hn_one
  have hNtrans : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  have hNaNormal : Na.Normal := by
    simpa [Na] using hNnormal.comap H.subtype
  rcases xi1115_frobenius_normal_subgroup_le_kernel_or_kernel_le
      F D Na (by simpa [D] using hFrob) hNaNormal hF2 with hNaF | hFNa
  · exfalso
    let R := MulAction.stabilizer N a
    have hRne : R ≠ ⊥ := by
      intro hRbot
      apply hno_regular_normal
      refine ⟨N, hNnormal, hNne, ?_⟩
      have hcomp : (⊤ : Subgroup N).IsComplement' R := by
        rw [hRbot]
        exact Subgroup.isComplement'_top_bot
      have hregularTop :=
        huppert_blackburn_XI_regular_of_isComplement_stabilizer
          (a := a) hcomp hNtrans
      intro x y
      obtain ⟨r, hr, hrunique⟩ := hregularTop x y
      refine ⟨(r : N), by
        simpa [MulAction.subgroup_smul_def] using hr
      , ?_⟩
      intro n hn
      let nTop : (⊤ : Subgroup N) := ⟨n, trivial⟩
      have hnTop : (nTop : N) • x = y := by simpa [nTop, Subtype.coe_mk] using hn
      have heq : nTop = r := hrunique nTop hnTop
      exact congrArg Subtype.val heq
    have hRproper : R ≠ ⊤ := by
      intro hRtop
      obtain ⟨n, hn⟩ := hNtrans.exists_smul_eq a b
      have hnR : n ∈ R := by rw [hRtop]; simp
      have hfix : n • a = a := MulAction.mem_stabilizer_iff.mp hnR
      exact hab (hfix.symm.trans hn)
    let rToH : R → H := fun r =>
      ⟨((r : N) : G), MulAction.mem_stabilizer_iff.mpr (by
        simpa using MulAction.mem_stabilizer_iff.mp r.property)⟩
    have hRtoF : ∀ r : R, rToH r ∈ F := by
      intro r
      apply hNaF
      change ((rToH r : H) : G) ∈ N
      exact (r : N).property
    have hRTI : ∀ g : N, g ∉ R → Disjoint R (R.conjBy g) := by
      intro g hgR
      rw [Subgroup.disjoint_def]
      intro x hxR hxconj
      by_contra hxne
      let xF : F := ⟨rToH ⟨x, hxR⟩, hRtoF ⟨x, hxR⟩⟩
      have hxFne : xF ≠ 1 := by
        intro hxone
        apply hxne
        apply Subtype.ext
        simpa [xF, rToH] using
          congrArg Subtype.val (congrArg Subtype.val hxone)
      rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj
      rcases hxconj with ⟨r, hrR, hrx⟩
      have hxfixga : ((x : N) : G) • (((g : N) : G) • a) =
          ((g : N) : G) • a := by
        have hrfix : (r : N) • a = a :=
          MulAction.mem_stabilizer_iff.mp hrR
        have hxval : (x : N) = g * r * g⁻¹ := hrx.symm
        have hxvalG : ((x : N) : G) =
            ((g : N) : G) * ((r : N) : G) * ((g : N) : G)⁻¹ := by
          exact congrArg Subtype.val hxval
        have hrfixG : ((r : N) : G) • a = a := by simpa using hrfix
        calc
          ((x : N) : G) • (((g : N) : G) • a) =
              (((g : N) : G) * ((r : N) : G) * ((g : N) : G)⁻¹) •
                (((g : N) : G) • a) := by rw [hxvalG]
          _ = ((g : N) : G) • (((r : N) : G) • a) := by
            simp only [mul_smul, inv_smul_smul]
          _ = ((g : N) : G) • a := by rw [hrfixG]
      have hga : ((g : N) : G) • a = a :=
        (xi1115_frobeniusKernel_uniqueFixedPoint
          htwo a b hab F hFrob xF hxFne (((g : N) : G) • a)).mp (by simpa [xF, rToH] using hxfixga)
      apply hgR
      exact MulAction.mem_stabilizer_iff.mpr (by simpa using hga)
    obtain ⟨K, hKFrob⟩ :=
      Suzuki.VI.suzuki_ch6_theorem_2_3 R hRne hRproper hRTI
    let Kmap : Subgroup G := K.map N.subtype
    have hKmapNormal : Kmap.Normal := by
      simpa [Kmap] using
        xi1115_frobenius_kernel_map_normal_of_ambient_normal
          N hNnormal a K hNtrans hKFrob
    have hKmapNe : Kmap ≠ ⊥ := by
      intro hKmapBot
      apply hKFrob.kernel_ne_bot
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := K) (f := N.subtype) N.subtype_injective).mp
          (by simpa [Kmap] using hKmapBot)
    apply hno_regular_normal
    refine ⟨Kmap, hKmapNormal, hKmapNe, ?_⟩
    have hKregular :=
      huppert_blackburn_XI_regular_of_isComplement_stabilizer
        (a := a) hKFrob.isComplement' hNtrans
    intro x y
    obtain ⟨k, hk, hkunique⟩ := hKregular x y
    let kg : Kmap := ⟨((k : N) : G), ⟨(k : N), k.property, rfl⟩⟩
    refine ⟨kg, by simpa [kg] using hk, ?_⟩
    intro z hz
    rcases z.property with ⟨n, hnK, hnz⟩
    let nK : K := ⟨n, hnK⟩
    have hnact : (nK : N) • x = y := by
      have hnzG : ((nK : N) : G) = (z : G) := by
        simpa [nK] using hnz
      calc
        (nK : N) • x = ((nK : N) : G) • x := rfl
        _ = (z : G) • x := by rw [hnzG]
        _ = y := hz
    have hnk : nK = k := hkunique nK hnact
    apply Subtype.ext
    calc
      (z : G) = (n : G) := hnz.symm
      _ = ((k : N) : G) := by rw [show n = (k : N) from congrArg Subtype.val hnk]
      _ = (kg : G) := rfl
  · exact hFNa


private theorem xi1115_nontrivial_normal_is_two_pretransitive
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    MulAction.IsMultiplyPretransitive N X 2 := by
  let H := MulAction.stabilizer G a
  letI : N.Normal := hNnormal
  letI : MulAction.IsPreprimitive G X :=
    MulAction.isPreprimitive_of_is_two_pretransitive htwo
  letI : MulAction.IsQuasiPreprimitive G X :=
    MulAction.IsPreprimitive.isQuasiPreprimitive
  have hfixed_ne_univ : MulAction.fixedPoints N X ≠ Set.univ := by
    intro hfixed
    apply hNne
    rw [eq_bot_iff]
    intro n hn
    have hn_one : n = 1 :=
      (faithfulSMul_iff.mp (inferInstance : FaithfulSMul G X)) n (by
        intro x
        have hx : x ∈ MulAction.fixedPoints N X := by
          rw [hfixed]
          trivial
        exact MulAction.mem_fixedPoints.mp hx ⟨n, hn⟩)
    exact Subgroup.mem_bot.mpr hn_one
  have hNtrans : MulAction.IsPretransitive N X :=
    MulAction.IsQuasiPreprimitive.isPretransitive_of_normal hfixed_ne_univ
  have hFNa : F ≤ N.comap H.subtype := by
    simpa [H] using
      xi1115_normal_stabilizer_contains_frobeniusKernel
        htwo hno_regular_normal a b hab F hFrob hF2 N hNnormal hNne
  have hstab_multi :
      MulAction.IsMultiplyPretransitive H
        (SubMulAction.ofStabilizer G a) 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  have hHtrans :
      MulAction.IsPretransitive H (SubMulAction.ofStabilizer G a) :=
    (MulAction.is_one_pretransitive_iff
      (G := H) (α := SubMulAction.ofStabilizer G a)).mp hstab_multi
  have hFregular :
      ∀ x y : SubMulAction.ofStabilizer G a,
        ∃! f : F, (f : H) • x = y :=
    huppert_blackburn_XI_regular_of_isComplement_stabilizer
      hFrob.isComplement' hHtrans
  have htoBase : ∀ x y : X, x ≠ y →
      ∃ n : N, n • x = a ∧ n • y = b := by
    intro x y hxy
    obtain ⟨n0, hn0x⟩ := hNtrans.exists_smul_eq x a
    have hn0y_ne : n0 • y ≠ a := by
      intro hn0y
      apply hxy
      exact smul_left_cancel n0 (hn0x.trans hn0y.symm)
    let ySub : SubMulAction.ofStabilizer G a := ⟨n0 • y, hn0y_ne⟩
    let bSub : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
    obtain ⟨f, hf, _hfunique⟩ := hFregular ySub bSub
    have hfNmem : ((f : H) : G) ∈ N := by
      exact hFNa f.property
    let fN : N := ⟨((f : H) : G), hfNmem⟩
    have hfixa : fN • a = a := by
      change ((f : H) : G) • a = a
      exact MulAction.mem_stabilizer_iff.mp (f : H).property
    have hfY : fN • (n0 • y) = b := by
      simpa [fN, ySub, bSub] using congrArg Subtype.val hf
    refine ⟨fN * n0, ?_, ?_⟩
    · rw [mul_smul, hn0x, hfixa]
    · rw [mul_smul, hfY]
  apply MulAction.is_two_pretransitive_iff.mpr
  intro x y u v hxy huv
  obtain ⟨p, hpx, hpy⟩ := htoBase x y hxy
  obtain ⟨q, hqu, hqv⟩ := htoBase u v huv
  refine ⟨q⁻¹ * p, ?_, ?_⟩
  · rw [mul_smul, hpx, ← hqu, inv_smul_smul]
  · rw [mul_smul, hpy, ← hqv, inv_smul_smul]

/-- The quotient by a nontrivial normal subgroup is covered by the two-point
stabilizer. -/
private theorem xi1115_quotient_card_dvd_complement
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Finite X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥) :
    Nat.card (G ⧸ N) ∣
      Nat.card (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) := by
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change Nat.card (G ⧸ N) ∣ Nat.card D
  letI : N.Normal := hNnormal
  have hNtwo : MulAction.IsMultiplyPretransitive N X 2 :=
    xi1115_nontrivial_normal_is_two_pretransitive
      htwo hno_regular_normal a b hab F hFrob hF2 N hNnormal hNne
  letI : MulAction.IsMultiplyPretransitive N X 2 := hNtwo
  letI : MulAction.IsPretransitive N X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hFNa : F ≤ N.comap H.subtype := by
    simpa [H] using
      xi1115_normal_stabilizer_contains_frobeniusKernel
        htwo hno_regular_normal a b hab F hFrob hF2 N hNnormal hNne
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let qD : D →* G ⧸ N := q.comp (H.subtype.comp D.subtype)
  apply Subgroup.card_dvd_of_surjective (f := qD)
  intro y
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N y
  obtain ⟨n, hn⟩ :=
    (inferInstance : MulAction.IsPretransitive N X).exists_smul_eq (g • a) a
  let h : H := ⟨(n : G) * g, by
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    exact hn⟩
  rcases hFrob.isComplement'.2 h with
    ⟨⟨⟨f, hfF⟩, ⟨d, hdD⟩⟩, hfd⟩
  let fF : F := ⟨f, hfF⟩
  let dD : D := ⟨d, hdD⟩
  refine ⟨dD, ?_⟩
  have hfN : ((fF : H) : G) ∈ N := hFNa fF.property
  have hnq : q (n : G) = 1 := by
    exact QuotientGroup.eq_one_iff (n : G) |>.2 n.property
  have hfq : q ((fF : H) : G) = 1 := by
    exact QuotientGroup.eq_one_iff ((fF : H) : G) |>.2 hfN
  have hfdG : (n : G) * g = ((fF : H) : G) * ((dD : H) : G) := by
    simpa [h, fF, dD] using congrArg (fun z : H => (z : G)) hfd.symm
  have hq := congrArg q hfdG
  change q ((dD : H) : G) = q g
  simpa [map_mul, hnq, hfq] using hq.symm
/-- An element with a unique fixed point belongs to every nontrivial ambient
normal subgroup. -/
private theorem xi1115_one_fixed_mem_normal
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Fintype X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (N : Subgroup G) (hNnormal : N.Normal)
    (hFNa :
      let H := MulAction.stabilizer G a
      F ≤ N.comap H.subtype)
    (g : G) (hfixcard : Nat.card (MulAction.fixedBy X g) = 1) :
    g ∈ N := by
  classical
  let H := MulAction.stabilizer G a
  let X0 := SubMulAction.ofStabilizer G a
  let b' : X0 := ⟨b, hab.symm⟩
  change F ≤ N.comap H.subtype at hFNa
  letI : N.Normal := hNnormal
  letI : MulAction.IsMultiplyPretransitive G X 2 := htwo
  letI : MulAction.IsPretransitive G X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hstab_multi : MulAction.IsMultiplyPretransitive H X0 1 :=
    (SubMulAction.ofStabilizer.isMultiplyPretransitive
      (G := G) (a := a)).mp htwo
  have hHtrans : MulAction.IsPretransitive H X0 :=
    (MulAction.is_one_pretransitive_iff (G := H) (α := X0)).mp hstab_multi
  letI : Fintype (MulAction.fixedBy X g) := Fintype.ofFinite _
  have hfixcard' : Fintype.card (MulAction.fixedBy X g) = 1 := by
    simpa [Nat.card_eq_fintype_card] using hfixcard
  obtain ⟨x0, hx0unique⟩ := Fintype.card_eq_one_iff.mp hfixcard'
  obtain ⟨t, ht⟩ :=
    (inferInstance : MulAction.IsPretransitive G X).exists_smul_eq (x0 : X) a
  let yG : G := t * g * t⁻¹
  have hyfixa : yG • a = a := by
    calc
      yG • a = t • (g • (t⁻¹ • a)) := by simp [yG, mul_smul]
      _ = t • (g • (x0 : X)) := by
        have htx0 : t⁻¹ • a = (x0 : X) := by
          calc
            t⁻¹ • a = t⁻¹ • (t • (x0 : X)) := by rw [ht]
            _ = (x0 : X) := inv_smul_smul t (x0 : X)
        rw [htx0]
      _ = t • (x0 : X) := by rw [x0.property]
      _ = a := ht
  let yH : H := ⟨yG, MulAction.mem_stabilizer_iff.mpr hyfixa⟩
  have hyfree : ∀ z : X0, yH • z ≠ z := by
    intro z hz
    have hyz : yG • (z : X) = (z : X) := congrArg Subtype.val hz
    have hwfix : g • (t⁻¹ • (z : X)) = t⁻¹ • (z : X) := by
      have h := congrArg (fun w : X => t⁻¹ • w) hyz
      simpa [yG, mul_smul] using h
    let w : MulAction.fixedBy X g := ⟨t⁻¹ • (z : X), hwfix⟩
    have hwx0 : w = x0 := hx0unique w
    have hwx0val : t⁻¹ • (z : X) = (x0 : X) := congrArg Subtype.val hwx0
    apply z.property
    calc
      (z : X) = t • (t⁻¹ • (z : X)) := (smul_inv_smul t (z : X)).symm
      _ = t • (x0 : X) := by rw [hwx0val]
      _ = a := ht
  have hyF : yH ∈ F :=
    (xi1115_frobenius_kernel_mem_iff_eq_one_or_fixedPointFree
      hHtrans b' F (by simpa [H, X0, b'] using hFrob) yH).2 (Or.inr hyfree)
  have hyN : yG ∈ N := hFNa hyF
  have hconj : t⁻¹ * yG * (t⁻¹)⁻¹ = g := by
    dsimp [yG]
    group
  rw [← hconj]
  exact hNnormal.conj_mem yG hyN t⁻¹
/-- In odd degree, a derangement lies in every nontrivial normal subgroup. -/
private theorem xi1115_derangement_mem_normal
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Fintype X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ x y z : X,
          x ≠ y → x ≠ z → y ≠ z →
            ¬ (g • x = x ∧ g • y = y ∧ g • z = z))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hdegree : Fintype.card X = Nat.card F + 1)
    (hdegreeOdd : Odd (Fintype.card X))
    (hDodd : Odd (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hDdiv : Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∣ Nat.card F - 1)
    (N : Subgroup G) (hNnormal : N.Normal) (hNne : N ≠ ⊥)
    (g : G) (hfree : ∀ x : X, g • x ≠ x) :
    g ∈ N := by
  classical
  let D := MulAction.stabilizer (MulAction.stabilizer G a)
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  let σ : Equiv.Perm X := MulAction.toPerm g
  have hsupport : σ.support = Finset.univ := by
    rw [Finset.eq_univ_iff_forall]
    intro x
    rw [Equiv.Perm.mem_support]
    exact hfree x
  have hsum : σ.cycleType.sum = Fintype.card X := by
    rw [Equiv.Perm.sum_cycleType, hsupport, Finset.card_univ]
  have hexOdd : ∃ k : ℕ, k ∈ σ.cycleType ∧ Odd k := by
    by_contra h
    push Not at h
    have htwoDvd : 2 ∣ σ.cycleType.sum :=
      Multiset.dvd_sum (fun k hk =>
        even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp (h k hk)))
    apply hdegreeOdd.not_two_dvd_nat
    rw [hsum] at htwoDvd
    exact htwoDvd
  let m := Nat.find hexOdd
  have hmMem : m ∈ σ.cycleType := (Nat.find_spec hexOdd).1
  have hmOdd : Odd m := (Nat.find_spec hexOdd).2
  have hmTwo : 2 ≤ m := Equiv.Perm.two_le_of_mem_cycleType hmMem
  have hmThree : 3 ≤ m := by
    rcases hmOdd with ⟨k, hk⟩
    omega
  have hmFactor := hmMem
  rw [Equiv.Perm.cycleType_def, Multiset.mem_map] at hmFactor
  obtain ⟨c, hc, hcard⟩ := hmFactor
  have hcFin : c ∈ σ.cycleFactorsFinset := Finset.mem_def.mpr hc
  have hcard' : c.support.card = m := by simpa using hcard
  have hcycle : σ.IsCycleOn c.support :=
    Equiv.Perm.isCycleOn_support_of_mem_cycleFactorsFinset hcFin
  obtain ⟨x, y, z, hx, hy, hz, hxy, hxz, hyz⟩ :=
    Finset.two_lt_card_iff.mp (by omega : 2 < c.support.card)
  have hσpowFix (w : X) (hw : w ∈ c.support) : (σ ^ m) w = w := by
    rw [← hcard']
    exact hcycle.pow_card_apply hw
  have hpermPow : MulAction.toPerm (g ^ m) = σ ^ m := by
    change (MulAction.toPermHom G X) (g ^ m) =
      ((MulAction.toPermHom G X) g) ^ m
    exact map_pow (MulAction.toPermHom G X) g m
  have hgpow : g ^ m = 1 := by
    by_contra hgpow
    apply hat_most_two_fixed_points (g ^ m) hgpow x y z hxy hxz hyz
    refine ⟨?_, ?_, ?_⟩
    · change MulAction.toPerm (g ^ m) x = x
      rw [hpermPow]
      exact hσpowFix x hx
    · change MulAction.toPerm (g ^ m) y = y
      rw [hpermPow]
      exact hσpowFix y hy
    · change MulAction.toPerm (g ^ m) z = z
      rw [hpermPow]
      exact hσpowFix z hz
  have hσpow : σ ^ m = 1 := by
    rw [← hpermPow, hgpow]
    simpa using map_one (MulAction.toPermHom G X)
  have hordσDvdM : orderOf σ ∣ m :=
    orderOf_dvd_iff_pow_eq_one.mpr hσpow
  have hcycleEq : ∀ k ∈ σ.cycleType, k = m := by
    intro k hk
    have hkDvdM : k ∣ m :=
      (Equiv.Perm.dvd_of_mem_cycleType hk).trans hordσDvdM
    have hkOdd : Odd k := Odd.of_dvd_nat hmOdd hkDvdM
    have hmLeK : m ≤ k := Nat.find_min' hexOdd ⟨hk, hkOdd⟩
    have hkLeM : k ≤ m := Nat.le_of_dvd hmOdd.pos hkDvdM
    omega
  have hmDvdDegree : m ∣ Fintype.card X := by
    rw [← hsum]
    exact Multiset.dvd_sum (fun k hk => by rw [hcycleEq k hk])
  letI : N.Normal := hNnormal
  let qg : G ⧸ N := QuotientGroup.mk' N g
  have hquotDvd : Nat.card (G ⧸ N) ∣ Nat.card D := by
    simpa [D] using xi1115_quotient_card_dvd_complement
      htwo hno_regular_normal a b hab F hFrob hF2 N hNnormal hNne
  have hqDvdD : orderOf qg ∣ Nat.card D :=
    (orderOf_dvd_natCard qg).trans hquotDvd
  have hqOdd : Odd (orderOf qg) := Odd.of_dvd_nat (by simpa [D] using hDodd) hqDvdD
  have hqPow : qg ^ m = 1 := by
    change ((QuotientGroup.mk' N) g) ^ m = 1
    rw [← map_pow, hgpow, map_one]
  have hqDvdM : orderOf qg ∣ m := orderOf_dvd_of_pow_eq_one hqPow
  have hqDvdDegree : orderOf qg ∣ Fintype.card X := hqDvdM.trans hmDvdDegree
  have hqDvdFsub : orderOf qg ∣ Nat.card F - 1 :=
    hqDvdD.trans (by simpa [D] using hDdiv)
  rw [hdegree] at hqDvdDegree
  have hqDvdTwo : orderOf qg ∣ 2 := by
    have hsub := Nat.dvd_sub hqDvdDegree hqDvdFsub
    have hFpos : 0 < Nat.card F := Nat.card_pos
    convert hsub using 1; omega
  have hqOrderOne : orderOf qg = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hqDvdTwo with h | h
    · exact h
    · exfalso
      apply hqOdd.not_two_dvd_nat
      rw [h]
  have hqOne : qg = 1 := orderOf_eq_one_iff.mp hqOrderOne
  exact (QuotientGroup.eq_one_iff (N := N) g).mp (by simpa [qg] using hqOne)
/-- Under the XI.11.15 hypotheses, every nontrivial normal subgroup is the
whole ambient group. -/
private theorem xi1115_simple
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    [FaithfulSMul G X] [Fintype X]
    (htwo : MulAction.IsMultiplyPretransitive G X 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ x y z : X,
          x ≠ y → x ≠ z → y ≠ z →
            ¬ (g • x = x ∧ g • y = y ∧ g • z = z))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ x y : X, ∃! r : R, (r : G) • x = y)
    (a b : X) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hdegree : Fintype.card X = Nat.card F + 1)
    (hdegreeOdd : Odd (Fintype.card X))
    (hDodd : Odd (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hDdiv : Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∣ Nat.card F - 1) :
    ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤ := by
  classical
  intro N hNnormal hNne
  letI : Fintype G := Fintype.ofFinite G
  letI : N.Normal := hNnormal
  let H := MulAction.stabilizer G a
  have hFNa : F ≤ N.comap H.subtype := by
    simpa [H] using xi1115_normal_stabilizer_contains_frobeniusKernel
      htwo hno_regular_normal a b hab F hFrob hF2 N hNnormal hNne
  have hNtwo : MulAction.IsMultiplyPretransitive N X 2 :=
    xi1115_nontrivial_normal_is_two_pretransitive
      htwo hno_regular_normal a b hab F hFrob hF2 N hNnormal hNne
  let fix : G → ℕ := fun g => Fintype.card (MulAction.fixedBy X g)
  have hfixLe (g : G) (hg : g ≠ 1) : fix g ≤ 2 := by
    by_contra hle
    have hthree : 2 < Fintype.card (MulAction.fixedBy X g) := by
      simpa [fix] using Nat.lt_of_not_ge hle
    obtain ⟨x, y, z, hxy, hxz, hyz⟩ := Fintype.two_lt_card_iff.mp hthree
    exact hat_most_two_fixed_points g hg x y z
      (fun h => hxy (Subtype.ext h))
      (fun h => hxz (Subtype.ext h))
      (fun h => hyz (Subtype.ext h))
      ⟨x.property, y.property, z.property⟩
  have hfixZero (g : G) : fix g = 0 ↔ ∀ x : X, g • x ≠ x := by
    constructor
    · intro hzero x hfix
      haveI : IsEmpty (MulAction.fixedBy X g) :=
        Fintype.card_eq_zero_iff.mp (by simpa [fix] using hzero)
      exact isEmptyElim (⟨x, hfix⟩ : MulAction.fixedBy X g)
    · intro hfree
      apply Fintype.card_eq_zero_iff.mpr
      exact ⟨fun x => hfree x.1 x.2⟩
  have hfixOutside (g : G) (hgN : g ∉ N) : fix g = 2 := by
    have hgOne : g ≠ 1 := by
      intro hg
      apply hgN
      simp [hg]
    have hle := hfixLe g hgOne
    have hneZero : fix g ≠ 0 := by
      intro hzero
      apply hgN
      apply xi1115_derangement_mem_normal
        htwo hat_most_two_fixed_points hno_regular_normal
        a b hab F hFrob hF2 hdegree hdegreeOdd hDodd hDdiv
        N hNnormal hNne g
      exact (hfixZero g).mp hzero
    have hneOne : fix g ≠ 1 := by
      intro hone
      apply hgN
      apply xi1115_one_fixed_mem_normal
        htwo a b hab F hFrob N hNnormal hFNa g
      simpa [fix, Nat.card_eq_fintype_card] using hone
    omega
  let QG := Quotient (MulAction.orbitRel G X)
  letI : Fintype QG := Fintype.ofFinite QG
  letI : MulAction.IsPretransitive G X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  have hQGcard : Fintype.card QG = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let q0 : QG := Quotient.mk (MulAction.orbitRel G X) a
    refine ⟨q0, ?_⟩
    intro q
    rw [← Quotient.out_eq q]
    apply Quotient.sound
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G a (Quotient.out q)
    exact ⟨g, hg⟩
  have hsumG : ∑ g : G, fix g = Nat.card G := by
    have hburnside :=
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group G X
    simpa [fix, QG, hQGcard, Nat.card_eq_fintype_card] using hburnside
  letI : Fintype N := Fintype.ofFinite N
  letI : MulAction.IsMultiplyPretransitive N X 2 := hNtwo
  letI : MulAction.IsPretransitive N X :=
    MulAction.isPretransitive_of_is_two_pretransitive
  let QN := Quotient (MulAction.orbitRel N X)
  letI : Fintype QN := Fintype.ofFinite QN
  have hQNcard : Fintype.card QN = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let q0 : QN := Quotient.mk (MulAction.orbitRel N X) a
    refine ⟨q0, ?_⟩
    intro q
    rw [← Quotient.out_eq q]
    apply Quotient.sound
    obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N a (Quotient.out q)
    exact ⟨n, hn⟩
  have hsumN : ∑ n : N, fix (n : G) = Nat.card N := by
    have hburnside :=
      MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group N X
    simpa [fix, QN, hQNcard, Nat.card_eq_fintype_card] using hburnside
  let inside : Finset G := Finset.univ.filter fun g : G => g ∈ N
  let outside : Finset G := Finset.univ.filter fun g : G => g ∉ N
  have hsumInside : ∑ g ∈ inside, fix g = Nat.card N := by
    calc
      ∑ g ∈ inside, fix g = ∑ n : N, fix (n : G) := by
        apply Finset.sum_subtype inside
        intro g
        simp [inside]
      _ = Nat.card N := hsumN
  let Gout := {g : G // g ∉ N}
  letI : Fintype Gout := Fintype.ofFinite Gout
  have hcardOut : Fintype.card Gout = Nat.card G - Nat.card N := by
    simp [Gout, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have hsumOutside : ∑ g ∈ outside, fix g = 2 * (Nat.card G - Nat.card N) := by
    calc
      ∑ g ∈ outside, fix g = ∑ g : Gout, fix (g : G) := by
        apply Finset.sum_subtype outside
        intro g
        simp [outside]
      _ = ∑ _g : Gout, 2 := by
        apply Finset.sum_congr rfl
        intro g _hg
        exact hfixOutside g.1 g.2
      _ = 2 * (Nat.card G - Nat.card N) := by
        simp [hcardOut, mul_comm]
  have hpartition :
      (∑ g ∈ inside, fix g) + (∑ g ∈ outside, fix g) = ∑ g : G, fix g := by
    simpa [inside, outside] using
      Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset G)
        (fun g : G => g ∈ N) fix
  rw [hsumInside, hsumOutside, hsumG] at hpartition
  have hcardLe : Nat.card N ≤ Nat.card G :=
    Nat.card_le_card_of_injective N.subtype N.subtype_injective
  have hcardEq : Nat.card N = Nat.card G := by omega
  exact Subgroup.eq_top_of_card_eq N hcardEq
private theorem xi1115_exists_structureEquation
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ x : G, x ≠ 1 →
        ∀ u v w : Omega,
          u ≠ v → u ≠ w → v ≠ w →
            ¬ (x • u = u ∧ x • v = v ∧ x • w = w))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (s : G) (hsorder : orderOf s = 2)
    (hsa : s • a = b) (hsb : s • b = a) :
    ∃ (j g : F), orderOf j = 2 ∧ g ≠ 1 ∧
      s * (((j : F) : MulAction.stabilizer G a) : G) * s =
        (((g : F) : MulAction.stabilizer G a) : G) * s *
          (((g : F) : MulAction.stabilizer G a) : G)⁻¹ := by
  classical
  let H := MulAction.stabilizer G a
  obtain ⟨c, hsc, _hcuniq⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints s hsorder
  have hca : c ≠ a := by
    intro h
    apply hab
    calc
      a = s • a := by rw [← h, hsc]
      _ = b := hsa
  have hcb : c ≠ b := by
    intro h
    apply hab
    calc
      a = s • b := hsb.symm
      _ = s • c := by rw [h]
      _ = c := hsc
      _ = b := h
  let c' : SubMulAction.ofStabilizer G a := ⟨c, hca⟩
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  obtain ⟨e, he⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_kernelPointEquiv
      htwo a b hab F hFrob
  let g0 : F := e.symm c'
  have hg0bSub : (g0 : H) • b' = c' := by
    rw [← he]
    exact e.apply_symm_apply c'
  have hg0b : (((g0 : F) : H) : G) • b = c :=
    congrArg Subtype.val hg0bSub
  let g : F := g0⁻¹
  let gG : G := (((g : F) : H) : G)
  have hgcinv : gG⁻¹ • b = c := by
    change ((((g0 : F)⁻¹ : F) : H) : G)⁻¹ • b = c
    simpa using hg0b
  have hgc : gG • c = b := by
    calc
      gG • c = gG • (gG⁻¹ • b) := by rw [hgcinv]
      _ = b := smul_inv_smul gG b
  have hgne : g ≠ 1 := by
    intro hg
    apply hcb
    have hgc' := hgc
    simp [gG, g, hg] at hgc'
    exact hgc'
  have hssq : s ^ 2 = 1 := by
    rw [← hsorder]
    exact pow_orderOf_eq_one s
  let jG : G := s * gG * s * gG⁻¹ * s
  have hjconj : jG = (s * gG) * s * (s * gG)⁻¹ := by
    dsimp [jG]
    have hsinv : s⁻¹ = s := by
      apply inv_eq_of_mul_eq_one_right
      simpa [pow_two] using hssq
    rw [mul_inv_rev, hsinv]
    group
  have hjorder : orderOf jG = 2 := by
    rw [hjconj]
    exact ((MulAut.conj (s * gG)).orderOf_eq s).trans hsorder
  have hginvb : gG⁻¹ • b = c := by
    calc
      gG⁻¹ • b = gG⁻¹ • (gG • c) := by rw [hgc]
      _ = c := inv_smul_smul gG c
  have hjfix : jG • a = a := by
    dsimp [jG]
    simp only [mul_smul]
    rw [hsa, hginvb, hsc, hgc, hsb]
  have hjmem : (⟨jG, hjfix⟩ : H) ∈ F :=
    xi1115_involution_mem_frobeniusKernel_of_fixedPoint
      htwo hdegreeOdd hatMostTwoFixedPoints a b hab F hFrob
      jG hjorder hjfix
  let j : F := ⟨⟨jG, hjfix⟩, hjmem⟩
  have hjorderF : orderOf j = 2 := by
    change orderOf (⟨⟨jG, hjfix⟩, hjmem⟩ : F) = 2
    calc
      orderOf (⟨⟨jG, hjfix⟩, hjmem⟩ : F) =
          orderOf (⟨jG, hjfix⟩ : H) := Subgroup.orderOf_mk _ _
      _ = orderOf jG := Subgroup.orderOf_mk _ _
      _ = 2 := hjorder
  refine ⟨j, g, hjorderF, hgne, ?_⟩
  change s * jG * s = gG * s * gG⁻¹
  dsimp [jG]
  calc
    s * (s * gG * s * gG⁻¹ * s) * s =
        (s * s) * gG * s * gG⁻¹ * (s * s) := by group
    _ = gG * s * gG⁻¹ := by
      have hss : s * s = 1 := by simpa [pow_two] using hssq
      rw [hss]
      simp
private theorem xi1115_zpowers_inf_kernel_eq_bot
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (a : Omega) (F : Subgroup (MulAction.stabilizer G a))
    (hF2 : IsPGroup 2 F) (r : G) (hrodd : Odd (orderOf r)) :
    Subgroup.zpowers r ⊓
        F.map (MulAction.stabilizer G a).subtype = ⊥ := by
  rw [eq_bot_iff]
  intro u hu
  rcases hu.2 with ⟨x, hxF, hxu⟩
  let xF : F := ⟨x, hxF⟩
  have horderEq : orderOf u = orderOf xF := by
    calc
      orderOf u = orderOf ((x : MulAction.stabilizer G a) : G) := by
        exact congrArg orderOf hxu |>.symm
      _ = orderOf x := Subgroup.orderOf_coe x
      _ = orderOf xF := Subgroup.orderOf_coe xF
  have hdvd : orderOf u ∣ orderOf r :=
    orderOf_dvd_of_mem_zpowers hu.1
  have hcopX : (orderOf xF).Coprime (orderOf r) :=
    hF2.orderOf_coprime hrodd.coprime_two_left xF
  have hcopU : (orderOf u).Coprime (orderOf r) := by
    rw [horderEq]
    exact hcopX
  have horderOne : orderOf u = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopU dvd_rfl hdvd
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp horderOne)
private theorem xi1115_mem_normalizer_zpowers_of_conj_eq_pow_coprime
    {G : Type*} [Group G] [Finite G]
    (g r : G) (n : ℕ)
    (hconj : g * r * g⁻¹ = r ^ n)
    (hcop : n.Coprime (orderOf r)) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
  let phi : G ≃* G := MulAut.conj g
  have hphi : phi r = r ^ n := by
    simpa [phi] using hconj
  have hzpow : Subgroup.zpowers (r ^ n) = Subgroup.zpowers r := by
    apply le_antisymm
    · exact Subgroup.zpowers_le.mpr
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers r) n)
    · exact Subgroup.zpowers_le.mpr (mem_zpowers_pow_iff.mpr hcop)
  have hmap :
      Subgroup.map phi.toMonoidHom (Subgroup.zpowers r) =
        Subgroup.zpowers r := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (phi r) = Subgroup.zpowers r
    rw [hphi, hzpow]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    change phi x ∈ Subgroup.zpowers r
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    change phi x ∈ Subgroup.zpowers r at hx
    have hxmap : phi x ∈
        Subgroup.map phi.toMonoidHom (Subgroup.zpowers r) := by
      rw [hmap]
      exact hx
    rcases hxmap with ⟨y, hy, hyx⟩
    have : y = x := phi.injective hyx
    simpa [this] using hy

private theorem xi1115_mem_normalizer_zpowers_of_conj_eq_inv
    {G : Type*} [Group G]
    (g r : G) (hconj : g * r * g⁻¹ = r⁻¹) :
    g ∈ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
  let phi : G ≃* G := MulAut.conj g
  have hphi : phi r = r⁻¹ := by
    simpa [phi] using hconj
  have hmap :
      Subgroup.map phi.toMonoidHom (Subgroup.zpowers r) =
        Subgroup.zpowers r := by
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (phi r) = Subgroup.zpowers r
    rw [hphi, Subgroup.zpowers_inv]
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    change phi x ∈ Subgroup.zpowers r
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  · intro hx
    change phi x ∈ Subgroup.zpowers r at hx
    have hxmap : phi x ∈
        Subgroup.map phi.toMonoidHom (Subgroup.zpowers r) := by
      rw [hmap]
      exact hx
    rcases hxmap with ⟨y, hy, hyx⟩
    have : y = x := phi.injective hyx
    simpa [this] using hy

private theorem xi1115_kernel_involution_inverts_zpowers
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (r : G)
    (hcap : Subgroup.zpowers r ⊓
      F.map (MulAction.stabilizer G a).subtype = ⊥)
    (z : F) (hzorder : orderOf z = 2)
    (hzNorm :
      (((z : MulAction.stabilizer G a) : G)) ∈
        Subgroup.normalizer (Subgroup.zpowers r : Set G)) :
    ∀ x : Subgroup.zpowers r,
      (((z : MulAction.stabilizer G a) : G)) * (x : G) *
          (((z : MulAction.stabilizer G a) : G))⁻¹ =
        ((x⁻¹ : Subgroup.zpowers r) : G) := by
  let U := Subgroup.zpowers r
  let zG : G := (((z : MulAction.stabilizer G a) : G))
  have hzsq : z ^ 2 = 1 := by
    rw [← hzorder]
    exact pow_orderOf_eq_one z
  have hzsqG : zG ^ 2 = 1 := by
    simpa [zG] using congrArg
      (fun y : F => (((y : F) : MulAction.stabilizer G a) : G)) hzsq
  let zN : Subgroup.normalizer (U : Set G) := ⟨zG, by simpa [U, zG] using hzNorm⟩
  let phi : MulAut U := U.normalizerMonoidHom zN
  have hphiSq : phi ^ 2 = 1 := by
    change (U.normalizerMonoidHom zN) ^ 2 = 1
    have hzNSq : zN ^ 2 = 1 := by
      apply Subtype.ext
      exact hzsqG
    rw [← map_pow, hzNSq, map_one]
  have hphiInv : Function.Involutive phi := by
    intro x
    have hx := congrArg (fun psi : MulAut U => psi x) hphiSq
    simpa [pow_two] using hx
  have hzne : z ≠ 1 := (orderOf_eq_prime_iff.mp hzorder).2
  have hphiFree : MonoidHom.FixedPointFree phi := by
    intro x hx
    have hxconj : zG * (x : G) * zG⁻¹ = (x : G) := by
      simpa [phi, zN, U, zG,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using
          congrArg Subtype.val hx
    have hxcomm : Commute zG (x : G) := by
      apply commutatorElement_eq_one_iff_commute.mp
      simp [commutatorElement_def, hxconj]
    have hxcent :
        (x : G) ∈ Subgroup.centralizer ({zG} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hxcomm.eq.symm
    have hxF :
        (x : G) ∈ F.map (MulAction.stabilizer G a).subtype := by
      simpa [zG] using
        xi1115_frobeniusKernel_ambient_centralizer_le
          htwo a b hab F hFrob z hzne hxcent
    have hxbot :
        (x : G) ∈ Subgroup.zpowers r ⊓
          F.map (MulAction.stabilizer G a).subtype :=
      ⟨by exact x.property, hxF⟩
    have hxoneG : (x : G) = 1 := by
      have : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [hcap] using hxbot
      simpa using this
    exact Subtype.ext hxoneG
  have hphiEqInv : ⇑phi = fun x : U => x⁻¹ :=
    hphiFree.coe_eq_inv_of_involutive hphiInv
  intro x
  have hx := congrArg Subtype.val (congrFun hphiEqInv x)
  simpa [phi, zN, U, zG,
    Subgroup.normalizerMonoidHom_apply_apply_coe] using hx

private theorem xi1115_structureEquation_product_order_odd
    {G : Type*} [Group G] [Finite G]
    (s j g : G) (hjg : j * g = g * j)
    (hstructure : s * j * s = g * s * g⁻¹) :
    Odd (orderOf (j * s)) := by
  have hconjPow : g * (j * s) * g⁻¹ = (j * s) ^ 2 := by
    calc
      g * (j * s) * g⁻¹ = (g * j) * s * g⁻¹ := by group
      _ = (j * g) * s * g⁻¹ := by rw [hjg]
      _ = j * (g * s * g⁻¹) := by group
      _ = j * (s * j * s) := by rw [← hstructure]
      _ = (j * s) ^ 2 := by rw [pow_two]; group
  have horderEq : orderOf ((j * s) ^ 2) = orderOf (j * s) := by
    rw [← hconjPow]
    exact (MulAut.conj g).orderOf_eq (j * s)
  apply Nat.not_even_iff_odd.mp
  intro heven
  have htwoDvd : 2 ∣ orderOf (j * s) := even_iff_two_dvd.mp heven
  have hpowOrder :
      orderOf ((j * s) ^ 2) = orderOf (j * s) / 2 :=
    orderOf_pow_of_dvd (x := j * s) (n := 2) (by norm_num) htwoDvd
  rw [hpowOrder] at horderEq
  have hpos : 0 < orderOf (j * s) := orderOf_pos (j * s)
  omega
private theorem xi1115_structureEquation_power
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (s : G) (hsorder : orderOf s = 2) (hsa : s • a = b)
    (j g : F) (hjorder : orderOf j = 2) (hgne : g ≠ 1)
    (hjcenter : j ∈ Subgroup.center F)
    (hstructure :
      s * (((j : F) : MulAction.stabilizer G a) : G) * s =
        (((g : F) : MulAction.stabilizer G a) : G) * s *
          (((g : F) : MulAction.stabilizer G a) : G)⁻¹) :
    j ∈ Subgroup.zpowers g := by
  let jG : G := (((j : F) : MulAction.stabilizer G a) : G)
  let gG : G := (((g : F) : MulAction.stabilizer G a) : G)
  let r : G := jG * s
  have hjgF : j * g = g * j :=
    (Subgroup.mem_center_iff.mp hjcenter g).symm
  have hjgG : jG * gG = gG * jG := by
    simpa [jG, gG] using congrArg
      (fun x : F => (((x : F) : MulAction.stabilizer G a) : G)) hjgF
  have hjsOdd : Odd (orderOf r) := by
    simpa [r, jG, gG] using
      xi1115_structureEquation_product_order_odd
        s jG gG hjgG hstructure
  have hcap :
      Subgroup.zpowers r ⊓
        F.map (MulAction.stabilizer G a).subtype = ⊥ :=
    xi1115_zpowers_inf_kernel_eq_bot a F hF2 r hjsOdd
  have hgConj : gG * r * gG⁻¹ = r ^ 2 := by
    calc
      gG * r * gG⁻¹ = (gG * jG) * s * gG⁻¹ := by
        simp [r, mul_assoc]
      _ = (jG * gG) * s * gG⁻¹ := by rw [← hjgG]
      _ = jG * (gG * s * gG⁻¹) := by group
      _ = jG * (s * jG * s) := by rw [← hstructure]
      _ = r ^ 2 := by simp [r, pow_two]; group
  have hgNorm :
      gG ∈ Subgroup.normalizer (Subgroup.zpowers r : Set G) :=
    xi1115_mem_normalizer_zpowers_of_conj_eq_pow_coprime
      gG r 2 hgConj hjsOdd.coprime_two_right.symm
  have hssq : s ^ 2 = 1 := by
    rw [← hsorder]
    exact pow_orderOf_eq_one s
  have hsinv : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hssq
  have hjsq : j ^ 2 = 1 := by
    rw [← hjorder]
    exact pow_orderOf_eq_one j
  have hjsqG : jG ^ 2 = 1 := by
    simpa [jG] using congrArg
      (fun x : F => (((x : F) : MulAction.stabilizer G a) : G)) hjsq
  have hjinvG : jG⁻¹ = jG := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using hjsqG
  have hjConj : jG * r * jG⁻¹ = r⁻¹ := by
    calc
      jG * r * jG⁻¹ = jG * (jG * s) * jG := by
        rw [hjinvG]
      _ = s * jG := by
        have hjmul : jG * jG = 1 := by simpa [pow_two] using hjsqG
        rw [← mul_assoc, hjmul, one_mul]
      _ = (jG * s)⁻¹ := by rw [mul_inv_rev, hjinvG, hsinv]
      _ = r⁻¹ := rfl
  have hjNorm :
      jG ∈ Subgroup.normalizer (Subgroup.zpowers r : Set G) :=
    xi1115_mem_normalizer_zpowers_of_conj_eq_inv jG r hjConj
  obtain ⟨k, hgorder⟩ := (IsPGroup.iff_orderOf.mp hF2) g
  have hkne : k ≠ 0 := by
    intro hk
    apply hgne
    apply orderOf_eq_one_iff.mp
    simpa [hk] using hgorder
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hkne
  let t : F := g ^ (2 ^ q)
  have hpowDvd : 2 ^ q ∣ orderOf g := by
    rw [hgorder]
    exact pow_dvd_pow 2 (Nat.le_succ q)
  have htorder : orderOf t = 2 := by
    calc
      orderOf t = orderOf g / (2 ^ q) := by
        exact orderOf_pow_of_dvd (by positivity) hpowDvd
      _ = 2 ^ (q + 1) / (2 ^ q) := by rw [hgorder]
      _ = 2 := by simp [pow_succ]
  let tG : G := (((t : F) : MulAction.stabilizer G a) : G)
  have htGpow : tG = gG ^ (2 ^ q) := by
    simp [tG, t, gG]
  have htNorm :
      tG ∈ Subgroup.normalizer (Subgroup.zpowers r : Set G) := by
    rw [htGpow]
    exact (Subgroup.normalizer (Subgroup.zpowers r : Set G)).pow_mem
      hgNorm (2 ^ q)
  have hjInverts :=
    xi1115_kernel_involution_inverts_zpowers
      htwo a b hab F hFrob r hcap j hjorder hjNorm
  have htInverts :=
    xi1115_kernel_involution_inverts_zpowers
      htwo a b hab F hFrob r hcap t htorder htNorm
  have hrne : r ≠ 1 := by
    intro hr
    have hsEq : s = jG⁻¹ := by
      have h := congrArg (fun x : G => jG⁻¹ * x) hr
      simpa [r, mul_assoc] using h
    have hjfix : jG • a = a := by
      exact (j : MulAction.stabilizer G a).property
    have hjinvfix : jG⁻¹ • a = a := by
      calc
        jG⁻¹ • a = jG⁻¹ • (jG • a) := by rw [hjfix]
        _ = a := inv_smul_smul jG a
    apply hab
    calc
      a = s • a := by rw [hsEq, hjinvfix]
      _ = b := hsa
  let rU : Subgroup.zpowers r := ⟨r, Subgroup.mem_zpowers r⟩
  have hjInvR : jG * r * jG⁻¹ = r⁻¹ := by
    simpa [rU] using hjInverts rU
  have htInvR : tG * r * tG⁻¹ = r⁻¹ := by
    simpa [rU] using htInverts rU
  let v : F := t⁻¹ * j
  have hvone : v = 1 := by
    by_contra hvne
    have hjMove : jG * r = r⁻¹ * jG := by
      calc
        jG * r = (jG * r * jG⁻¹) * jG := by group
        _ = r⁻¹ * jG := by rw [hjInvR]
    have htMove : tG⁻¹ * r⁻¹ = r * tG⁻¹ := by
      calc
        tG⁻¹ * r⁻¹ = tG⁻¹ * (tG * r * tG⁻¹) := by rw [htInvR]
        _ = r * tG⁻¹ := by group
    have hvcomm :
        (((v : F) : MulAction.stabilizer G a) : G) * r =
          r * (((v : F) : MulAction.stabilizer G a) : G) := by
      change (tG⁻¹ * jG) * r = r * (tG⁻¹ * jG)
      calc
        (tG⁻¹ * jG) * r = tG⁻¹ * (r⁻¹ * jG) := by
          rw [mul_assoc, hjMove]
        _ = r * (tG⁻¹ * jG) := by
          rw [← mul_assoc, htMove, mul_assoc]
    have hrcent :
        r ∈ Subgroup.centralizer
          ({(((v : F) : MulAction.stabilizer G a) : G)} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr hvcomm.symm
    have hrF :
        r ∈ F.map (MulAction.stabilizer G a).subtype :=
      xi1115_frobeniusKernel_ambient_centralizer_le
        htwo a b hab F hFrob v hvne hrcent
    have hrbot : r ∈ (⊥ : Subgroup G) := by
      have :
          r ∈ Subgroup.zpowers r ⊓
            F.map (MulAction.stabilizer G a).subtype :=
        ⟨Subgroup.mem_zpowers r, hrF⟩
      simpa [hcap] using this
    exact hrne (Subgroup.mem_bot.mp hrbot)
  have hjt : j = t := by
    have h := congrArg (fun x : F => t * x) hvone
    simpa [v, mul_assoc] using h
  rw [hjt]
  exact (Subgroup.zpowers g).pow_mem (Subgroup.mem_zpowers g) (2 ^ q)


private theorem xi1115_cyclic_power_order_four
    {F : Type*} [Group F] [Finite F]
    (j g : F) (hjorder : orderOf j = 2) (hgne : g ≠ 1)
    (hg4 : g ^ 4 = 1) (hjPower : j ∈ Subgroup.zpowers g)
    (hjgne : j ≠ g) :
    orderOf g = 4 ∧ j = g ^ 2 := by
  have horderDvd : orderOf g ∣ 4 :=
    orderOf_dvd_of_pow_eq_one hg4
  have horderPos : 0 < orderOf g := orderOf_pos g
  have horderNeOne : orderOf g ≠ 1 := by
    intro h
    exact hgne (orderOf_eq_one_iff.mp h)
  have horderNeTwo : orderOf g ≠ 2 := by
    intro horderTwo
    let U := Subgroup.zpowers g
    have hUcard : Nat.card U = 2 := by
      simpa [U, Nat.card_zpowers] using horderTwo
    let jU : U := ⟨j, hjPower⟩
    let gU : U := ⟨g, Subgroup.mem_zpowers g⟩
    have hjUne : jU ≠ 1 := by
      intro h
      have hjone : j = 1 := congrArg Subtype.val h
      rw [hjone, orderOf_one] at hjorder
      omega
    have hgUne : gU ≠ 1 := by
      intro h
      exact hgne (congrArg Subtype.val h)
    obtain ⟨u, _hu, huuniq⟩ :=
      (Nat.card_eq_two_iff' (1 : U)).mp hUcard
    have hjUeq : jU = u := huuniq jU hjUne
    have hgUeq : gU = u := huuniq gU hgUne
    apply hjgne
    exact congrArg Subtype.val (hjUeq.trans hgUeq.symm)
  have horderLe : orderOf g ≤ 4 :=
    Nat.le_of_dvd (by norm_num) horderDvd
  have horderNeThree : orderOf g ≠ 3 := by
    intro h
    norm_num [h] at horderDvd
  have horder : orderOf g = 4 := by omega
  refine ⟨horder, ?_⟩
  have hjSq : j ^ 2 = 1 := by
    rw [← hjorder]
    exact pow_orderOf_eq_one j
  have hjne : j ≠ 1 := (orderOf_eq_prime_iff.mp hjorder).2
  obtain ⟨n, hn⟩ :=
    (Submonoid.mem_powers_iff j g).mp
      (mem_powers_iff_mem_zpowers.mpr hjPower)
  have hjPow : j = g ^ n := hn.symm
  have htwoDvd : 2 ∣ n := by
    have hpow : g ^ (2 * n) = 1 := by
      calc
        g ^ (2 * n) = g ^ (n * 2) := by rw [Nat.mul_comm]
        _ = (g ^ n) ^ 2 := by rw [pow_mul]
        _ = j ^ 2 := by rw [← hjPow]
        _ = 1 := hjSq
    have hfourDvd : 4 ∣ 2 * n := by
      rw [← horder]
      exact orderOf_dvd_of_pow_eq_one hpow
    omega
  have hfourNotDvd : ¬ 4 ∣ n := by
    intro hfourDvd
    apply hjne
    rw [hjPow]
    apply orderOf_dvd_iff_pow_eq_one.mp
    simpa [horder] using hfourDvd
  have hmod : n ≡ 2 [MOD 4] := by
    rcases htwoDvd with ⟨k, rfl⟩
    have hkodd : Odd k := by
      apply Nat.not_even_iff_odd.mp
      intro hkeven
      apply hfourNotDvd
      rcases hkeven with ⟨q, hq⟩
      refine ⟨q, ?_⟩
      omega
    rcases hkodd with ⟨q, hq⟩
    rw [hq]
    apply Nat.ModEq.symm
    rw [Nat.modEq_iff_dvd' (by omega)]
    exact ⟨q, by omega⟩
  rw [hjPow]
  apply pow_eq_pow_iff_modEq.mpr
  simpa [horder] using hmod

private theorem xi1115_seven_term_relation_order_five
    {G : Type*} [Group G] (s j : G)
    (hss : s * s = 1) (hjj : j * j = 1)
    (hrel : j * s * j = s * j * s * j * s * j * s) :
    (s * j) ^ 5 = 1 := by
  have hsInv : s⁻¹ = s := by
    apply inv_eq_of_mul_eq_one_right
    exact hss
  have hjInv : j⁻¹ = j := by
    apply inv_eq_of_mul_eq_one_right
    exact hjj
  have hpow : (s * j)⁻¹ = (s * j) ^ 4 := by
    calc
      (s * j)⁻¹ = j * s := by rw [mul_inv_rev, hsInv, hjInv]
      _ = (j * s) * (j * j) := by rw [hjj, mul_one]
      _ = (j * s * j) * j := by group
      _ = (s * j * s * j * s * j * s) * j := by rw [hrel]
      _ = (s * j) ^ 4 := by
        simp only [pow_succ, pow_zero, one_mul]
        group
  calc
    (s * j) ^ 5 = (s * j) * (s * j) ^ 4 := by
      simp only [pow_succ, pow_zero, one_mul]
      group
    _ = (s * j) * (s * j)⁻¹ := by rw [hpow]
    _ = 1 := mul_inv_cancel (s * j)

private theorem xi1115_structureEquation_order_five
    {G : Type*} [Group G] (s j g : G)
    (hss : s * s = 1) (hjj : j * j = 1)
    (hjg : j = g ^ 2)
    (hstructure : s * j * s = g * s * g⁻¹) :
    (s * j) ^ 5 = 1 := by
  have hjInv : j⁻¹ = j := by
    apply inv_eq_of_mul_eq_one_right
    exact hjj
  have hgj : g * j = j * g := by
    rw [hjg]
    group
  have hgs : g * s = s * j * s * g := by
    calc
      g * s = (g * s * g⁻¹) * g := by group
      _ = (s * j * s) * g := by rw [← hstructure]
  have hrel : j * s * j = s * j * s * j * s * j * s := by
    calc
      j * s * j = j * s * j⁻¹ := by rw [hjInv]
      _ = g ^ 2 * s * (g ^ 2)⁻¹ := by rw [hjg]
      _ = g * (g * s * g⁻¹) * g⁻¹ := by
        simp only [pow_two, mul_inv_rev]
        group
      _ = g * (s * j * s) * g⁻¹ := by rw [← hstructure]
      _ = (g * s) * j * s * g⁻¹ := by group
      _ = (s * j * s * g) * j * s * g⁻¹ := by rw [hgs]
      _ = s * j * s * (g * j) * s * g⁻¹ := by group
      _ = s * j * s * (j * g) * s * g⁻¹ := by rw [hgj]
      _ = s * j * s * j * g * s * g⁻¹ := by group
      _ = s * j * s * j * (g * s * g⁻¹) := by group
      _ = s * j * s * j * (s * j * s) := by rw [← hstructure]
      _ = s * j * s * j * s * j * s := by group
  exact xi1115_seven_term_relation_order_five s j hss hjj hrel

private theorem xi1115_odd_of_not_three_dvd_two_pow_sub_one
    (l : ℕ) (hnot : ¬ 3 ∣ 2 ^ l - 1) :
    Odd l := by
  apply Nat.not_even_iff_odd.mp
  intro hEven
  rcases hEven with ⟨k, hk⟩
  apply hnot
  have hmod : 2 ^ l % 3 = 1 := by
    rw [hk]
    have hexp : k + k = 2 * k := by omega
    rw [hexp, pow_mul]
    have hfour : 4 ^ k % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    simpa using hfour
  have hpos : 1 ≤ 2 ^ l := by
    have : 0 < 2 ^ l := by positivity
    omega
  apply (Nat.modEq_iff_dvd' hpos).mp
  change 1 % 3 = 2 ^ l % 3
  norm_num [hmod]

private theorem xi1115_pow_two_mod_five_of_odd (l : ℕ) (hl : Odd l) :
    2 ^ l % 5 = 2 ∨ 2 ^ l % 5 = 3 := by
  rcases hl with ⟨k, hk⟩
  rcases Nat.even_or_odd' k with ⟨r, hr | hr⟩
  · left
    rw [hk, hr]
    have hexp : 2 * (2 * r) + 1 = 4 * r + 1 := by omega
    rw [hexp, pow_add, pow_mul, Nat.mul_mod]
    have h16 : 16 ^ r % 5 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    norm_num [h16]
  · right
    rw [hk, hr]
    have hexp : 2 * (2 * r + 1) + 1 = 4 * r + 3 := by omega
    rw [hexp, pow_add, pow_mul, Nat.mul_mod]
    have h16 : 16 ^ r % 5 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    norm_num [h16]

private theorem xi1115_not_five_dvd_cube_order_of_odd
    (l : ℕ) (hl : Odd l) :
    ¬ 5 ∣ ((2 ^ l) ^ 3 + 1) * (2 ^ l) ^ 3 * (2 ^ l - 1) := by
  intro hfive
  let q := 2 ^ l
  have hqmod : q % 5 = 2 ∨ q % 5 = 3 := by
    simpa [q] using xi1115_pow_two_mod_five_of_odd l hl
  rcases Nat.prime_five.dvd_mul.mp hfive with hleft | hsub
  · rcases Nat.prime_five.dvd_mul.mp hleft with hplus | hpow
    · have hzero : (q ^ 3 + 1) % 5 = 0 :=
        Nat.dvd_iff_mod_eq_zero.mp hplus
      rcases hqmod with hqmod | hqmod <;>
        norm_num [Nat.add_mod, Nat.pow_mod, hqmod] at hzero
    · have hqdiv : 5 ∣ q := Nat.prime_five.dvd_of_dvd_pow hpow
      have hzero : q % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp hqdiv
      omega
  · have hqpos : 1 ≤ q := by
      have hqpositive : 0 < q := by
        dsimp [q]
        positivity
      omega
    have hmod : 1 ≡ q [MOD 5] :=
      (Nat.modEq_iff_dvd' hqpos).mpr hsub
    change 1 % 5 = q % 5 at hmod
    norm_num at hmod
    omega

private theorem xi1115_kernel_card_eq_center_sq_of_structureEquation
    {G F : Type*} [Group G] [Finite G] [Group F] [Finite F]
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (l : ℕ) (hZcard : Nat.card (Subgroup.center F) = 2 ^ l)
    (hlOdd : Odd l) (phi : F →* G)
    (s : G) (j g : F) (hss : s * s = 1)
    (hjorder : orderOf j = 2) (hgne : g ≠ 1)
    (hjPower : j ∈ Subgroup.zpowers g) (hjgne : j ≠ g)
    (hsjne : s * phi j ≠ 1)
    (hstructure : s * phi j * s = phi g * s * (phi g)⁻¹)
    (hGcard : Nat.card G =
      (Nat.card F + 1) * Nat.card F * (2 ^ l - 1)) :
    Nat.card F = Nat.card (Subgroup.center F) ^ 2 := by
  have hHigman :=
    Higman.theorem1_center_quotient_orders_and_exponent hFSuzuki
  rcases hHigman.2.2.2.1 with hsq | hcube
  · exact hsq
  · exfalso
    have hg4 : g ^ 4 = 1 := hHigman.2.2.2.2 g
    obtain ⟨_hgorder, hjg⟩ :=
      xi1115_cyclic_power_order_four
        j g hjorder hgne hg4 hjPower hjgne
    have hjSq : j ^ 2 = 1 := by
      rw [← hjorder]
      exact pow_orderOf_eq_one j
    have hjSqG : phi j * phi j = 1 := by
      simpa [pow_two] using congrArg phi hjSq
    have hjgG : phi j = (phi g) ^ 2 := by
      simpa using congrArg phi hjg
    have hpowFive : (s * phi j) ^ 5 = 1 :=
      xi1115_structureEquation_order_five
        s (phi j) (phi g) hss hjSqG hjgG hstructure
    letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have horderFive : orderOf (s * phi j) = 5 :=
      orderOf_eq_prime hpowFive hsjne
    have hfive : 5 ∣ Nat.card G := by
      rw [← horderFive]
      exact orderOf_dvd_natCard (s * phi j)
    apply xi1115_not_five_dvd_cube_order_of_odd l hlOdd
    rw [hGcard, hcube, hZcard] at hfive
    exact hfive

private theorem xi1115_sharpTriple_of_card_eq_descFactorial
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (hcard : Nat.card G = (Fintype.card Omega).descFactorial 3)
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c)) :
    ∀ a b c a' b' c' : Omega,
      a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
          ∃! g : G,
            g • a = a' ∧ g • b = b' ∧ g • c = c' := by
  classical
  intro a b c a' b' c' hab hac hbc ha'b' ha'c' hb'c'
  let source : Fin 3 ↪ Omega :=
    ⟨![a, b, c], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  let target : Fin 3 ↪ Omega :=
    ⟨![a', b', c'], by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all⟩
  let orbit : G → (Fin 3 ↪ Omega) := fun g =>
    source.trans (MulAction.toPermHom G Omega g).toEmbedding
  have horbitInjective : Function.Injective orbit := by
    intro g h hgh
    have hga : g • a = h • a := by
      have hcoord := congrArg (fun e : Fin 3 ↪ Omega => e 0) hgh
      change g • a = h • a at hcoord
      exact hcoord
    have hgb : g • b = h • b := by
      have hcoord := congrArg (fun e : Fin 3 ↪ Omega => e 1) hgh
      change g • b = h • b at hcoord
      exact hcoord
    have hgc : g • c = h • c := by
      have hcoord := congrArg (fun e : Fin 3 ↪ Omega => e 2) hgh
      change g • c = h • c at hcoord
      exact hcoord
    have hfixa : (h⁻¹ * g) • a = a := by
      rw [mul_smul, hga, inv_smul_smul]
    have hfixb : (h⁻¹ * g) • b = b := by
      rw [mul_smul, hgb, inv_smul_smul]
    have hfixc : (h⁻¹ * g) • c = c := by
      rw [mul_smul, hgc, inv_smul_smul]
    have hone : h⁻¹ * g = 1 := by
      by_contra hne
      exact hatMostTwoFixedPoints (h⁻¹ * g) hne a b c hab hac hbc
        ⟨hfixa, hfixb, hfixc⟩
    exact (inv_mul_eq_one.mp hone).symm
  have horbitCard : Nat.card G = Nat.card (Fin 3 ↪ Omega) := by
    calc
      Nat.card G = (Fintype.card Omega).descFactorial 3 := hcard
      _ = Fintype.card (Fin 3 ↪ Omega) := by
        rw [Fintype.card_embedding_eq, Fintype.card_fin]
      _ = Nat.card (Fin 3 ↪ Omega) := Nat.card_eq_fintype_card.symm
  have horbitSurjective : Function.Surjective orbit :=
    ((Nat.bijective_iff_injective_and_card orbit).2
      ⟨horbitInjective, horbitCard⟩).2
  rcases horbitSurjective target with ⟨g, hg⟩
  refine ⟨g, ?_, ?_⟩
  · have h0 := congrArg (fun e : Fin 3 ↪ Omega => e 0) hg
    have h1 := congrArg (fun e : Fin 3 ↪ Omega => e 1) hg
    have h2 := congrArg (fun e : Fin 3 ↪ Omega => e 2) hg
    change g • a = a' at h0
    change g • b = b' at h1
    change g • c = c' at h2
    exact ⟨h0, ⟨h1, h2⟩⟩
  · intro h hh
    have hg0 : g • a = a' := by
      have hcoord := congrArg (fun e : Fin 3 ↪ Omega => e 0) hg
      change g • a = a' at hcoord
      exact hcoord
    have hg1 : g • b = b' := by
      have hcoord := congrArg (fun e : Fin 3 ↪ Omega => e 1) hg
      change g • b = b' at hcoord
      exact hcoord
    have hg2 : g • c = c' := by
      have hcoord := congrArg (fun e : Fin 3 ↪ Omega => e 2) hg
      change g • c = c' at hcoord
      exact hcoord
    apply horbitInjective
    ext i
    fin_cases i
    · have hcoord := hh.1.trans hg0.symm
      change h • a = g • a at hcoord
      exact hcoord
    · have hcoord := hh.2.1.trans hg1.symm
      change h • b = g • b at hcoord
      exact hcoord
    · have hcoord := hh.2.2.trans hg2.symm
      change h • c = g • c at hcoord
      exact hcoord
private theorem xi1115_rankOneOrbit_sharpTriple
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (M B : Subgroup G) (a : Omega) (q : ℕ)
    (hB_le_M : B ≤ M)
    (hstab : MulAction.stabilizer M a = B.subgroupOf M)
    (hMcard : Nat.card M = (q + 1) * q * (q - 1))
    (hBcard : Nat.card B = q * (q - 1))
    (hq : 2 ≤ q)
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ x y z : Omega,
          x ≠ y → x ≠ z → y ≠ z →
            ¬ (g • x = x ∧ g • y = y ∧ g • z = z)) :
    let O := MulAction.orbit M a
    ∀ x y z x' y' z' : O,
      x ≠ y → x ≠ z → y ≠ z →
        x' ≠ y' → x' ≠ z' → y' ≠ z' →
          ∃! g : M,
            g • x = x' ∧ g • y = y' ∧ g • z = z' := by
  classical
  let O := MulAction.orbit M a
  letI : Fintype M := Fintype.ofFinite M
  letI : Fintype O := Fintype.ofFinite O
  letI : Fintype (MulAction.stabilizer M a) := Fintype.ofFinite _
  have hBsubCard : Nat.card (B.subgroupOf M) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB_le_M).toEquiv
  have hOrbitMul :
      Nat.card O * Nat.card (MulAction.stabilizer M a) = Nat.card M := by
    simpa only [Nat.card_eq_fintype_card] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group M a)
  have hfactorPos : 0 < q * (q - 1) :=
    Nat.mul_pos (by omega) (by omega)
  have hOrbitCard : Nat.card O = q + 1 := by
    apply Nat.eq_of_mul_eq_mul_right hfactorPos
    calc
      Nat.card O * (q * (q - 1)) =
          Nat.card O * Nat.card (MulAction.stabilizer M a) := by
            rw [hstab, hBsubCard, hBcard]
      _ = Nat.card M := hOrbitMul
      _ = (q + 1) * q * (q - 1) := hMcard
      _ = (q + 1) * (q * (q - 1)) := by ring
  have hOrbitFintypeCard : Fintype.card O = q + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hOrbitCard
  have hMdesc : Nat.card M = (Fintype.card O).descFactorial 3 := by
    rw [hOrbitFintypeCard, hMcard]
    simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
      Nat.sub_zero, mul_one]
    rw [show q + 1 - 1 = q by omega, show q + 1 - 2 = q - 1 by omega]
    ring
  have hOrbitAtMostTwo :
      ∀ g : M, g ≠ 1 →
        ∀ x y z : O,
          x ≠ y → x ≠ z → y ≠ z →
            ¬ (g • x = x ∧ g • y = y ∧ g • z = z) := by
    intro g hg x y z hxy hxz hyz hfix
    have hgG : (g : G) ≠ 1 := by
      intro h
      apply hg
      exact Subtype.ext h
    have hxyG : (x : Omega) ≠ (y : Omega) := by
      intro h
      exact hxy (Subtype.ext h)
    have hxzG : (x : Omega) ≠ (z : Omega) := by
      intro h
      exact hxz (Subtype.ext h)
    have hyzG : (y : Omega) ≠ (z : Omega) := by
      intro h
      exact hyz (Subtype.ext h)
    apply hatMostTwoFixedPoints (g : G) hgG
      (x : Omega) (y : Omega) (z : Omega) hxyG hxzG hyzG
    exact ⟨congrArg Subtype.val hfix.1,
      congrArg Subtype.val hfix.2.1,
      congrArg Subtype.val hfix.2.2⟩
  exact xi1115_sharpTriple_of_card_eq_descFactorial hMdesc hOrbitAtMostTwo
private theorem xi1115_centralizer_card_eq_of_isConj
    {G : Type*} [Group G] [Finite G]
    (t z : G) (hconj : IsConj t z) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) =
      Nat.card (Subgroup.centralizer ({z} : Set G)) := by
  rw [isConj_iff] at hconj
  rcases hconj with ⟨g, hg⟩
  let Ct := Subgroup.centralizer ({t} : Set G)
  let Cz := Subgroup.centralizer ({z} : Set G)
  let e : Ct ≃ Cz :=
    { toFun := fun x => ⟨g * (x : G) * g⁻¹, by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        rw [← hg]
        have hx : (x : G) * t = t * (x : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp x.property
        calc
          (g * (x : G) * g⁻¹) * (g * t * g⁻¹) =
              g * ((x : G) * t) * g⁻¹ := by group
          _ = g * (t * (x : G)) * g⁻¹ := by rw [hx]
          _ = (g * t * g⁻¹) * (g * (x : G) * g⁻¹) := by group⟩
      invFun := fun y => ⟨g⁻¹ * (y : G) * g, by
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        have ht : t = g⁻¹ * z * g := by
          rw [← hg]
          group
        rw [ht]
        have hy : (y : G) * z = z * (y : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp y.property
        calc
          (g⁻¹ * (y : G) * g) * (g⁻¹ * z * g) =
              g⁻¹ * ((y : G) * z) * g := by group
          _ = g⁻¹ * (z * (y : G)) * g := by rw [hy]
          _ = (g⁻¹ * z * g) * (g⁻¹ * (y : G) * g) := by group⟩
      left_inv := by
        intro x
        apply Subtype.ext
        simp [mul_assoc]
      right_inv := by
        intro y
        apply Subtype.ext
        simp [mul_assoc] }
  exact Nat.card_congr e

private theorem xi1115_involution_centralizer_regular_on_punctured
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (t : G) (htorder : orderOf t = 2)
    (c : Omega) (htc : t • c = c)
    (hcuniq : ∀ x : Omega, t • x = x → x = c)
    (hcard : Nat.card (Subgroup.centralizer ({t} : Set G)) =
      Fintype.card Omega - 1) :
    ∀ x : Omega, x ≠ c → ∀ y : Omega, y ≠ c →
      ∃! z : Subgroup.centralizer ({t} : Set G), (z : G) • x = y := by
  classical
  let C := Subgroup.centralizer ({t} : Set G)
  have htsq : t * t = 1 := by
    simpa [pow_two] using (show t ^ 2 = 1 by
      rw [← htorder]
      exact pow_orderOf_eq_one t)
  have hfixC : ∀ z : C, (z : G) • c = c := by
    intro z
    have hzcomm : (z : G) * t = t * (z : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp z.property
    apply hcuniq
    calc
      t • ((z : G) • c) = (t * (z : G)) • c := by rw [mul_smul]
      _ = ((z : G) * t) • c := by rw [hzcomm]
      _ = (z : G) • (t • c) := by rw [mul_smul]
      _ = (z : G) • c := by rw [htc]
  have hfree : ∀ z : C, ∀ x : Omega, x ≠ c →
      (z : G) • x = x → z = 1 := by
    intro z x hxc hzx
    by_contra hz1
    have hzG1 : (z : G) ≠ 1 := by
      intro h
      apply hz1
      apply Subtype.ext
      exact h
    have htx_ne_x : t • x ≠ x := by
      intro h
      exact hxc (hcuniq x h)
    have htx_ne_c : t • x ≠ c := by
      intro h
      have h' : t • (t • x) = t • c :=
        congrArg (fun y : Omega => t • y) h
      apply hxc
      calc
        x = t • (t • x) := by rw [← mul_smul, htsq, one_smul]
        _ = t • c := h'
        _ = c := htc
    have hzcomm : (z : G) * t = t * (z : G) :=
      Subgroup.mem_centralizer_singleton_iff.mp z.property
    have hzTx : (z : G) • (t • x) = t • x := by
      calc
        (z : G) • (t • x) = ((z : G) * t) • x := by rw [mul_smul]
        _ = (t * (z : G)) • x := by rw [hzcomm]
        _ = t • ((z : G) • x) := by rw [mul_smul]
        _ = t • x := by rw [hzx]
    exact hatMostTwoFixedPoints (z : G) hzG1 c x (t • x)
      hxc.symm htx_ne_c.symm htx_ne_x.symm
      ⟨hfixC z, hzx, hzTx⟩
  intro x hxc y hyc
  let punctured := {w : Omega // w ≠ c}
  let orbit : C → punctured := fun z =>
    ⟨(z : G) • x, by
      intro h
      have hzc := hfixC z
      apply hxc
      calc
        x = (z : G)⁻¹ • ((z : G) • x) := (inv_smul_smul (z : G) x).symm
        _ = (z : G)⁻¹ • c := by rw [h]
        _ = (z : G)⁻¹ • ((z : G) • c) := by rw [hzc]
        _ = c := inv_smul_smul (z : G) c⟩
  have horbitInjective : Function.Injective orbit := by
    intro z w hzw
    have hsmul : (z : G) • x = (w : G) • x :=
      congrArg Subtype.val hzw
    let q : C := w⁻¹ * z
    have hqfix : (q : G) • x = x := by
      change ((w : G)⁻¹ * (z : G)) • x = x
      rw [mul_smul, hsmul, inv_smul_smul]
    have hqone : q = 1 := hfree q x hxc hqfix
    have hqoneG : (w : G)⁻¹ * (z : G) = 1 :=
      congrArg Subtype.val hqone
    apply Subtype.ext
    exact (inv_mul_eq_one.mp hqoneG).symm
  have hpuncturedCard : Nat.card punctured = Fintype.card Omega - 1 := by
    dsimp [punctured]
    rw [Nat.card_eq_fintype_card]
    simp
  have hcardEq : Nat.card C = Nat.card punctured := by
    rw [hpuncturedCard]
    exact hcard
  have horbitSurjective : Function.Surjective orbit := by
    letI : Fintype C := Fintype.ofFinite C
    letI : Fintype punctured := Fintype.ofFinite punctured
    exact ((Fintype.bijective_iff_injective_and_card orbit).mpr
      ⟨horbitInjective, by
        simpa only [Nat.card_eq_fintype_card] using hcardEq⟩).2
  rcases horbitSurjective ⟨y, hyc⟩ with ⟨z, hz⟩
  refine ⟨z, congrArg Subtype.val hz, ?_⟩
  intro w hw
  apply horbitInjective
  apply Subtype.ext
  exact hw.trans (congrArg Subtype.val hz).symm


private theorem xi1115_involution_centralizer_card_eq_kernel
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (t : G)
    (hallInvolutionsConj : ∀ u : G, orderOf u = 2 → IsConj u t) :
    Nat.card (Subgroup.centralizer ({t} : Set G)) = Nat.card F := by
  let H := MulAction.stabilizer G a
  letI : Nontrivial F :=
    (Subgroup.nontrivial_iff_ne_bot F).mpr hFrob.kernel_ne_bot
  obtain ⟨zc, hzcorder⟩ :=
    xi1115_exists_central_involution
      (F := F) (inferInstance : Nontrivial F) hF2
  let zF : F := zc
  let zG : G := (((zF : F) : H) : G)
  have hzForder : orderOf zF = 2 := by
    calc
      orderOf zF = orderOf (zc : F) := rfl
      _ = orderOf zc := (Subgroup.orderOf_coe (zc : Subgroup.center F))
      _ = 2 := hzcorder
  have hzGorder : orderOf zG = 2 := by
    calc
      orderOf zG = orderOf ((zF : H) : G) := rfl
      _ = orderOf (zF : H) := (Subgroup.orderOf_coe (zF : H))
      _ = orderOf zF := (Subgroup.orderOf_coe (zF : F))
      _ = 2 := hzForder
  have hzFne : zF ≠ 1 := (orderOf_eq_prime_iff.mp hzForder).2
  have hCzLe : Subgroup.centralizer ({zG} : Set G) ≤ F.map H.subtype := by
    simpa [H, zG] using
      xi1115_frobeniusKernel_ambient_centralizer_le
        htwo a b hab F hFrob zF hzFne
  have hFmapLe : F.map H.subtype ≤ Subgroup.centralizer ({zG} : Set G) := by
    rintro x ⟨y, hy, rfl⟩
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    let yF : F := ⟨y, hy⟩
    have hyzF : yF * zF = zF * yF :=
      Subgroup.mem_center_iff.mp zc.property yF
    simpa [zG, zF, yF] using
      congrArg (fun q : F => (((q : F) : H) : G)) hyzF
  have hCzEq :
      Subgroup.centralizer ({zG} : Set G) = F.map H.subtype :=
    le_antisymm hCzLe hFmapLe
  have hCzCard :
      Nat.card (Subgroup.centralizer ({zG} : Set G)) = Nat.card F := by
    rw [hCzEq]
    exact Nat.card_congr
      (Subgroup.equivMapOfInjective (f := H.subtype) F
        H.subtype_injective).toEquiv.symm
  calc
    Nat.card (Subgroup.centralizer ({t} : Set G)) =
        Nat.card (Subgroup.centralizer ({zG} : Set G)) :=
      xi1115_centralizer_card_eq_of_isConj
        t zG (hallInvolutionsConj zG hzGorder).symm
    _ = Nat.card F := hCzCard


private theorem xi1115_stronglyReal_centralizer_card_odd
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s)
    (x : G) (hxStrong : PFAppendixIII.IsStronglyReal x)
    (hxsq : x ^ 2 ≠ 1) :
    Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) := by
  have hxOdd : Odd (orderOf x) :=
    xi1115_stronglyReal_sq_ne_one_order_odd
      htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
      a b hab F hFrob hFSuzuki x hxStrong hxsq
  apply Nat.not_even_iff_odd.mp
  intro hcardEven
  obtain ⟨y, hyorder⟩ :=
    exists_prime_orderOf_dvd_card'
      (G := Subgroup.centralizer ({x} : Set G)) 2
      (even_iff_two_dvd.mp hcardEven)
  let yG : G := y
  have hyGorder : orderOf yG = 2 := by
    calc
      orderOf yG = orderOf y := by
        simp [yG]
      _ = 2 := hyorder
  have hallY : ∀ u : G, orderOf u = 2 → IsConj u yG := by
    intro u huorder
    exact (hallInvolutionsConj u huorder).trans
      (hallInvolutionsConj yG hyGorder).symm
  have hCyCard :
      Nat.card (Subgroup.centralizer ({yG} : Set G)) = Nat.card F :=
    xi1115_involution_centralizer_card_eq_kernel
      htwo a b hab F hFrob hF2 yG hallY
  have hCy2 : IsPGroup 2 (Subgroup.centralizer ({yG} : Set G)) := by
    rcases IsPGroup.iff_card.mp hF2 with ⟨k, hk⟩
    exact IsPGroup.iff_card.mpr ⟨k, hCyCard.trans hk⟩
  have hycommx : yG * x = x * yG := by
    simpa [yG] using
      (Subgroup.mem_centralizer_singleton_iff.mp y.property)
  let xCy : Subgroup.centralizer ({yG} : Set G) :=
    ⟨x, Subgroup.mem_centralizer_singleton_iff.mpr hycommx.symm⟩
  have hxCyOdd : Odd (orderOf xCy) := by
    simpa [xCy] using hxOdd
  have hcop : (orderOf xCy).Coprime (orderOf xCy) :=
    hCy2.orderOf_coprime hxCyOdd.coprime_two_left xCy
  have hxCyOrderOne : orderOf xCy = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  have hxCyOne : xCy = 1 := orderOf_eq_one_iff.mp hxCyOrderOne
  have hxOne : x = 1 := by
    exact congrArg
      (fun z : Subgroup.centralizer ({yG} : Set G) => (z : G)) hxCyOne
  apply hxsq
  simp [hxOne]
private theorem xi1115_stronglyReal_centralizer_structure
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s)
    (x : G) (hxStrong : PFAppendixIII.IsStronglyReal x)
    (hxsq : x ^ 2 ≠ 1) :
    IsMulCommutative (Subgroup.centralizer ({x} : Set G)) ∧
      ∃ t : G, PFAppendixIII.IsInvolution t ∧
        ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) →
          t * z * t⁻¹ = z⁻¹ := by
  have hCodd : Odd (Nat.card (Subgroup.centralizer ({x} : Set G))) :=
    xi1115_stronglyReal_centralizer_card_odd
      htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
      a b hab F hFrob hF2 hFSuzuki s hallInvolutionsConj
      x hxStrong hxsq
  rcases hxStrong with ⟨t, u, htInv, huInv, rfl⟩
  let C := Subgroup.centralizer ({t * u} : Set G)
  have htt : t * t = 1 := by
    simpa [pow_two] using htInv.sq_eq_one
  have htxInv : t * (t * u) * t⁻¹ = (t * u)⁻¹ := by
    calc
      t * (t * u) * t⁻¹ = (t * t) * u * t := by
        rw [htInv.inv_eq_self]
        group
      _ = u * t := by rw [htt]; simp
      _ = (t * u)⁻¹ := by
        simp [mul_inv_rev, htInv.inv_eq_self, huInv.inv_eq_self]
  have htForward : ∀ z : G, z ∈ C → t * z * t⁻¹ ∈ C := by
    intro z hz
    have hzx : z * (t * u) = (t * u) * z := by
      exact Subgroup.mem_centralizer_singleton_iff.mp (by simpa [C] using hz)
    have hconjComm :
        (t * z * t⁻¹) * (t * (t * u) * t⁻¹) =
          (t * (t * u) * t⁻¹) * (t * z * t⁻¹) := by
      calc
        (t * z * t⁻¹) * (t * (t * u) * t⁻¹) =
            t * (z * (t * u)) * t⁻¹ := by group
        _ = t * ((t * u) * z) * t⁻¹ := by rw [hzx]
        _ = (t * (t * u) * t⁻¹) * (t * z * t⁻¹) := by group
    rw [htxInv] at hconjComm
    have hcommInv : Commute (t * z * t⁻¹) (t * u)⁻¹ := hconjComm
    have hcomm : Commute (t * z * t⁻¹) (t * u) := by
      simpa using hcommInv.inv_right
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  have htNorm : t ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact htForward z
    · intro hz
      have hback := htForward (t * z * t⁻¹) hz
      have hconjBack : t * (t * z * t⁻¹) * t⁻¹ = z := by
        rw [htInv.inv_eq_self]
        calc
          t * (t * z * t) * t = (t * t) * z * (t * t) := by group
          _ = z := by rw [htt]; simp
      simpa only [hconjBack] using hback
  let tN : Subgroup.normalizer (C : Set G) := ⟨t, htNorm⟩
  let phi : MulAut C := C.normalizerMonoidHom tN
  have hphiSq : phi ^ 2 = 1 := by
    change (C.normalizerMonoidHom tN) ^ 2 = 1
    have htNSq : tN ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using htInv.sq_eq_one
    rw [← map_pow, htNSq, map_one]
  have hphiInv : Function.Involutive phi := by
    intro z
    have hz := congrArg (fun psi : MulAut C => psi z) hphiSq
    simpa [pow_two] using hz
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime htInv.sq_eq_one htInv.ne_one
  have hallT : ∀ v : G, orderOf v = 2 → IsConj v t := by
    intro v hvorder
    exact (hallInvolutionsConj v hvorder).trans
      (hallInvolutionsConj t htorder).symm
  have hCtCard :
      Nat.card (Subgroup.centralizer ({t} : Set G)) = Nat.card F :=
    xi1115_involution_centralizer_card_eq_kernel
      htwo a b hab F hFrob hF2 t hallT
  have hCt2 : IsPGroup 2 (Subgroup.centralizer ({t} : Set G)) := by
    rcases IsPGroup.iff_card.mp hF2 with ⟨k, hk⟩
    exact IsPGroup.iff_card.mpr ⟨k, hCtCard.trans hk⟩
  have hphiFree : MonoidHom.FixedPointFree phi := by
    intro z hz
    have hzconj : t * (z : G) * t⁻¹ = (z : G) := by
      simpa [phi, tN, C,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using
          congrArg Subtype.val hz
    have htcommz : Commute t (z : G) := by
      apply commutatorElement_eq_one_iff_commute.mp
      simp [commutatorElement_def, hzconj]
    let zCt : Subgroup.centralizer ({t} : Set G) :=
      ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr htcommz.eq.symm⟩
    have hzOdd : Odd (orderOf z) :=
      hCodd.of_dvd_nat (orderOf_dvd_natCard z)
    have hzCtOdd : Odd (orderOf zCt) := by
      simpa [zCt] using hzOdd
    have hcop : (orderOf zCt).Coprime (orderOf zCt) :=
      hCt2.orderOf_coprime hzCtOdd.coprime_two_left zCt
    have hzCtOrderOne : orderOf zCt = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
    have hzCtOne : zCt = 1 := orderOf_eq_one_iff.mp hzCtOrderOne
    apply Subtype.ext
    exact congrArg
      (fun q : Subgroup.centralizer ({t} : Set G) => (q : G)) hzCtOne
  have hphiEqInv : ⇑phi = fun z : C => z⁻¹ :=
    hphiFree.coe_eq_inv_of_involutive hphiInv
  have htInverts : ∀ z : G, z ∈ C → t * z * t⁻¹ = z⁻¹ := by
    intro z hz
    let zC : C := ⟨z, hz⟩
    have hzEq := congrArg Subtype.val (congrFun hphiEqInv zC)
    simpa [phi, tN, C, zC,
      Subgroup.normalizerMonoidHom_apply_apply_coe] using hzEq
  constructor
  · refine ⟨⟨fun z w => ?_⟩⟩
    exact (hphiFree.commute_all_of_involutive hphiInv z w).eq
  · exact ⟨t, htInv, by simpa [C] using htInverts⟩
private theorem xi1115_stronglyReal_centralizer_isMulCommutative
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s)
    (x : G) (hxStrong : PFAppendixIII.IsStronglyReal x)
    (hxsq : x ^ 2 ≠ 1) :
    IsMulCommutative (Subgroup.centralizer ({x} : Set G)) :=
  (xi1115_stronglyReal_centralizer_structure
    htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
    a b hab F hFrob hF2 hFSuzuki s hallInvolutionsConj
    x hxStrong hxsq).1
private theorem xi1115_stronglyReal_centralizer_nontrivial
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s)
    (x : G) (hxStrong : PFAppendixIII.IsStronglyReal x)
    (hxsq : x ^ 2 ≠ 1)
    (z : G) (hzmem : z ∈ Subgroup.centralizer ({x} : Set G))
    (hzne : z ≠ 1) :
    PFAppendixIII.IsStronglyReal z ∧
      Subgroup.centralizer ({z} : Set G) =
        Subgroup.centralizer ({x} : Set G) := by
  let Cx := Subgroup.centralizer ({x} : Set G)
  have hCodd : Odd (Nat.card Cx) := by
    simpa [Cx] using
      xi1115_stronglyReal_centralizer_card_odd
        htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
        a b hab F hFrob hF2 hFSuzuki s hallInvolutionsConj
        x hxStrong hxsq
  have hStructure :=
    xi1115_stronglyReal_centralizer_structure
      htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
      a b hab F hFrob hF2 hFSuzuki s hallInvolutionsConj
      x hxStrong hxsq
  obtain ⟨hCxComm, t, htInv, htInverts⟩ := hStructure
  let zCx : Cx := ⟨z, by simpa [Cx] using hzmem⟩
  have hzOdd : Odd (orderOf zCx) :=
    hCodd.of_dvd_nat (orderOf_dvd_natCard zCx)
  have hzsq : z ^ 2 ≠ 1 := by
    intro hzsq
    have hzCxSq : zCx ^ 2 = 1 := by
      apply Subtype.ext
      simpa [zCx] using hzsq
    have hzCxNe : zCx ≠ 1 := by
      intro hzOne
      apply hzne
      exact congrArg (fun q : Cx => (q : G)) hzOne
    have hzCxOrder : orderOf zCx = 2 :=
      orderOf_eq_prime hzCxSq hzCxNe
    exact hzOdd.not_two_dvd_nat (by rw [hzCxOrder])
  have htzInv : t * z * t⁻¹ = z⁻¹ :=
    htInverts z hzmem
  let v : G := t * z
  have hvsq : v ^ 2 = 1 := by
    dsimp [v]
    calc
      (t * z) ^ 2 = (t * z * t⁻¹) * z := by
        rw [pow_two, htInv.inv_eq_self]
        group
      _ = z⁻¹ * z := by rw [htzInv]
      _ = 1 := by simp
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime htInv.sq_eq_one htInv.ne_one
  have htt : t * t = 1 := by
    simpa [pow_two] using htInv.sq_eq_one
  have hvne : v ≠ 1 := by
    intro hvOne
    have hzt : z = t := by
      calc
        z = 1 * z := by simp
        _ = (t * t) * z := by rw [htt]
        _ = t * (t * z) := by group
        _ = t * v := by rfl
        _ = t * 1 := by rw [hvOne]
        _ = t := by simp
    have hzCxOrder : orderOf zCx = 2 := by
      calc
        orderOf zCx = orderOf z := (Subgroup.orderOf_coe zCx).symm
        _ = orderOf t := by rw [hzt]
        _ = 2 := htorder
    exact hzOdd.not_two_dvd_nat (by rw [hzCxOrder])
  have hvInv : PFAppendixIII.IsInvolution v := ⟨hvne, hvsq⟩
  have hzStrong : PFAppendixIII.IsStronglyReal z := by
    refine ⟨t, v, htInv, hvInv, ?_⟩
    dsimp [v]
    calc
      z = 1 * z := by simp
      _ = (t * t) * z := by rw [htt]
      _ = t * (t * z) := by group
  have hCzComm : IsMulCommutative
      (Subgroup.centralizer ({z} : Set G)) :=
    xi1115_stronglyReal_centralizer_isMulCommutative
      htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
      a b hab F hFrob hF2 hFSuzuki s hallInvolutionsConj
      z hzStrong hzsq
  have hCxLeCz : Cx ≤ Subgroup.centralizer ({z} : Set G) := by
    intro y hy
    let yCx : Cx := ⟨y, hy⟩
    have hyz : yCx * zCx = zCx * yCx :=
      (@IsMulCommutative.is_comm Cx _ hCxComm).comm yCx zCx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa [yCx, zCx] using congrArg Subtype.val hyz)
  have hxmemCz : x ∈ Subgroup.centralizer ({z} : Set G) := by
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp hzmem).symm
  have hCzLeCx : Subgroup.centralizer ({z} : Set G) ≤ Cx := by
    intro y hy
    let yCz : Subgroup.centralizer ({z} : Set G) := ⟨y, hy⟩
    let xCz : Subgroup.centralizer ({z} : Set G) := ⟨x, hxmemCz⟩
    have hyx : yCz * xCz = xCz * yCz :=
      (@IsMulCommutative.is_comm _ _ hCzComm).comm yCz xCz
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (by simpa [Cx, yCz, xCz] using congrArg Subtype.val hyx)
  exact ⟨hzStrong, le_antisymm hCzLeCx hCxLeCz⟩

private theorem xi1115_square_surjective_of_odd_card
    {A : Type*} [CommGroup A] [Finite A]
    (hAodd : Odd (Nat.card A)) :
    Function.Surjective (fun x : A => x ^ 2) := by
  apply Finite.injective_iff_surjective.mp
  intro x y hxy
  change x ^ 2 = y ^ 2 at hxy
  have hsq : (y⁻¹ * x) ^ 2 = 1 := by
    rw [mul_pow, inv_pow, hxy, inv_mul_cancel]
  have hordDvdTwo : orderOf (y⁻¹ * x) ∣ 2 :=
    orderOf_dvd_of_pow_eq_one hsq
  have hordOdd : Odd (orderOf (y⁻¹ * x)) :=
    hAodd.of_dvd_nat (orderOf_dvd_natCard (y⁻¹ * x))
  have hordOne : orderOf (y⁻¹ * x) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hordDvdTwo with h | h
    · exact h
    · exfalso
      exact hordOdd.not_two_dvd_nat (by rw [h])
  have hyx : y⁻¹ * x = 1 := orderOf_eq_one_iff.mp hordOne
  exact (inv_mul_eq_one.mp hyx).symm

private theorem xi1115_inverting_involutions_conj_by_centralizer
    {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) (x s t : G)
    (hCcentralizer : C = Subgroup.centralizer ({x} : Set G))
    (hxC : x ∈ C) (_hxne : x ≠ 1)
    (hCcomm : IsMulCommutative C) (hCodd : Odd (Nat.card C))
    (_hss : s * s = 1) (htt : t * t = 1)
    (hsInv : ∀ z : G, z ∈ C → s * z * s⁻¹ = z⁻¹)
    (htInv : ∀ z : G, z ∈ C → t * z * t⁻¹ = z⁻¹) :
    ∃ c : G, c ∈ C ∧ c * t * c⁻¹ = s := by
  let r : G := s * t
  have hrconj : r * x * r⁻¹ = x := by
    dsimp [r]
    calc
      (s * t) * x * (s * t)⁻¹ =
          s * (t * x * t⁻¹) * s⁻¹ := by group
      _ = s * x⁻¹ * s⁻¹ := by rw [htInv x hxC]
      _ = (s * x * s⁻¹)⁻¹ := by group
      _ = (x⁻¹)⁻¹ := by rw [hsInv x hxC]
      _ = x := inv_inv x
  have hrcomm : r * x = x * r := by
    have h := congrArg (fun z : G => z * r) hrconj
    simpa [mul_assoc] using h
  have hrC : r ∈ C := by
    rw [hCcentralizer]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hrcomm
  let rC : C := ⟨r, hrC⟩
  letI : IsMulCommutative C := hCcomm
  obtain ⟨c, hc⟩ :=
    xi1115_square_surjective_of_odd_card hCodd rC
  have hcG : (c : G) * (c : G) = r := by
    simpa [pow_two, rC] using congrArg Subtype.val hc
  have htInvSelf : t⁻¹ = t :=
    inv_eq_of_mul_eq_one_right htt
  have htMove : t * (c : G)⁻¹ = (c : G) * t := by
    calc
      t * (c : G)⁻¹ = t * (t * (c : G) * t⁻¹) := by
        rw [htInv (c : G) c.property]
      _ = (t * t) * (c : G) * t⁻¹ := by group
      _ = (c : G) * t⁻¹ := by rw [htt, one_mul]
      _ = (c : G) * t := by rw [htInvSelf]
  refine ⟨c, c.property, ?_⟩
  calc
    (c : G) * t * (c : G)⁻¹ =
        (c : G) * (t * (c : G)⁻¹) := by group
    _ = (c : G) * ((c : G) * t) := by rw [htMove]
    _ = ((c : G) * (c : G)) * t := by group
    _ = r * t := by rw [hcG]
    _ = s := by dsimp [r]; rw [mul_assoc, htt, mul_one]

private theorem xi1115_involution_inverts_odd_centralizer
    {G : Type*} [Group G] [Finite G]
    (C : Subgroup G) (x t : G)
    (hCcentralizer : C = Subgroup.centralizer ({x} : Set G))
    (hCodd : Odd (Nat.card C))
    (hCt2 : IsPGroup 2 (Subgroup.centralizer ({t} : Set G)))
    (htt : t * t = 1)
    (htxInv : t * x * t⁻¹ = x⁻¹) :
    ∀ z : G, z ∈ C → t * z * t⁻¹ = z⁻¹ := by
  have htInvSelf : t⁻¹ = t :=
    inv_eq_of_mul_eq_one_right htt
  have htForward : ∀ z : G, z ∈ C → t * z * t⁻¹ ∈ C := by
    intro z hz
    have hzx : z * x = x * z := by
      exact Subgroup.mem_centralizer_singleton_iff.mp
        (by simpa [hCcentralizer] using hz)
    have hconjComm :
        (t * z * t⁻¹) * (t * x * t⁻¹) =
          (t * x * t⁻¹) * (t * z * t⁻¹) := by
      calc
        (t * z * t⁻¹) * (t * x * t⁻¹) =
            t * (z * x) * t⁻¹ := by group
        _ = t * (x * z) * t⁻¹ := by rw [hzx]
        _ = (t * x * t⁻¹) * (t * z * t⁻¹) := by group
    rw [htxInv] at hconjComm
    have hcommInv : Commute (t * z * t⁻¹) x⁻¹ := hconjComm
    have hcomm : Commute (t * z * t⁻¹) x := by
      simpa using hcommInv.inv_right
    rw [hCcentralizer]
    exact Subgroup.mem_centralizer_singleton_iff.mpr hcomm.eq
  have htNorm : t ∈ Subgroup.normalizer (C : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact htForward z
    · intro hz
      have hback := htForward (t * z * t⁻¹) hz
      have hconjBack : t * (t * z * t⁻¹) * t⁻¹ = z := by
        rw [htInvSelf]
        calc
          t * (t * z * t) * t = (t * t) * z * (t * t) := by group
          _ = z := by rw [htt]; simp
      simpa only [hconjBack] using hback
  let tN : Subgroup.normalizer (C : Set G) := ⟨t, htNorm⟩
  let phi : MulAut C := C.normalizerMonoidHom tN
  have hphiSq : phi ^ 2 = 1 := by
    change (C.normalizerMonoidHom tN) ^ 2 = 1
    have htNSq : tN ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using htt
    rw [← map_pow, htNSq, map_one]
  have hphiInv : Function.Involutive phi := by
    intro z
    have hz := congrArg (fun psi : MulAut C => psi z) hphiSq
    simpa [pow_two] using hz
  have hphiFree : MonoidHom.FixedPointFree phi := by
    intro z hz
    have hzconj : t * (z : G) * t⁻¹ = (z : G) := by
      simpa [phi, tN,
        Subgroup.normalizerMonoidHom_apply_apply_coe] using
          congrArg Subtype.val hz
    have htcommz : Commute t (z : G) := by
      apply commutatorElement_eq_one_iff_commute.mp
      simp [commutatorElement_def, hzconj]
    let zCt : Subgroup.centralizer ({t} : Set G) :=
      ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr htcommz.eq.symm⟩
    have hzOdd : Odd (orderOf z) :=
      hCodd.of_dvd_nat (orderOf_dvd_natCard z)
    have hzCtOdd : Odd (orderOf zCt) := by
      simpa [zCt] using hzOdd
    have hcop : (orderOf zCt).Coprime (orderOf zCt) :=
      hCt2.orderOf_coprime hzCtOdd.coprime_two_left zCt
    have hzCtOrderOne : orderOf zCt = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
    have hzCtOne : zCt = 1 := orderOf_eq_one_iff.mp hzCtOrderOne
    apply Subtype.ext
    exact congrArg
      (fun q : Subgroup.centralizer ({t} : Set G) => (q : G)) hzCtOne
  have hphiEqInv : ⇑phi = fun z : C => z⁻¹ :=
    hphiFree.coe_eq_inv_of_involutive hphiInv
  intro z hz
  let zC : C := ⟨z, hz⟩
  have hzEq := congrArg Subtype.val (congrFun hphiEqInv zC)
  simpa [phi, tN, zC,
    Subgroup.normalizerMonoidHom_apply_apply_coe] using hzEq

private theorem xi1115_stronglyReal_isConj_swap_mul_kernelInvolution
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hsorder : orderOf s = 2) (hsa : s • a = b)
    (hallInvolutionsConj : ∀ t : G, orderOf t = 2 → IsConj t s)
    (x : G) (hxStrong : PFAppendixIII.IsStronglyReal x)
    (hxsq : x ^ 2 ≠ 1) :
    ∃ j : F, orderOf j = 2 ∧
      IsConj x
        (s * (((j : F) : MulAction.stabilizer G a) : G)) := by
  classical
  rcases hxStrong with ⟨t, u, htInv, huInv, rfl⟩
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime htInv.sq_eq_one htInv.ne_one
  have huorder : orderOf u = 2 :=
    orderOf_eq_prime huInv.sq_eq_one huInv.ne_one
  obtain ⟨p, htfix, _htuniq⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints t htorder
  obtain ⟨q, hufix, _huuniq⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints u huorder
  have hpq : p ≠ q := by
    intro hpq
    subst q
    have hcomm : Commute t u :=
      xi1115_sameFixedPoint_involutions_commute
        htwo hdegreeOdd hatMostTwoFixedPoints a b hab F hFrob hFSuzuki
        t u htorder huorder p htfix hufix
    have htt : t * t = 1 := by
      simpa [pow_two] using htInv.sq_eq_one
    have huu : u * u = 1 := by
      simpa [pow_two] using huInv.sq_eq_one
    apply hxsq
    rw [pow_two]
    calc
      (t * u) * (t * u) = t * (u * t) * u := by group
      _ = t * (t * u) * u := by rw [hcomm.eq.symm]
      _ = (t * t) * (u * u) := by group
      _ = 1 := by rw [htt, huu, one_mul]
  obtain ⟨c, hsc, hscuniq⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints s hsorder
  have hca : c ≠ a := by
    intro hca
    apply hab
    have hsfixa : s • a = a := by simpa [hca] using hsc
    exact hsfixa.symm.trans hsa
  obtain ⟨k, hkp, hkq⟩ :=
    (MulAction.is_two_pretransitive_iff.mp htwo) hpq hca
  let t1 : G := k * t * k⁻¹
  let u1 : G := k * u * k⁻¹
  have ht1order : orderOf t1 = 2 :=
    ((MulAut.conj k).orderOf_eq t).trans htorder
  have hu1order : orderOf u1 = 2 :=
    ((MulAut.conj k).orderOf_eq u).trans huorder
  have hkinvc : k⁻¹ • c = p := by
    calc
      k⁻¹ • c = k⁻¹ • (k • p) := by rw [hkp]
      _ = p := inv_smul_smul k p
  have hkinva : k⁻¹ • a = q := by
    calc
      k⁻¹ • a = k⁻¹ • (k • q) := by rw [hkq]
      _ = q := inv_smul_smul k q
  have ht1fix : t1 • c = c := by
    dsimp [t1]
    simp only [mul_smul]
    rw [hkinvc, htfix, hkp]
  have hu1fix : u1 • a = a := by
    dsimp [u1]
    simp only [mul_smul]
    rw [hkinva, hufix, hkq]
  have ht1Conj : IsConj t1 s := hallInvolutionsConj t1 ht1order
  rw [isConj_iff] at ht1Conj
  rcases ht1Conj with ⟨h, hh⟩
  have hhfixc : h • c = c := by
    apply hscuniq
    calc
      s • (h • c) = (h * t1 * h⁻¹) • (h • c) := by rw [hh]
      _ = h • (t1 • c) := by simp only [mul_smul, inv_smul_smul]
      _ = h • c := by rw [ht1fix]
  have hhane : h • a ≠ c := by
    intro hha
    apply hca
    apply (MulAction.toPerm h).injective
    change h • c = h • a
    rw [hhfixc, hha]
  have hCsCard :
      Nat.card (Subgroup.centralizer ({s} : Set G)) = Nat.card F :=
    xi1115_involution_centralizer_card_eq_kernel
      htwo a b hab F hFrob hF2 s hallInvolutionsConj
  have hCsCardPunctured :
      Nat.card (Subgroup.centralizer ({s} : Set G)) =
        Fintype.card Omega - 1 := by
    rw [hCsCard]
    have hOmegaCard : 1 < Fintype.card Omega :=
      Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    have hFcard :=
      huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
        (Fintype.card Omega - 1) (by omega)
        htwo a b hab F hFrob
    exact hFcard
  obtain ⟨z, hzmap, _hzuniq⟩ :=
    xi1115_involution_centralizer_regular_on_punctured
      hatMostTwoFixedPoints s hsorder c hsc hscuniq hCsCardPunctured
      (h • a) hhane a hca.symm
  let u2 : G := h * u1 * h⁻¹
  let u3 : G := (z : G) * u2 * (z : G)⁻¹
  have hu2fix : u2 • (h • a) = h • a := by
    dsimp [u2]
    calc
      (h * u1 * h⁻¹) • (h • a) = h • (u1 • a) := by
        simp only [mul_smul, inv_smul_smul]
      _ = h • a := by rw [hu1fix]
  have hu3fix : u3 • a = a := by
    dsimp [u3]
    have hzinva : (z : G)⁻¹ • a = h • a := by
      calc
        (z : G)⁻¹ • a = (z : G)⁻¹ • ((z : G) • (h • a)) := by rw [hzmap]
        _ = h • a := inv_smul_smul (z : G) (h • a)
    simp only [mul_smul]
    rw [hzinva, hu2fix, hzmap]
  have hu3order : orderOf u3 = 2 := by
    calc
      orderOf u3 = orderOf u2 := (MulAut.conj (z : G)).orderOf_eq u2
      _ = orderOf u1 := (MulAut.conj h).orderOf_eq u1
      _ = 2 := hu1order
  let u3H : MulAction.stabilizer G a := ⟨u3, hu3fix⟩
  have hu3Fmem : u3H ∈ F :=
    xi1115_involution_mem_frobeniusKernel_of_fixedPoint
      htwo hdegreeOdd hatMostTwoFixedPoints a b hab F hFrob
      u3 hu3order hu3fix
  let j : F := ⟨u3H, hu3Fmem⟩
  have hjorder : orderOf j = 2 := by
    calc
      orderOf j = orderOf u3H := Subgroup.orderOf_mk _ _
      _ = orderOf u3 := Subgroup.orderOf_mk _ _
      _ = 2 := hu3order
  refine ⟨j, hjorder, ?_⟩
  rw [isConj_iff]
  let w : G := (z : G) * h * k
  refine ⟨w, ?_⟩
  have hzcomm : (z : G) * s = s * (z : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp z.property
  have htImage : w * t * w⁻¹ = s := by
    dsimp [w]
    calc
      ((z : G) * h * k) * t * ((z : G) * h * k)⁻¹ =
          (z : G) * (h * (k * t * k⁻¹) * h⁻¹) * (z : G)⁻¹ := by group
      _ = (z : G) * (h * t1 * h⁻¹) * (z : G)⁻¹ := by rfl
      _ = (z : G) * s * (z : G)⁻¹ := by rw [hh]
      _ = s := by
        calc
          (z : G) * s * (z : G)⁻¹ =
              s * (z : G) * (z : G)⁻¹ := by rw [hzcomm]
          _ = s := by simp
  have huImage : w * u * w⁻¹ = u3 := by
    dsimp [w, u1, u2, u3]
    group
  change w * (t * u) * w⁻¹ =
    s * (((j : F) : MulAction.stabilizer G a) : G)
  rw [show (((j : F) : MulAction.stabilizer G a) : G) = u3 from rfl]
  calc
    w * (t * u) * w⁻¹ =
        (w * t * w⁻¹) * (w * u * w⁻¹) := by group
    _ = s * u3 := by rw [htImage, huImage]

private theorem xi1115_swap_mul_kernelInvolution_sq_ne_one
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (s : G) (hsa : s • a = b) (hss : s * s = 1)
    (j : F) (hjorder : orderOf j = 2) :
    (s * (((j : F) : MulAction.stabilizer G a) : G)) ^ 2 ≠ 1 := by
  let jG : G := (((j : F) : MulAction.stabilizer G a) : G)
  have hjSq : jG * jG = 1 := by
    simpa [jG, pow_two] using congrArg
      (fun z : F => (((z : F) : MulAction.stabilizer G a) : G))
      (show j ^ 2 = 1 by
        rw [← hjorder]
        exact pow_orderOf_eq_one j)
  intro hsjSq
  have hsj : s * jG * s * jG = 1 := by
    simpa [pow_two, mul_assoc] using hsjSq
  have hjs : jG * s = s * jG := by
    have hsInvSelf : s⁻¹ = s :=
      inv_eq_of_mul_eq_one_right hss
    have hjInvSelf : jG⁻¹ = jG :=
      inv_eq_of_mul_eq_one_right hjSq
    exact (commutatorElement_eq_one_iff_commute.mp (by
      simpa [commutatorElement_def, hsInvSelf, hjInvSelf,
        mul_assoc] using hsj)).eq.symm
  have hjfixa : jG • a = a := (j : MulAction.stabilizer G a).property
  have hjfixb : jG • b = b := by
    calc
      jG • b = jG • (s • a) := by rw [hsa]
      _ = (jG * s) • a := by rw [mul_smul]
      _ = (s * jG) • a := by rw [hjs]
      _ = s • (jG • a) := by rw [mul_smul]
      _ = b := by rw [hjfixa, hsa]
  have hjne : j ≠ 1 := (orderOf_eq_prime_iff.mp hjorder).2
  have hbEq :=
    (xi1115_frobeniusKernel_uniqueFixedPoint
      htwo a b hab F hFrob j hjne b).mp hjfixb
  exact hab hbEq.symm

private theorem xi1115_swap_mul_kernelInvolution_isConj_iff
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hsorder : orderOf s = 2) (hsa : s • a = b)
    (hallInvolutionsConj : ∀ t : G, orderOf t = 2 → IsConj t s)
    (j1 j2 : F) (hj1order : orderOf j1 = 2)
    (hj2order : orderOf j2 = 2) :
    IsConj
        (s * (((j1 : F) : MulAction.stabilizer G a) : G))
        (s * (((j2 : F) : MulAction.stabilizer G a) : G)) ↔
      j1 = j2 := by
  classical
  let j1G : G := (((j1 : F) : MulAction.stabilizer G a) : G)
  let j2G : G := (((j2 : F) : MulAction.stabilizer G a) : G)
  let x1 : G := s * j1G
  let x2 : G := s * j2G
  have hss : s * s = 1 := by
    simpa [pow_two] using (show s ^ 2 = 1 by
      rw [← hsorder]
      exact pow_orderOf_eq_one s)
  have hj1sq : j1G * j1G = 1 := by
    simpa [j1G, pow_two] using congrArg
      (fun z : F => (((z : F) : MulAction.stabilizer G a) : G))
      (show j1 ^ 2 = 1 by
        rw [← hj1order]
        exact pow_orderOf_eq_one j1)
  have hj2sq : j2G * j2G = 1 := by
    simpa [j2G, pow_two] using congrArg
      (fun z : F => (((z : F) : MulAction.stabilizer G a) : G))
      (show j2 ^ 2 = 1 by
        rw [← hj2order]
        exact pow_orderOf_eq_one j2)
  have hsInv : PFAppendixIII.IsInvolution s :=
    (orderOf_eq_prime_iff.mp hsorder).symm
  have hj1Inv : PFAppendixIII.IsInvolution j1G := by
    refine ⟨?_, by simpa [pow_two] using hj1sq⟩
    intro hj1one
    have hj1oneF : j1 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hj1one
    rw [hj1oneF, orderOf_one] at hj1order
    omega
  have hj2Inv : PFAppendixIII.IsInvolution j2G := by
    refine ⟨?_, by simpa [pow_two] using hj2sq⟩
    intro hj2one
    have hj2oneF : j2 = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hj2one
    rw [hj2oneF, orderOf_one] at hj2order
    omega
  have hx1Strong : PFAppendixIII.IsStronglyReal x1 :=
    ⟨s, j1G, hsInv, hj1Inv, rfl⟩
  have hx2Strong : PFAppendixIII.IsStronglyReal x2 :=
    ⟨s, j2G, hsInv, hj2Inv, rfl⟩
  have hx2sq : x2 ^ 2 ≠ 1 := by
    simpa [x2, j2G] using
      xi1115_swap_mul_kernelInvolution_sq_ne_one
        htwo a b hab F hFrob s hsa hss j2 hj2order
  constructor
  · intro hconj
    rw [isConj_iff] at hconj
    rcases hconj with ⟨g, hg⟩
    let t : G := g * s * g⁻¹
    have htorder : orderOf t = 2 :=
      ((MulAut.conj g).orderOf_eq s).trans hsorder
    have htt : t * t = 1 := by
      simpa [pow_two] using (show t ^ 2 = 1 by
        rw [← htorder]
        exact pow_orderOf_eq_one t)
    let C : Subgroup G := Subgroup.centralizer ({x2} : Set G)
    have hCodd : Odd (Nat.card C) := by
      simpa [C] using
        xi1115_stronglyReal_centralizer_card_odd
          htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
          a b hab F hFrob hF2 hFSuzuki s hallInvolutionsConj
          x2 hx2Strong hx2sq
    have hCcomm : IsMulCommutative C := by
      simpa [C] using
        xi1115_stronglyReal_centralizer_isMulCommutative
          htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
          a b hab F hFrob hF2 hFSuzuki s hallInvolutionsConj
          x2 hx2Strong hx2sq
    have hCsCard :
        Nat.card (Subgroup.centralizer ({s} : Set G)) = Nat.card F :=
      xi1115_involution_centralizer_card_eq_kernel
        htwo a b hab F hFrob hF2 s hallInvolutionsConj
    have hCs2 : IsPGroup 2 (Subgroup.centralizer ({s} : Set G)) := by
      rcases IsPGroup.iff_card.mp hF2 with ⟨r, hr⟩
      exact IsPGroup.iff_card.mpr ⟨r, hCsCard.trans hr⟩
    have hallT : ∀ u : G, orderOf u = 2 → IsConj u t := by
      intro u hu
      exact (hallInvolutionsConj u hu).trans
        (hallInvolutionsConj t htorder).symm
    have hCtCard :
        Nat.card (Subgroup.centralizer ({t} : Set G)) = Nat.card F :=
      xi1115_involution_centralizer_card_eq_kernel
        htwo a b hab F hFrob hF2 t hallT
    have hCt2 : IsPGroup 2 (Subgroup.centralizer ({t} : Set G)) := by
      rcases IsPGroup.iff_card.mp hF2 with ⟨r, hr⟩
      exact IsPGroup.iff_card.mpr ⟨r, hCtCard.trans hr⟩
    have hsx2Inv : s * x2 * s⁻¹ = x2⁻¹ := by
      dsimp [x2]
      have hsInvSelf : s⁻¹ = s :=
        inv_eq_of_mul_eq_one_right hss
      have hj2InvSelf : j2G⁻¹ = j2G :=
        inv_eq_of_mul_eq_one_right hj2sq
      rw [hsInvSelf]
      calc
        s * (s * j2G) * s = j2G * s := by rw [← mul_assoc, hss, one_mul]
        _ = (s * j2G)⁻¹ := by rw [mul_inv_rev, hsInvSelf, hj2InvSelf]
    have hsx1Inv : s * x1 * s⁻¹ = x1⁻¹ := by
      dsimp [x1]
      have hsInvSelf : s⁻¹ = s :=
        inv_eq_of_mul_eq_one_right hss
      have hj1InvSelf : j1G⁻¹ = j1G :=
        inv_eq_of_mul_eq_one_right hj1sq
      rw [hsInvSelf]
      calc
        s * (s * j1G) * s = j1G * s := by rw [← mul_assoc, hss, one_mul]
        _ = (s * j1G)⁻¹ := by rw [mul_inv_rev, hsInvSelf, hj1InvSelf]
    have htx2Inv : t * x2 * t⁻¹ = x2⁻¹ := by
      dsimp [t]
      calc
        (g * s * g⁻¹) * x2 * (g * s * g⁻¹)⁻¹ =
            (g * s * g⁻¹) * (g * x1 * g⁻¹) *
              (g * s * g⁻¹)⁻¹ := by rw [hg]
        _ = g * (s * x1 * s⁻¹) * g⁻¹ := by group
        _ = g * x1⁻¹ * g⁻¹ := by rw [hsx1Inv]
        _ = (g * x1 * g⁻¹)⁻¹ := by group
        _ = x2⁻¹ := by rw [hg]
    have hsInvC : ∀ z : G, z ∈ C → s * z * s⁻¹ = z⁻¹ :=
      xi1115_involution_inverts_odd_centralizer
        C x2 s rfl hCodd hCs2 hss hsx2Inv
    have htInvC : ∀ z : G, z ∈ C → t * z * t⁻¹ = z⁻¹ :=
      xi1115_involution_inverts_odd_centralizer
        C x2 t rfl hCodd hCt2 htt htx2Inv
    have hx2C : x2 ∈ C := by
      exact Subgroup.mem_centralizer_singleton_iff.mpr (Commute.refl x2).eq
    have hx2ne : x2 ≠ 1 := by
      intro hx2one
      apply hx2sq
      simp [hx2one]
    obtain ⟨z, hzC, hzt⟩ :=
      xi1115_inverting_involutions_conj_by_centralizer
        C x2 s t rfl hx2C hx2ne hCcomm hCodd hss htt hsInvC htInvC
    let w : G := z * g
    have hwS : w * s * w⁻¹ = s := by
      dsimp [w]
      calc
        (z * g) * s * (z * g)⁻¹ = z * (g * s * g⁻¹) * z⁻¹ := by group
        _ = z * t * z⁻¹ := by rfl
        _ = s := hzt
    have hzcommx2 : z * x2 = x2 * z :=
      Subgroup.mem_centralizer_singleton_iff.mp (by simpa [C] using hzC)
    have hwX : w * x1 * w⁻¹ = x2 := by
      dsimp [w]
      calc
        (z * g) * x1 * (z * g)⁻¹ = z * (g * x1 * g⁻¹) * z⁻¹ := by group
        _ = z * x2 * z⁻¹ := by rw [hg]
        _ = x2 := by
          calc
            z * x2 * z⁻¹ = x2 * z * z⁻¹ := by rw [hzcommx2]
            _ = x2 := by simp
    have hwJ : w * j1G * w⁻¹ = j2G := by
      apply mul_left_cancel
      calc
        s * (w * j1G * w⁻¹) =
            (w * s * w⁻¹) * (w * j1G * w⁻¹) := by rw [hwS]
        _ = w * (s * j1G) * w⁻¹ := by group
        _ = w * x1 * w⁻¹ := by rfl
        _ = x2 := hwX
        _ = s * j2G := by rfl
    have hj1fixa : j1G • a = a := (j1 : MulAction.stabilizer G a).property
    have hj2fixwa : j2G • (w • a) = w • a := by
      calc
        j2G • (w • a) = (w * j1G * w⁻¹) • (w • a) := by rw [hwJ]
        _ = w • (j1G • a) := by simp only [mul_smul, inv_smul_smul]
        _ = w • a := by rw [hj1fixa]
    have hj2ne : j2 ≠ 1 := (orderOf_eq_prime_iff.mp hj2order).2
    have hwfixa : w • a = a :=
      (xi1115_frobeniusKernel_uniqueFixedPoint
        htwo a b hab F hFrob j2 hj2ne (w • a)).mp hj2fixwa
    have hwcommS : w * s = s * w := by
      have h := congrArg (fun q : G => q * w) hwS
      simpa [mul_assoc] using h
    let wCs : Subgroup.centralizer ({s} : Set G) :=
      ⟨w, Subgroup.mem_centralizer_singleton_iff.mpr hwcommS⟩
    obtain ⟨c, hsc, hscuniq⟩ :=
      xi1115_involution_uniqueFixedPoint
        hdegreeOdd hatMostTwoFixedPoints s hsorder
    have hca : c ≠ a := by
      intro hca
      apply hab
      have hsfixa : s • a = a := by simpa [hca] using hsc
      exact hsfixa.symm.trans hsa
    have hCsCardPunctured :
        Nat.card (Subgroup.centralizer ({s} : Set G)) =
          Fintype.card Omega - 1 := by
      rw [hCsCard]
      have hOmegaCard : 1 < Fintype.card Omega :=
        Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
      exact huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
        (Fintype.card Omega - 1) (by omega)
        htwo a b hab F hFrob
    obtain ⟨z0, hz0, hz0uniq⟩ :=
      xi1115_involution_centralizer_regular_on_punctured
        hatMostTwoFixedPoints s hsorder c hsc hscuniq hCsCardPunctured
        a hca.symm a hca.symm
    have hwCs : (wCs : G) • a = a := by simpa [wCs] using hwfixa
    have honeCs : ((1 : Subgroup.centralizer ({s} : Set G)) : G) • a = a := by
      simp
    have hwCsOne : wCs = 1 :=
      (hz0uniq wCs hwCs).trans (hz0uniq 1 honeCs).symm
    have hwOne : w = 1 := congrArg Subtype.val hwCsOne
    have hjG : j1G = j2G := by
      simpa [hwOne] using hwJ
    apply Subtype.ext
    apply Subtype.ext
    exact hjG
  · intro hj
    subst j2
    exact IsConj.refl _

private theorem xi1115_stronglyReal_classCode_injective
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hsorder : orderOf s = 2) (hsa : s • a = b)
    (hallInvolutionsConj : ∀ t : G, orderOf t = 2 → IsConj t s) :
    let J := {j : F // PFAppendixIII.IsInvolution j}
    let code : Option J → ConjClasses G
      | none => ConjClasses.mk s
      | some j => ConjClasses.mk
          (s * ((((j : J) : F) : MulAction.stabilizer G a) : G))
    Function.Injective code := by
  classical
  let J := {j : F // PFAppendixIII.IsInvolution j}
  let code : Option J → ConjClasses G
    | none => ConjClasses.mk s
    | some j => ConjClasses.mk
        (s * ((((j : J) : F) : MulAction.stabilizer G a) : G))
  change Function.Injective code
  have hss : s * s = 1 := by
    simpa [pow_two] using (show s ^ 2 = 1 by
      rw [← hsorder]
      exact pow_orderOf_eq_one s)
  have hsomeNotNone : ∀ j : J, code (some j) ≠ code none := by
    intro j hcode
    let jG : G := ((((j : J) : F) : MulAction.stabilizer G a) : G)
    let x : G := s * jG
    have hjorder : orderOf (j : F) = 2 :=
      orderOf_eq_prime j.property.sq_eq_one j.property.ne_one
    have hxsq : x ^ 2 ≠ 1 := by
      simpa [x, jG] using
        xi1115_swap_mul_kernelInvolution_sq_ne_one
          htwo a b hab F hFrob s hsa hss (j : F) hjorder
    have hjGInv : PFAppendixIII.IsInvolution jG := by
      refine ⟨?_, ?_⟩
      · intro hjone
        apply j.property.ne_one
        apply Subtype.ext
        apply Subtype.ext
        exact hjone
      · simpa [jG] using congrArg
          (fun z : F => (((z : F) : MulAction.stabilizer G a) : G))
          j.property.sq_eq_one
    have hsInv : PFAppendixIII.IsInvolution s :=
      (orderOf_eq_prime_iff.mp hsorder).symm
    have hxStrong : PFAppendixIII.IsStronglyReal x :=
      ⟨s, jG, hsInv, hjGInv, rfl⟩
    have hxOdd : Odd (orderOf x) :=
      xi1115_stronglyReal_sq_ne_one_order_odd
        htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
        a b hab F hFrob hFSuzuki x hxStrong hxsq
    have hconj : IsConj x s := by
      exact ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [code, x, jG] using hcode)
    rw [isConj_iff] at hconj
    rcases hconj with ⟨g, hg⟩
    have hxorder : orderOf x = 2 := by
      calc
        orderOf x = orderOf s := by
          simpa [hg] using ((MulAut.conj g).orderOf_eq x).symm
        _ = 2 := hsorder
    exact hxOdd.not_two_dvd_nat (by rw [hxorder])
  intro x y hxy
  cases x with
  | none =>
      cases y with
      | none => rfl
      | some j => exact False.elim (hsomeNotNone j hxy.symm)
  | some i =>
      cases y with
      | none => exact False.elim (hsomeNotNone i hxy)
      | some j =>
          have hconj : IsConj
              (s * ((((i : J) : F) : MulAction.stabilizer G a) : G))
              (s * ((((j : J) : F) : MulAction.stabilizer G a) : G)) :=
            ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [code] using hxy)
          have hij : (i : F) = (j : F) :=
            (xi1115_swap_mul_kernelInvolution_isConj_iff
              htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
              a b hab F hFrob hF2 hFSuzuki s hsorder hsa
              hallInvolutionsConj (i : F) (j : F)
              (orderOf_eq_prime i.property.sq_eq_one i.property.ne_one)
              (orderOf_eq_prime j.property.sq_eq_one j.property.ne_one)).mp hconj
          exact congrArg some (Subtype.ext hij)

private theorem xi1115_stronglyReal_class_mem_codeRange
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hsorder : orderOf s = 2) (hsa : s • a = b)
    (hallInvolutionsConj : ∀ t : G, orderOf t = 2 → IsConj t s)
    (x : G) (hxStrong : PFAppendixIII.IsStronglyReal x) (hxne : x ≠ 1) :
    let J := {j : F // PFAppendixIII.IsInvolution j}
    let code : Option J → ConjClasses G
      | none => ConjClasses.mk s
      | some j => ConjClasses.mk
          (s * ((((j : J) : F) : MulAction.stabilizer G a) : G))
    ∃ o, ConjClasses.mk x = code o := by
  classical
  let J := {j : F // PFAppendixIII.IsInvolution j}
  let code : Option J → ConjClasses G
    | none => ConjClasses.mk s
    | some j => ConjClasses.mk
        (s * ((((j : J) : F) : MulAction.stabilizer G a) : G))
  change ∃ o, ConjClasses.mk x = code o
  by_cases hxsq : x ^ 2 = 1
  · have hxorder : orderOf x = 2 := orderOf_eq_prime hxsq hxne
    refine ⟨none, ?_⟩
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr
      (hallInvolutionsConj x hxorder)
  · obtain ⟨j, hjorder, hxj⟩ :=
      xi1115_stronglyReal_isConj_swap_mul_kernelInvolution
        htwo hdegreeOdd hatMostTwoFixedPoints a b hab F hFrob
        hF2 hFSuzuki s hsorder hsa hallInvolutionsConj x hxStrong hxsq
    let jJ : J :=
      ⟨j, (orderOf_eq_prime_iff.mp hjorder).symm⟩
    refine ⟨some jJ, ?_⟩
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (by simpa [code, jJ] using hxj)

private theorem xi1115_centralizer_conj_eq
    {G : Type*} [Group G] (x g : G) :
    Subgroup.centralizer ({g * x * g⁻¹} : Set G) =
      (Subgroup.centralizer ({x} : Set G)).map
        (MulAut.conj g).toMonoidHom := by
  apply le_antisymm
  · intro y hy
    let z : G := g⁻¹ * y * g
    have hycomm : y * (g * x * g⁻¹) = (g * x * g⁻¹) * y :=
      Subgroup.mem_centralizer_singleton_iff.mp hy
    have hzcomm : z * x = x * z := by
      dsimp [z]
      calc
        (g⁻¹ * y * g) * x = g⁻¹ * (y * (g * x * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * x * g⁻¹) * y) * g := by rw [hycomm]
        _ = x * (g⁻¹ * y * g) := by group
    refine ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr hzcomm, ?_⟩
    dsimp [z]
    group
  · rintro y ⟨z, hz, rfl⟩
    have hzcomm : z * x = x * z :=
      Subgroup.mem_centralizer_singleton_iff.mp hz
    apply Subgroup.mem_centralizer_singleton_iff.mpr
    change (g * z * g⁻¹) * (g * x * g⁻¹) =
      (g * x * g⁻¹) * (g * z * g⁻¹)
    calc
      (g * z * g⁻¹) * (g * x * g⁻¹) = g * (z * x) * g⁻¹ := by group
      _ = g * (x * z) * g⁻¹ := by rw [hzcomm]
      _ = (g * x * g⁻¹) * (g * z * g⁻¹) := by group

private theorem xi1115_centralizer_TI_core
    {G : Type*} [Group G] [Finite G]
    (x : G)
    (hcentralizerEq :
      ∀ z : G, z ∈ Subgroup.centralizer ({x} : Set G) → z ≠ 1 →
        Subgroup.centralizer ({z} : Set G) =
          Subgroup.centralizer ({x} : Set G))
    (g : G)
    (hg : g ∉ Subgroup.normalizer
      (Subgroup.centralizer ({x} : Set G) : Set G)) :
    Subgroup.centralizer ({x} : Set G) ⊓
        (Subgroup.centralizer ({x} : Set G)).map
          (MulAut.conj g).toMonoidHom = ⊥ := by
  let A := Subgroup.centralizer ({x} : Set G)
  let Ag := A.map (MulAut.conj g).toMonoidHom
  rw [eq_bot_iff]
  intro y hy
  by_contra hyne
  have hyA : y ∈ A := hy.1
  have hyAg : y ∈ Ag := hy.2
  rcases hyAg with ⟨z, hzA, hzy⟩
  have hzNe : z ≠ 1 := by
    intro hz
    subst z
    apply hyne
    simpa using hzy.symm
  have hCyA : Subgroup.centralizer ({y} : Set G) = A := by
    simpa [A] using hcentralizerEq y (by simpa [A] using hyA) hyne
  have hCzA : Subgroup.centralizer ({z} : Set G) = A := by
    simpa [A] using hcentralizerEq z (by simpa [A] using hzA) hzNe
  have hCyAg : Subgroup.centralizer ({y} : Set G) = Ag := by
    calc
      Subgroup.centralizer ({y} : Set G) =
          Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
        have hyEq : y = g * z * g⁻¹ := by simpa using hzy.symm
        rw [hyEq]
      _ = (Subgroup.centralizer ({z} : Set G)).map
          (MulAut.conj g).toMonoidHom := xi1115_centralizer_conj_eq z g
      _ = Ag := by rw [hCzA]
  have hAeqAg : A = Ag := hCyA.symm.trans hCyAg
  apply hg
  rw [Subgroup.mem_normalizer_iff]
  intro z
  constructor
  · intro hz
    have hzAg : g * z * g⁻¹ ∈ Ag := by
      exact ⟨z, hz, rfl⟩
    change g * z * g⁻¹ ∈ A
    rw [hAeqAg]
    exact hzAg
  · intro hzg
    change g * z * g⁻¹ ∈ A at hzg
    have hzgAg : g * z * g⁻¹ ∈ Ag := by
      rw [← hAeqAg]
      exact hzg
    rcases hzgAg with ⟨w, hwA, hwz⟩
    have hwz' : (MulAut.conj g) w = (MulAut.conj g) z := by
      simpa using hwz
    have hwEq : w = z := (MulAut.conj g).injective hwz'
    simpa [← hwEq] using hwA

set_option maxHeartbeats 800000 in
private theorem xi1115_centralizer_card_coprime_index_core
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G)
    (hcentralizer :
      ∀ a : G, a ∈ A → a ≠ 1 →
        Subgroup.centralizer ({a} : Set G) = A) :
    Nat.Coprime (Nat.card A) A.index := by
  classical
  by_contra hcop
  rw [Nat.Prime.not_coprime_iff_dvd] at hcop
  rcases hcop with ⟨p, hp, hpCard, hpIndex⟩
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p A := Classical.choice inferInstance
  obtain ⟨Q, hQcomap⟩ := P.exists_comap_subtype_eq
  let Pmap : Subgroup G := (P : Subgroup A).map A.subtype
  have hPmap_le_Q : Pmap ≤ (Q : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap, hQcomap]
  have hPmap_le_A : Pmap ≤ A := by
    rintro _ ⟨x, _hxP, rfl⟩
    exact x.property
  have hQnot_le_A : ¬ (Q : Subgroup G) ≤ A := by
    intro hQA
    have hindexDvd : A.index ∣ (Q : Subgroup G).index :=
      Subgroup.index_dvd_of_le hQA
    exact Q.not_dvd_index (hpIndex.trans hindexDvd)
  have hPmap_lt_Q : Pmap < (Q : Subgroup G) := by
    refine lt_of_le_of_ne hPmap_le_Q ?_
    intro hEq
    apply hQnot_le_A
    rw [← hEq]
    exact hPmap_le_A
  let K : Subgroup Q := Pmap.subgroupOf Q
  have hKlt : K < ⊤ := by
    rw [lt_top_iff_ne_top, ne_eq, Subgroup.subgroupOf_eq_top]
    exact not_le_of_gt hPmap_lt_Q
  letI : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  have hnormalizer : K < Subgroup.normalizer (K : Set Q) :=
    Group.normalizerCondition_of_isNilpotent K hKlt
  obtain ⟨b, hbNormalizer, hbNotK⟩ := SetLike.exists_of_lt hnormalizer
  have hPne : (P : Subgroup A) ≠ ⊥ :=
    P.ne_bot_of_dvd_card hpCard
  have hPmap_ne : Pmap ≠ ⊥ := by
    intro hPmap
    apply hPne
    apply (Subgroup.map_eq_bot_iff_of_injective
      (H := (P : Subgroup A)) (f := A.subtype) Subtype.coe_injective).mp
    simpa [Pmap] using hPmap
  have hKne : K ≠ ⊥ := by
    intro hK
    apply hPmap_ne
    calc
      Pmap = (Pmap.subgroupOf (Q : Subgroup G)).map
          (Q : Subgroup G).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPmap_le_Q).symm
      _ = K.map (Q : Subgroup G).subtype := by rfl
      _ = ⊥ := by rw [hK]; simp
  let N : Subgroup Q := Subgroup.normalizer (K : Set Q)
  let KN : Subgroup N := K.subgroupOf N
  letI : KN.Normal := by
    simpa [KN, N] using hkt_subgroupOf_normalizer_normal K
  have hKNne : KN ≠ ⊥ := by
    intro hKN
    apply hKne
    calc
      K = KN.map N.subtype := by
        simpa [KN, N] using
          (Subgroup.map_subgroupOf_eq_of_le
            (Subgroup.le_normalizer (H := K))).symm
      _ = ⊥ := by rw [hKN]; simp
  letI : Fact (IsPGroup p N) :=
    ⟨Q.isPGroup'.to_subgroup N⟩
  obtain ⟨z, hzKN, hzCenter, hzNe, _hzPow⟩ :=
    exists_nontrivial_mem_center_of_normal_p_subgroup
      (G := N) (p := p) KN hKNne
  let bN : N := ⟨b, hbNormalizer⟩
  let zG : G := (((z : N) : Q) : G)
  let bG : G := ((b : Q) : G)
  have hzPmap : zG ∈ Pmap := by
    have hzK : (z : Q) ∈ K := Subgroup.mem_subgroupOf.mp hzKN
    have hzPmap' : ((z : Q) : G) ∈ Pmap := Subgroup.mem_subgroupOf.mp hzK
    simpa [zG] using hzPmap'
  have hzA : zG ∈ A := hPmap_le_A hzPmap
  have hzGne : zG ≠ 1 := by
    intro hzG
    apply hzNe
    apply Subtype.ext
    apply Subtype.ext
    exact hzG
  have hbComm : bG * zG = zG * bG := by
    have hzCommN : bN * z = z * bN :=
      Subgroup.mem_center_iff.mp hzCenter bN
    simpa [bG, zG, bN] using congrArg
      (fun x : N => (((x : N) : Q) : G)) hzCommN
  have hbCentralizer :
      bG ∈ Subgroup.centralizer ({zG} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hbComm
  have hbA : bG ∈ A := by
    rw [← hcentralizer zG hzA hzGne]
    exact hbCentralizer
  let bA : A := ⟨bG, hbA⟩
  have hbP : bA ∈ (P : Subgroup A) := by
    rw [← hQcomap]
    exact b.property
  apply hbNotK
  change bG ∈ Pmap
  exact ⟨bA, hbP, rfl⟩

private theorem xi1115_stronglyReal_centralizer_card_coprime_index
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega] [FaithfulSMul G Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hnoRegularNormal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G) (hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s)
    (x : G) (hxStrong : PFAppendixIII.IsStronglyReal x)
    (hxsq : x ^ 2 ≠ 1) :
    Nat.Coprime
      (Nat.card (Subgroup.centralizer ({x} : Set G)))
      (Subgroup.centralizer ({x} : Set G)).index := by
  apply xi1115_centralizer_card_coprime_index_core
  intro z hz hzNe
  exact (xi1115_stronglyReal_centralizer_nontrivial
    htwo hdegreeOdd hatMostTwoFixedPoints hnoRegularNormal
    a b hab F hFrob hF2 hFSuzuki s hallInvolutionsConj
    x hxStrong hxsq z hz hzNe).2

private def xi1115_rankOneSet
    {G : Type*} [Group G] (B I : Subgroup G) (s : G) : Set G :=
  {x : G | x ∈ B ∨ ∃ b ∈ B, ∃ i ∈ I, x = b * s * i}

private theorem xi1115_rankOneSet_right_stable
    {G : Type*} [Group G] (B I H : Subgroup G) (s : G)
    (hHB : H ≤ B)
    (hdecomp :
      ∀ b : G, b ∈ B →
        ∃ i : G, i ∈ I ∧ ∃ h : G, h ∈ H ∧ b = i * h)
    (hInormal :
      ∀ h : G, h ∈ H →
        ∀ i : G, i ∈ I → h⁻¹ * i * h ∈ I)
    (hss : s * s = 1)
    (hHs : ∀ h : G, h ∈ H → s * h * s ∈ H) :
    ∀ x : G, x ∈ xi1115_rankOneSet B I s →
      ∀ b : G, b ∈ B →
        x * b ∈ xi1115_rankOneSet B I s := by
  intro x hx b hb
  change x ∈ B ∨ ∃ c ∈ B, ∃ i ∈ I, x = c * s * i at hx
  rcases hx with hxB | ⟨c, hcB, ix, hixI, rfl⟩
  · change x * b ∈ B ∨
      ∃ c ∈ B, ∃ i ∈ I, x * b = c * s * i
    exact Or.inl (B.mul_mem hxB hb)
  · rcases hdecomp b hb with ⟨ib, hibI, h, hhH, rfl⟩
    let k : G := h⁻¹ * (ix * ib) * h
    have hkI : k ∈ I := by
      exact hInormal h hhH (ix * ib) (I.mul_mem hixI hibI)
    have hshH : s * h * s ∈ H := hHs h hhH
    have hsInv : s⁻¹ = s :=
      inv_eq_of_mul_eq_one_right hss
    change (c * s * ix) * (ib * h) ∈ B ∨
      ∃ c' ∈ B, ∃ i ∈ I,
        (c * s * ix) * (ib * h) = c' * s * i
    refine Or.inr
      ⟨c * (s * h * s), B.mul_mem hcB (hHB hshH), k, hkI, ?_⟩
    calc
      (c * s * ix) * (ib * h) = c * s * h * k := by
        dsimp [k]
        group
      _ = (c * (s * h * s⁻¹)) * s * k := by group
      _ = (c * (s * h * s)) * s * k := by rw [hsInv]

private theorem xi1115_rankOneSet_weyl_of_regular_conjugates
    {G : Type*} [Group G] (B I H : Subgroup G) (s j : G)
    (hIB : I ≤ B) (hHB : H ≤ B)
    (hIconj :
      ∀ h : G, h ∈ H →
        ∀ i : G, i ∈ I → h * i * h⁻¹ ∈ I)
    (hss : s * s = 1)
    (hInverts :
      ∀ h : G, h ∈ H → s * h * s = h⁻¹)
    (hjI : j ∈ I)
    (hself : s * j * s = j * s * j)
    (horbit :
      ∀ y : G, y ∈ I → y ≠ 1 →
        ∃ h : G, h ∈ H ∧ y = h⁻¹ * j * h) :
    ∀ y : G, y ∈ I →
      s * y * s ∈ xi1115_rankOneSet B I s := by
  intro y hyI
  by_cases hyOne : y = 1
  · subst y
    change s * 1 * s ∈ B ∨
      ∃ b ∈ B, ∃ i ∈ I, s * 1 * s = b * s * i
    left
    simp [hss]
  · rcases horbit y hyI hyOne with ⟨h, hhH, hy⟩
    have hsh : s * h * s = h⁻¹ := hInverts h hhH
    have hsinvMove : s * h⁻¹ = h * s := by
      calc
        s * h⁻¹ = s * (s * h * s) := by rw [hsh]
        _ = (s * s) * h * s := by group
        _ = h * s := by rw [hss, one_mul]
    have hsMove : h * s = s * h⁻¹ := by
      calc
        h * s = (s * s) * h * s := by rw [hss, one_mul]
        _ = s * (s * h * s) := by group
        _ = s * h⁻¹ := by rw [hsh]
    have hshMiddle : h * s * h = s := by
      rw [hsMove]
      simp
    let i : G := h * j * h⁻¹
    have hiI : i ∈ I := hIconj h hhH j hjI
    have hbB : h * j * h ∈ B :=
      B.mul_mem (B.mul_mem (hHB hhH) (hIB hjI)) (hHB hhH)
    change s * y * s ∈ B ∨
      ∃ b ∈ B, ∃ i ∈ I, s * y * s = b * s * i
    refine Or.inr ⟨h * j * h, hbB, i, hiI, ?_⟩
    rw [hy]
    calc
      s * (h⁻¹ * j * h) * s =
          (s * h⁻¹) * j * (h * s) := by group
      _ = (h * s) * j * (s * h⁻¹) := by
        rw [hsinvMove, hsMove]
      _ = h * (s * j * s) * h⁻¹ := by group
      _ = h * (j * s * j) * h⁻¹ := by rw [hself]
      _ = h * j * (h * s * h) * j * h⁻¹ := by
        rw [hshMiddle]
        group
      _ = (h * j * h) * s * i := by
        dsimp [i]
        group

private theorem xi1115_rankOneSet_isSubgroup
    {G : Type*} [Group G] (B I : Subgroup G) (s : G)
    (hIB : I ≤ B) (hss : s * s = 1)
    (hright :
      ∀ x : G, x ∈ xi1115_rankOneSet B I s →
        ∀ b : G, b ∈ B →
          x * b ∈ xi1115_rankOneSet B I s)
    (hweyl :
      ∀ i : G, i ∈ I →
        s * i * s ∈ xi1115_rankOneSet B I s) :
    ∃ M : Subgroup G, (M : Set G) = xi1115_rankOneSet B I s := by
  have hleft :
      ∀ b : G, b ∈ B →
        ∀ x : G, x ∈ xi1115_rankOneSet B I s →
          b * x ∈ xi1115_rankOneSet B I s := by
    intro b hb x hx
    change x ∈ B ∨ ∃ c ∈ B, ∃ i ∈ I, x = c * s * i at hx
    change b * x ∈ B ∨
      ∃ c ∈ B, ∃ i ∈ I, b * x = c * s * i
    rcases hx with hxB | ⟨c, hcB, i, hiI, rfl⟩
    · exact Or.inl (B.mul_mem hb hxB)
    · exact Or.inr
        ⟨b * c, B.mul_mem hb hcB, i, hiI, by group⟩
  let M : Subgroup G :=
    { carrier := xi1115_rankOneSet B I s
      one_mem' := by
        change (1 : G) ∈ B ∨
          ∃ b ∈ B, ∃ i ∈ I, (1 : G) = b * s * i
        exact Or.inl B.one_mem
      mul_mem' := by
        intro x y hx hy
        have hyRank : y ∈ xi1115_rankOneSet B I s := hy
        change x ∈ B ∨ ∃ b ∈ B, ∃ i ∈ I, x = b * s * i at hx
        rcases hx with hxB | ⟨bx, hbxB, ix, hixI, rfl⟩
        · exact hleft x hxB y hyRank
        · have hxRank :
              bx * s * ix ∈ xi1115_rankOneSet B I s := by
            change bx * s * ix ∈ B ∨
              ∃ b ∈ B, ∃ i ∈ I, bx * s * ix = b * s * i
            exact Or.inr ⟨bx, hbxB, ix, hixI, rfl⟩
          change y ∈ B ∨
            ∃ b ∈ B, ∃ i ∈ I, y = b * s * i at hy
          rcases hy with hyB | ⟨byElem, hbyB, iy, hiyI, rfl⟩
          · exact hright (bx * s * ix) hxRank y hyB
          · have hprefix :=
              hright (bx * s * ix) hxRank byElem hbyB
            change (bx * s * ix) * byElem ∈ B ∨
              ∃ b ∈ B, ∃ i ∈ I,
                (bx * s * ix) * byElem = b * s * i at hprefix
            rcases hprefix with hprefixB |
                ⟨bp, hbpB, ip, hipI, hprefixEq⟩
            · change (bx * s * ix) * (byElem * s * iy) ∈ B ∨
                ∃ b ∈ B, ∃ i ∈ I,
                  (bx * s * ix) * (byElem * s * iy) = b * s * i
              exact Or.inr
                ⟨(bx * s * ix) * byElem, hprefixB, iy, hiyI, by group⟩
            · have hweylMem :=
                hweyl ip hipI
              have hleftMem :=
                hleft bp hbpB (s * ip * s) hweylMem
              have hrightMem :=
                hright (bp * (s * ip * s)) hleftMem iy (hIB hiyI)
              have heq :
                  (bx * s * ix) * (byElem * s * iy) =
                    (bp * (s * ip * s)) * iy := by
                calc
                  (bx * s * ix) * (byElem * s * iy) =
                      ((bx * s * ix) * byElem) * s * iy := by group
                  _ = (bp * s * ip) * s * iy := by rw [hprefixEq]
                  _ = (bp * (s * ip * s)) * iy := by group
              rw [heq]
              exact hrightMem
      inv_mem' := by
        intro x hx
        change x ∈ B ∨ ∃ b ∈ B, ∃ i ∈ I, x = b * s * i at hx
        rcases hx with hxB | ⟨b, hbB, i, hiI, rfl⟩
        · change x⁻¹ ∈ B ∨
            ∃ b ∈ B, ∃ i ∈ I, x⁻¹ = b * s * i
          exact Or.inl (B.inv_mem hxB)
        · have hsInv : s⁻¹ = s :=
            inv_eq_of_mul_eq_one_right hss
          have hsMem : s ∈ xi1115_rankOneSet B I s := by
            change s ∈ B ∨ ∃ b ∈ B, ∃ i ∈ I, s = b * s * i
            exact Or.inr ⟨1, B.one_mem, 1, I.one_mem, by simp⟩
          have hleftMem :=
            hleft i⁻¹ (hIB (I.inv_mem hiI)) s hsMem
          have hrightMem :=
            hright (i⁻¹ * s) hleftMem b⁻¹ (B.inv_mem hbB)
          have heq : (b * s * i)⁻¹ = (i⁻¹ * s) * b⁻¹ := by
            rw [mul_inv_rev, mul_inv_rev, hsInv]
            group
          rw [heq]
          exact hrightMem }
  exact ⟨M, rfl⟩

private theorem xi1115_rankOneSet_card
    {G : Type*} [Group G] [Finite G]
    (B I M : Subgroup G) (s : G)
    (hM : (M : Set G) = xi1115_rankOneSet B I s)
    (hdisjoint :
      ∀ b : G, b ∈ B →
        ∀ b' : G, b' ∈ B →
          ∀ i : G, i ∈ I → b ≠ b' * s * i)
    (hinjective :
      Function.Injective
        (fun p : B × I => ((p.1 : G) * s * (p.2 : G)))) :
    Nat.card M = Nat.card B + Nat.card B * Nat.card I := by
  classical
  let e : B ⊕ (B × I) → M
    | Sum.inl b => ⟨b, by
        change (b : G) ∈ (M : Set G)
        rw [hM]
        exact Or.inl b.property⟩
    | Sum.inr p => ⟨(p.1 : G) * s * (p.2 : G), by
        change (p.1 : G) * s * (p.2 : G) ∈ (M : Set G)
        rw [hM]
        exact Or.inr ⟨p.1, p.1.property, p.2, p.2.property, rfl⟩⟩
  have heInjective : Function.Injective e := by
    intro x y hxy
    rcases x with bx | px
    · rcases y with bz | py
      · apply congrArg Sum.inl
        apply Subtype.ext
        exact congrArg (fun z : M => (z : G)) hxy
      · exfalso
        exact hdisjoint bx bx.property py.1 py.1.property py.2 py.2.property
          (congrArg (fun z : M => (z : G)) hxy)
    · rcases y with bz | py
      · exfalso
        exact hdisjoint bz bz.property px.1 px.1.property px.2 px.2.property
          (congrArg (fun z : M => (z : G)) hxy).symm
      · apply congrArg Sum.inr
        exact hinjective (congrArg (fun z : M => (z : G)) hxy)
  have heSurjective : Function.Surjective e := by
    intro x
    have hxM : (x : G) ∈ (M : Set G) := x.property
    rw [hM] at hxM
    rcases hxM with hxB | ⟨b, hb, i, hi, hxi⟩
    · exact ⟨Sum.inl ⟨x, hxB⟩, Subtype.ext rfl⟩
    · exact ⟨Sum.inr (⟨b, hb⟩, ⟨i, hi⟩), Subtype.ext hxi.symm⟩
  calc
    Nat.card M = Nat.card (B ⊕ (B × I)) :=
      (Nat.card_congr
        (Equiv.ofBijective e ⟨heInjective, heSurjective⟩)).symm
    _ = Nat.card B + Nat.card (B × I) := Nat.card_sum
    _ = Nat.card B + Nat.card B * Nat.card I := by rw [Nat.card_prod]
private theorem xi1115_rankOneSet_card_of_conj_intersection
    {G : Type*} [Group G] [Finite G]
    (B I M : Subgroup G) (s : G)
    (hM : (M : Set G) = xi1115_rankOneSet B I s)
    (hIB : I ≤ B) (hsnot : s ∉ B)
    (hinter :
      ∀ x : G, x ∈ B → s⁻¹ * x * s ∈ I → x = 1) :
    Nat.card M = Nat.card B + Nat.card B * Nat.card I := by
  have hdisjoint :
      ∀ b : G, b ∈ B →
        ∀ b' : G, b' ∈ B →
          ∀ i : G, i ∈ I → b ≠ b' * s * i := by
    intro b hb b' hb' i hi heq
    apply hsnot
    have hsEq : s = b'⁻¹ * b * i⁻¹ := by
      rw [heq]
      group
    rw [hsEq]
    exact B.mul_mem (B.mul_mem (B.inv_mem hb') hb)
      (hIB (I.inv_mem hi))
  have hinjective :
      Function.Injective
        (fun p : B × I => ((p.1 : G) * s * (p.2 : G))) := by
    intro p q hpq
    change (p.1 : G) * s * (p.2 : G) =
      (q.1 : G) * s * (q.2 : G) at hpq
    have hxB : (q.1 : G)⁻¹ * (p.1 : G) ∈ B :=
      B.mul_mem (B.inv_mem q.1.property) p.1.property
    have hxconjI :
        s⁻¹ * ((q.1 : G)⁻¹ * (p.1 : G)) * s ∈ I := by
      have heq :
          s⁻¹ * ((q.1 : G)⁻¹ * (p.1 : G)) * s =
            (q.2 : G) * (p.2 : G)⁻¹ := by
        calc
          s⁻¹ * ((q.1 : G)⁻¹ * (p.1 : G)) * s =
              s⁻¹ * (q.1 : G)⁻¹ *
                (((p.1 : G) * s * (p.2 : G)) * (p.2 : G)⁻¹) := by
                  group
          _ = s⁻¹ * (q.1 : G)⁻¹ *
                (((q.1 : G) * s * (q.2 : G)) * (p.2 : G)⁻¹) := by
                  rw [hpq]
          _ = (q.2 : G) * (p.2 : G)⁻¹ := by group
      rw [heq]
      exact I.mul_mem q.2.property (I.inv_mem p.2.property)
    have hxOne :
        (q.1 : G)⁻¹ * (p.1 : G) = 1 :=
      hinter _ hxB hxconjI
    have hfirst : p.1 = q.1 := by
      apply Subtype.ext
      calc
        (p.1 : G) =
            (q.1 : G) * ((q.1 : G)⁻¹ * (p.1 : G)) := by group
        _ = (q.1 : G) := by rw [hxOne]; simp
    have hsecond : p.2 = q.2 := by
      apply Subtype.ext
      rw [hfirst] at hpq
      calc
        (p.2 : G) =
            (((q.1 : G) * s)⁻¹ * ((q.1 : G) * s)) * (p.2 : G) := by
              simp
        _ = ((q.1 : G) * s)⁻¹ *
              (((q.1 : G) * s) * (p.2 : G)) := by group
        _ = ((q.1 : G) * s)⁻¹ *
              (((q.1 : G) * s) * (q.2 : G)) := by
                rw [hpq]
        _ = (q.2 : G) := by group
    exact Prod.ext hfirst hsecond
  exact
    xi1115_rankOneSet_card B I M s hM hdisjoint hinjective
open scoped Pointwise in
private theorem xi1115_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (F H : Subgroup G)
    (hnormal : H ≤ Subgroup.normalizer F)
    (hdisjoint : Disjoint F H) :
    Nat.card (F ⊔ H : Subgroup G) = Nat.card F * Nat.card H := by
  let toB : F × H → ↥(F ⊔ H) := fun z =>
    ⟨(z.1 : G) * (z.2 : G),
      Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have htoB_injective : Function.Injective toB := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisjoint
    exact congrArg Subtype.val hxy
  have htoB_surjective : Function.Surjective toB := by
    intro b
    have hb : (b : G) ∈ (F : Set G) * (H : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left
        F H hnormal]
      exact b.property
    rcases hb with ⟨f, hf, h, hh, hfh⟩
    refine ⟨(⟨f, hf⟩, ⟨h, hh⟩), ?_⟩
    exact Subtype.ext hfh
  calc
    Nat.card (F ⊔ H : Subgroup G) = Nat.card (F × H) :=
      Nat.card_congr
        (Equiv.ofBijective toB
          ⟨htoB_injective, htoB_surjective⟩).symm
    _ = Nat.card F * Nat.card H := Nat.card_prod F H
private theorem xi1115_center_rankOneSubgroup_of_self
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (F D : Subgroup H)
    [MulDistribMulAction D F]
    (haction :
      ∀ d : D, ∀ x : F,
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (hregular : PFAppendixIII.ActionRegularOn D F
      (PFAppendixIII.involutions F))
    (s : G) (hss : s * s = 1)
    (hInvertsD :
      ∀ d : D,
        s * (((d : D) : H) : G) * s =
          (((d⁻¹ : D) : H) : G))
    (j : F) (hjorder : orderOf j = 2)
    (hself :
      s * (((j : F) : H) : G) * s =
        (((j : F) : H) : G) * s * (((j : F) : H) : G)⁻¹) :
    let phi : F →* G := H.subtype.comp F.subtype
    let I : Subgroup G := (Subgroup.center F).map phi
    let Hg : Subgroup G := D.map H.subtype
    let B : Subgroup G := I ⊔ Hg
    ∃ M : Subgroup G, (M : Set G) = xi1115_rankOneSet B I s := by
  classical
  let phi : F →* G := H.subtype.comp F.subtype
  let I : Subgroup G := (Subgroup.center F).map phi
  let Hg : Subgroup G := D.map H.subtype
  let B : Subgroup G := I ⊔ Hg
  change ∃ M : Subgroup G, (M : Set G) = xi1115_rankOneSet B I s
  have hIB : I ≤ B := le_sup_left
  have hHgB : Hg ≤ B := le_sup_right
  have hIconj :
      ∀ h : G, h ∈ Hg →
        ∀ i : G, i ∈ I → h * i * h⁻¹ ∈ I := by
    intro h hh i hi
    rcases hh with ⟨hH, hhD, rfl⟩
    rcases hi with ⟨x, hxZ, rfl⟩
    let d : D := ⟨hH, hhD⟩
    have hdxZ : d • x ∈ Subgroup.center F := by
      exact
        (MulEquivClass.apply_mem_center_iff
          (MulDistribMulAction.toMulAut D F d)).2 hxZ
    refine ⟨d • x, hdxZ, ?_⟩
    simpa [phi, d] using haction d x
  have hHgNorm : Hg ≤ Subgroup.normalizer I := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro i
    constructor
    · exact hIconj h hh i
    · intro hconj
      have hback := hIconj h⁻¹ (Hg.inv_mem hh)
        (h * i * h⁻¹) hconj
      have heq : h⁻¹ * (h * i * h⁻¹) * (h⁻¹)⁻¹ = i := by
        group
      rw [heq] at hback
      exact hback
  have hdecomp :
      ∀ b : G, b ∈ B →
        ∃ i : G, i ∈ I ∧ ∃ h : G, h ∈ Hg ∧ b = i * h := by
    intro b hb
    have hbProd :=
      (Set.ext_iff.mp
        (Subgroup.coe_mul_of_right_le_normalizer_left I Hg hHgNorm) b).mp
        (by simpa [B] using hb)
    rcases hbProd with ⟨i, hiI, h, hhHg, rfl⟩
    exact ⟨i, hiI, h, hhHg, rfl⟩
  have hInormal :
      ∀ h : G, h ∈ Hg →
        ∀ i : G, i ∈ I → h⁻¹ * i * h ∈ I := by
    intro h hh i hi
    simpa only [inv_inv] using hIconj h⁻¹ (Hg.inv_mem hh) i hi
  have hInverts :
      ∀ h : G, h ∈ Hg → s * h * s = h⁻¹ := by
    intro h hh
    rcases hh with ⟨hH, hhD, rfl⟩
    let d : D := ⟨hH, hhD⟩
    simpa [d] using hInvertsD d
  have hHs :
      ∀ h : G, h ∈ Hg → s * h * s ∈ Hg := by
    intro h hh
    rw [hInverts h hh]
    exact Hg.inv_mem hh
  have hinvolutions :=
    (Higman.theorem1_involutions_center hFSuzuki).1
  have hjInv : PFAppendixIII.IsInvolution j :=
    (orderOf_eq_prime_iff.mp hjorder).symm
  have hjcenter : j ∈ Subgroup.center F := by
    exact ((Set.ext_iff.mp hinvolutions j).mp hjInv).1
  have hjI : (((j : F) : H) : G) ∈ I := by
    exact ⟨j, hjcenter, rfl⟩
  have hjSq : j * j = 1 := by
    simpa [pow_two] using (show j ^ 2 = 1 by
      rw [← hjorder]
      exact pow_orderOf_eq_one j)
  have hjSqG :
      (((j : F) : H) : G) * (((j : F) : H) : G) = 1 := by
    simpa using congrArg
      (fun x : F => (((x : F) : H) : G)) hjSq
  have hjInvG : (((j : F) : H) : G)⁻¹ = (((j : F) : H) : G) :=
    inv_eq_of_mul_eq_one_right hjSqG
  have hself' :
      s * (((j : F) : H) : G) * s =
        (((j : F) : H) : G) * s * (((j : F) : H) : G) := by
    simpa [hjInvG] using hself
  have horbit :
      ∀ y : G, y ∈ I → y ≠ 1 →
        ∃ h : G, h ∈ Hg ∧
          y = h⁻¹ * (((j : F) : H) : G) * h := by
    intro y hyI hyne
    rcases hyI with ⟨x, hxcenter, hxy⟩
    have hxne : x ≠ 1 := by
      intro hx
      subst x
      apply hyne
      simpa [phi] using hxy.symm
    have hxInv : PFAppendixIII.IsInvolution x := by
      change x ∈ PFAppendixIII.involutions F
      rw [hinvolutions]
      exact ⟨hxcenter, hxne⟩
    rcases hregular.2 j hjInv x hxInv with ⟨d, hdx, _⟩
    let h : G := (((d⁻¹ : D) : H) : G)
    have hhHg : h ∈ Hg := by
      exact ⟨(d⁻¹ : D), (d⁻¹ : D).property, rfl⟩
    refine ⟨h, hhHg, ?_⟩
    have hphi :
        phi x = h⁻¹ * (((j : F) : H) : G) * h := by
      rw [hdx]
      calc
        phi (d • j) =
            (((d : D) : H) : G) * (((j : F) : H) : G) *
              (((d : D) : H) : G)⁻¹ := by
                simpa [phi] using haction d j
        _ = h⁻¹ * (((j : F) : H) : G) * h := by
          dsimp [h]
          group
    exact hxy.symm.trans hphi
  have hright :=
    xi1115_rankOneSet_right_stable B I Hg s hHgB
      hdecomp hInormal hss hHs
  have hweyl :=
    xi1115_rankOneSet_weyl_of_regular_conjugates
      B I Hg s (((j : F) : H) : G)
      hIB hHgB hIconj hss hInverts hjI hself' horbit
  exact xi1115_rankOneSet_isSubgroup B I s hIB hss hright hweyl
private theorem xi1115_center_rankOneSubgroup_of_self_explicit
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (F D : Subgroup H)
    [MulDistribMulAction D F]
    (haction :
      ∀ d : D, ∀ x : F,
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (hregular : PFAppendixIII.ActionRegularOn D F
      (PFAppendixIII.involutions F))
    (s : G) (hss : s * s = 1)
    (hInvertsD :
      ∀ d : D,
        s * (((d : D) : H) : G) * s =
          (((d⁻¹ : D) : H) : G))
    (j : F) (hjorder : orderOf j = 2)
    (hself :
      s * (((j : F) : H) : G) * s =
        (((j : F) : H) : G) * s * (((j : F) : H) : G)⁻¹) :
    ∃ M : Subgroup G,
      (M : Set G) = xi1115_rankOneSet
        ((Subgroup.center F).map (H.subtype.comp F.subtype) ⊔
          D.map H.subtype)
        ((Subgroup.center F).map (H.subtype.comp F.subtype)) s := by
  simpa only using
    xi1115_center_rankOneSubgroup_of_self
      H F D haction hFSuzuki hregular s hss hInvertsD j hjorder hself

private theorem xi1115_center_rankOneSubgroup_of_structure_eq_self
    {G : Type*} [Group G] [Finite G]
    (H : Subgroup G) (F D : Subgroup H)
    [MulDistribMulAction D F]
    (haction :
      ∀ d : D, ∀ x : F,
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (hregular : PFAppendixIII.ActionRegularOn D F
      (PFAppendixIII.involutions F))
    (s : G) (hss : s * s = 1)
    (hInvertsD :
      ∀ d : D,
        s * (((d : D) : H) : G) * s =
          (((d⁻¹ : D) : H) : G))
    (j g : F) (hjorder : orderOf j = 2) (hjg : j = g)
    (hstructure :
      s * (((j : F) : H) : G) * s =
        (((g : F) : H) : G) * s * (((g : F) : H) : G)⁻¹) :
    ∃ M : Subgroup G,
      (M : Set G) = xi1115_rankOneSet
        ((Subgroup.center F).map (H.subtype.comp F.subtype) ⊔
          D.map H.subtype)
        ((Subgroup.center F).map (H.subtype.comp F.subtype)) s := by
  subst g
  exact xi1115_center_rankOneSubgroup_of_self_explicit
    H F D haction hFSuzuki hregular
    s hss hInvertsD j hjorder hstructure

private theorem xi1115_braid_of_product_order_three
    {G : Type*} [Group G] (s i : G)
    (hss : s * s = 1) (hii : i * i = 1)
    (horder : orderOf (i * s) = 3) :
    s * i * s = i * s * i := by
  have hpow : (i * s) ^ 3 = 1 := by
    rw [← horder]
    exact pow_orderOf_eq_one (i * s)
  calc
    s * i * s = 1 * (s * i * s) := by simp
    _ = (i * s) ^ 3 * (s * i * s) := by rw [hpow]
    _ = i * s * i := by
      rw [pow_succ, pow_two]
      calc
        i * s * (i * s) * (i * s) * (s * i * s) =
            i * s * i * s * i * (s * s) * i * s := by group
        _ = i * s * i * s * i * i * s := by rw [hss]; simp
        _ = i * s * i * s * (i * i) * s := by group
        _ = i * s * i * (s * s) := by rw [hii]; simp [mul_assoc]
        _ = i * s * i := by rw [hss]; simp

private theorem xi1115_three_dvd_complement_structure_self
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hdegreeF : Fintype.card Omega = Nat.card F + 1)
    (s : G) (hsorder : orderOf s = 2)
    (hsa : s • a = b) (hsb : s • b = a)
    (hsInvertsD :
      ∀ x : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
          ((((x⁻¹ : MulAction.stabilizer
              (MulAction.stabilizer G a)
              (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) :
                MulAction.stabilizer G a) : G)))
    (hallInvolutionsConj : ∀ t : G, orderOf t = 2 → IsConj t s)
    (hthree : 3 ∣ Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))) :
    ∃ i : F, orderOf i = 2 ∧
      s * (((i : F) : MulAction.stabilizer G a) : G) * s =
        (((i : F) : MulAction.stabilizer G a) : G) * s *
          (((i : F) : MulAction.stabilizer G a) : G)⁻¹ := by
  classical
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  have hthreeD : 3 ∣ Nat.card D := by
    simpa [D, H, b'] using hthree
  obtain ⟨h, hhorder⟩ : ∃ h : D, orderOf h = 3 :=
    exists_prime_orderOf_dvd_card' (G := D) 3 hthreeD
  let hG : G := (((h : D) : H) : G)
  have hhfixa : hG • a = a := by
    exact ((h : H).property)
  have hhfixb : hG • b = b := by
    exact congrArg Subtype.val h.property
  have hhGorder : orderOf hG = 3 := by
    simpa [hG, D, H, b'] using hhorder
  have hhGne : hG ≠ 1 := (orderOf_eq_prime_iff.mp hhGorder).2
  have hssq : s * s = 1 := by
    simpa [pow_two] using (show s ^ 2 = 1 by
      rw [← hsorder]
      exact pow_orderOf_eq_one s)
  have hsinv : s⁻¹ = s :=
    inv_eq_of_mul_eq_one_right hssq
  have hinverts : s * hG * s⁻¹ = hG⁻¹ := by
    simpa [D, H, b', hG] using hsInvertsD h
  let t : G := s * hG
  have htsq : t * t = 1 := by
    dsimp [t]
    calc
      s * hG * (s * hG) = (s * hG * s⁻¹) * hG := by rw [hsinv]; group
      _ = hG⁻¹ * hG := by rw [hinverts]
      _ = 1 := by simp
  have hta : t • a = b := by
    dsimp [t]
    rw [mul_smul, hhfixa, hsa]
  have htne : t ≠ 1 := by
    intro ht
    apply hab
    calc
      a = (1 : G) • a := by simp
      _ = t • a := by rw [ht]
      _ = b := hta
  have htorder : orderOf t = 2 :=
    orderOf_eq_prime (by simpa [pow_two] using htsq) htne
  obtain ⟨c, hsc, hcuniq⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints s hsorder
  obtain ⟨d, htd, hduniq⟩ :=
    xi1115_involution_uniqueFixedPoint
      hdegreeOdd hatMostTwoFixedPoints t htorder
  have hca : c ≠ a := by
    intro h
    apply hab
    calc
      a = s • a := by rw [← h, hsc]
      _ = b := hsa
  have hcb : c ≠ b := by
    intro h
    apply hab
    calc
      a = s • b := hsb.symm
      _ = s • c := by rw [h]
      _ = c := hsc
      _ = b := h
  have hst : s * t = hG := by
    dsimp [t]
    calc
      s * (s * hG) = (s * s) * hG := by group
      _ = hG := by rw [hssq]; simp
  have hcd : c ≠ d := by
    intro h
    have hhc : hG • c = c := by
      calc
        hG • c = (s * t) • c := by rw [hst]
        _ = s • (t • c) := by rw [mul_smul]
        _ = s • c := by rw [h, htd]
        _ = c := hsc
    exact hatMostTwoFixedPoints hG hhGne a b c
      hab hca.symm hcb.symm ⟨hhfixa, hhfixb, hhc⟩
  have hconj : IsConj t s := hallInvolutionsConj t htorder
  rw [isConj_iff] at hconj
  rcases hconj with ⟨k, hk⟩
  have hkd : k • d = c := by
    apply hcuniq
    calc
      s • (k • d) = (k * t * k⁻¹) • (k • d) := by rw [hk]
      _ = k • (t • d) := by simp only [mul_smul, inv_smul_smul]
      _ = k • d := by rw [htd]
  have hkc_ne : k • c ≠ c := by
    intro hkc
    apply hcd
    apply smul_left_cancel k
    exact hkc.trans hkd.symm
  have hCcardF :
      Nat.card (Subgroup.centralizer ({s} : Set G)) = Nat.card F :=
    xi1115_involution_centralizer_card_eq_kernel
      htwo a b hab F hFrob hF2 s hallInvolutionsConj
  have hCcard :
      Nat.card (Subgroup.centralizer ({s} : Set G)) =
        Fintype.card Omega - 1 := by
    rw [hCcardF, hdegreeF]
    omega
  have hCregular :
      ∀ x : Omega, x ≠ c → ∀ y : Omega, y ≠ c →
        ∃! q : Subgroup.centralizer ({s} : Set G), (q : G) • x = y :=
    xi1115_involution_centralizer_regular_on_punctured
      hatMostTwoFixedPoints s hsorder c hsc hcuniq hCcard
  obtain ⟨q, hqkc, _hquniq⟩ :=
    hCregular (k • c) hkc_ne a hca.symm
  have hqcomm : (q : G) * s = s * (q : G) :=
    Subgroup.mem_centralizer_singleton_iff.mp q.property
  have hqc : (q : G) • c = c := by
    apply hcuniq
    calc
      s • ((q : G) • c) = (s * (q : G)) • c := by rw [mul_smul]
      _ = ((q : G) * s) • c := by rw [hqcomm]
      _ = (q : G) • (s • c) := by rw [mul_smul]
      _ = (q : G) • c := by rw [hsc]
  let r : G := (q : G) * k
  have hrt : r * t * r⁻¹ = s := by
    dsimp [r]
    calc
      (q : G) * k * t * ((q : G) * k)⁻¹ =
          (q : G) * (k * t * k⁻¹) * (q : G)⁻¹ := by group
      _ = (q : G) * s * (q : G)⁻¹ := by rw [hk]
      _ = s * (q : G) * (q : G)⁻¹ := by rw [hqcomm]
      _ = s := by simp
  have hrc : r • c = a := by
    dsimp [r]
    rw [mul_smul, hqkc]
  let iG : G := r * s * r⁻¹
  have hiGorder : orderOf iG = 2 := by
    exact ((MulAut.conj r).orderOf_eq s).trans hsorder
  have hrinca : r⁻¹ • a = c := by
    calc
      r⁻¹ • a = r⁻¹ • (r • c) := by rw [hrc]
      _ = c := inv_smul_smul r c
  have hiGfixa : iG • a = a := by
    dsimp [iG]
    calc
      (r * s * r⁻¹) • a = r • (s • (r⁻¹ • a)) := by simp only [mul_smul]
      _ = r • (s • c) := by rw [hrinca]
      _ = r • c := by rw [hsc]
      _ = a := hrc
  have hiGmem : (⟨iG, hiGfixa⟩ : H) ∈ F :=
    xi1115_involution_mem_frobeniusKernel_of_fixedPoint
      htwo hdegreeOdd hatMostTwoFixedPoints a b hab F hFrob
      iG hiGorder hiGfixa
  let i : F := ⟨⟨iG, hiGfixa⟩, hiGmem⟩
  have hiorder : orderOf i = 2 := by
    change orderOf (⟨⟨iG, hiGfixa⟩, hiGmem⟩ : F) = 2
    calc
      orderOf (⟨⟨iG, hiGfixa⟩, hiGmem⟩ : F) =
          orderOf (⟨iG, hiGfixa⟩ : H) := Subgroup.orderOf_mk _ _
      _ = orderOf iG := Subgroup.orderOf_mk _ _
      _ = 2 := hiGorder
  have hhConj : r * hG * r⁻¹ = iG * s := by
    rw [← hst]
    dsimp [iG]
    calc
      r * (s * t) * r⁻¹ =
          (r * s * r⁻¹) * (r * t * r⁻¹) := by group
      _ = (r * s * r⁻¹) * s := by rw [hrt]
  have hiSorder : orderOf (iG * s) = 3 := by
    rw [← hhConj]
    exact ((MulAut.conj r).orderOf_eq hG).trans hhGorder
  have hii : iG * iG = 1 := by
    simpa [pow_two] using (show iG ^ 2 = 1 by
      rw [← hiGorder]
      exact pow_orderOf_eq_one iG)
  have hbraid : s * iG * s = iG * s * iG :=
    xi1115_braid_of_product_order_three s iG hssq hii hiSorder
  refine ⟨i, hiorder, ?_⟩
  change s * iG * s = iG * s * iG⁻¹
  have hiinv : iG⁻¹ = iG :=
    inv_eq_of_mul_eq_one_right hii
  simpa [hiinv] using hbraid

private theorem xi1115_actor_card_eq_center_card_sub_one
    {D F : Type*} [Group D] [Group F] [MulDistribMulAction D F]
    (hF : PFAppendixIII.IsSuzukiTwoGroup F)
    (hregular : PFAppendixIII.ActionRegularOn D F
      (PFAppendixIII.involutions F)) :
    Nat.card D = Nat.card (Subgroup.center F) - 1 := by
  classical
  letI : Finite F := Higman.finite_of_isSuzukiTwoGroup hF
  have hinvolutions := (Higman.theorem1_involutions_center hF).1
  let involEquiv : {x : F // x ∈ PFAppendixIII.involutions F} ≃
      {z : Subgroup.center F // z ≠ 1} :=
    { toFun := fun x =>
        ⟨⟨x, (by
          have hx := (Set.ext_iff.mp hinvolutions (x : F)).mp x.property
          exact hx.1)⟩,
          fun hz => x.property.ne_one (congrArg Subtype.val hz)⟩
      invFun := fun z =>
        ⟨z, by
          rw [hinvolutions]
          exact ⟨z.1.property, fun hz => z.2 (Subtype.ext hz)⟩⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl }
  have hinvolutionCard :
      Nat.card {x : F // x ∈ PFAppendixIII.involutions F} =
        Nat.card (Subgroup.center F) - 1 := by
    calc
      Nat.card {x : F // x ∈ PFAppendixIII.involutions F} =
          Nat.card {z : Subgroup.center F // z ≠ 1} :=
        Nat.card_congr involEquiv
      _ = Nat.card (Subgroup.center F) - 1 := by
        letI : Fintype (Subgroup.center F) := Fintype.ofFinite _
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
        simp
  obtain ⟨x0, _y0, hx0, _hy0, _hxy0⟩ := hF.2.2.1
  let orbit : D → {x : F // x ∈ PFAppendixIII.involutions F} :=
    fun d => ⟨d • x0, hregular.1 x0 hx0 d⟩
  have horbitInjective : Function.Injective orbit := by
    intro d e hde
    have hsmul : d • x0 = e • x0 := congrArg Subtype.val hde
    rcases hregular.2 x0 hx0 (d • x0)
        (hregular.1 x0 hx0 d) with ⟨k, _hk, huniq⟩
    exact (huniq d rfl).trans (huniq e hsmul).symm
  have horbitSurjective : Function.Surjective orbit := by
    rintro ⟨y, hy⟩
    rcases hregular.2 x0 hx0 y hy with ⟨d, hd, _huniq⟩
    exact ⟨d, Subtype.ext hd.symm⟩
  calc
    Nat.card D =
        Nat.card {x : F // x ∈ PFAppendixIII.involutions F} :=
      Nat.card_congr (Equiv.ofBijective orbit
        ⟨horbitInjective, horbitSurjective⟩)
    _ = Nat.card (Subgroup.center F) - 1 := hinvolutionCard

private theorem xi1115_kernel_involution_card
    {F : Type*} [Group F] [Finite F]
    (hF : PFAppendixIII.IsSuzukiTwoGroup F) :
    Nat.card {x : F // PFAppendixIII.IsInvolution x} =
      Nat.card (Subgroup.center F) - 1 := by
  classical
  have hinvolutions := (Higman.theorem1_involutions_center hF).1
  let e : {x : F // PFAppendixIII.IsInvolution x} ≃
      {z : Subgroup.center F // z ≠ 1} :=
    { toFun := fun x =>
        ⟨⟨x, ((Set.ext_iff.mp hinvolutions (x : F)).mp x.property).1⟩,
          fun hz => x.property.ne_one (congrArg Subtype.val hz)⟩
      invFun := fun z =>
        ⟨z, by
          exact (Set.ext_iff.mp hinvolutions (z : F)).mpr
            ⟨z.1.property, fun hz => z.2 (Subtype.ext hz)⟩⟩
      left_inv := by intro x; apply Subtype.ext; rfl
      right_inv := by intro z; apply Subtype.ext; apply Subtype.ext; rfl }
  calc
    Nat.card {x : F // PFAppendixIII.IsInvolution x} =
        Nat.card {z : Subgroup.center F // z ≠ 1} := Nat.card_congr e
    _ = Nat.card (Subgroup.center F) - 1 := by
      letI : Fintype (Subgroup.center F) := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
      simp
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_kernel_suzukiActionData
    {G Omega : Type*} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFnoncomm : ¬ IsMulCommutative F)
    (hF2 : IsPGroup 2 F)
    (hDcyclic : IsCyclic
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (s : G) (hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s) :
    let D := MulAction.stabilizer (MulAction.stabilizer G a)
      (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
    letI : F.Normal := hFrob.normal
    letI : MulDistribMulAction D F :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer D F
        (Subgroup.le_normalizer_of_normal (H := F))
    PFAppendixIII.IsSuzukiTwoGroup F ∧
      FaithfulSMul D F ∧
      PFAppendixIII.ActionRegularOn D F (PFAppendixIII.involutions F) := by
  classical
  let H := MulAction.stabilizer G a
  let D := MulAction.stabilizer H
    (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)
  letI : F.Normal := hFrob.normal
  letI : MulDistribMulAction D F :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D F
      (Subgroup.le_normalizer_of_normal (H := F))
  obtain ⟨z, hzorder, _hzcenter, hzorbit⟩ :=
    xi1115_frobeniusKernel_involutions_D_orbit
      htwo a b hab F hFrob hF2 s hallInvolutionsConj
  have hzInv : PFAppendixIII.IsInvolution z := by
    exact (orderOf_eq_prime_iff.mp hzorder).symm
  have hzOrbit' : ∀ w : F, PFAppendixIII.IsInvolution w →
      ∃! d : D, w = d • z := by
    intro w hw
    have hworder : orderOf w = 2 := orderOf_eq_prime hw.2 hw.1
    rcases hzorbit w hworder with ⟨d, hd, hdu⟩
    refine ⟨d, ?_, ?_⟩
    · apply Subtype.ext
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using hd.symm
    · intro e he
      apply hdu e
      have he' := congrArg (fun q : F => (q : H)) he
      simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using he'.symm
  have hregular : PFAppendixIII.ActionRegularOn D F
      (PFAppendixIII.involutions F) := by
    constructor
    · intro x hx d
      change PFAppendixIII.IsInvolution x at hx
      change PFAppendixIII.IsInvolution (d • x)
      have hxorder : orderOf x = 2 := orderOf_eq_prime hx.2 hx.1
      have hdxorder : orderOf (d • x) = 2 := by
        simpa [MulDistribMulAction.toMulAut_apply] using
          ((MulEquiv.orderOf_eq (MulDistribMulAction.toMulAut D F d) x).trans hxorder)
      exact (orderOf_eq_prime_iff.mp hdxorder).symm
    · intro x hx y hy
      change PFAppendixIII.IsInvolution x at hx
      change PFAppendixIII.IsInvolution y at hy
      rcases hzOrbit' x hx with ⟨dx, hdx, hdxuniq⟩
      rcases hzOrbit' y hy with ⟨dy, hdy, hdyuniq⟩
      refine ⟨dy * dx⁻¹, ?_, ?_⟩
      · calc
          y = dy • z := hdy
          _ = dy • (dx⁻¹ • x) := by rw [hdx, inv_smul_smul]
          _ = (dy * dx⁻¹) • x := by rw [mul_smul]
      · intro k hk
        have hky : y = (k * dx) • z := by
          calc
            y = k • x := hk
            _ = k • (dx • z) := by rw [← hdx]
            _ = (k * dx) • z := by rw [mul_smul]
        have hkdx : k * dx = dy := hdyuniq (k * dx) hky
        calc
          k = (k * dx) * dx⁻¹ := by group
          _ = dy * dx⁻¹ := by rw [hkdx]
  have hfaithful : FaithfulSMul D F := faithfulSMul_iff.mpr (by
    intro d hd
    rcases hzOrbit' z hzInv with ⟨e, he, huniq⟩
    have hde : d = e := huniq d (hd z).symm
    have h1e : (1 : D) = e := huniq 1 (by simp)
    exact hde.trans h1e.symm)
  have hDne : D ≠ ⊥ := by
    simpa [D] using hFrob.complement_ne_bot
  letI : Nontrivial D := (Subgroup.nontrivial_iff_ne_bot D).mpr hDne
  obtain ⟨d, hd⟩ := exists_ne (1 : D)
  let w : F := d • z
  have hwInv : PFAppendixIII.IsInvolution w := by
    simpa [w, PFAppendixIII.involutions] using hregular.1 z hzInv d
  have hzw : z ≠ w := by
    intro h
    rcases hzOrbit' z hzInv with ⟨e, he, huniq⟩
    have hde : d = e := huniq d (by simpa [w] using h)
    have h1e : (1 : D) = e := huniq 1 (by simp)
    exact hd (hde.trans h1e.symm)
  obtain ⟨f, _hfpos, hFcard⟩ :=
    xi1115_kernel_card_twoPower F hFrob.kernel_ne_bot hF2
  have hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F := by
    refine ⟨?_, hFnoncomm, ?_, ?_⟩
    · exact ⟨f, by simpa using hFcard⟩
    · exact ⟨z, w, hzInv, hwInv, hzw⟩
    · refine ⟨D, inferInstance, inferInstance, ?_, hfaithful, hregular⟩
      simpa [D] using hDcyclic
  exact ⟨hFSuzuki, hfaithful, hregular⟩
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_frobenius_subgroupOf_sup
    {G : Type*} [Group G]
    (K R : Subgroup G)
    (hRnormalizesK : R ≤ Subgroup.normalizer K)
    (hdisjoint : Disjoint K R)
    (hKne : K ≠ ⊥) (hRne : R ≠ ⊥)
    (hTI :
      let S := K ⊔ R
      ∀ g : S, g ∉ R.subgroupOf S →
        Disjoint (R.subgroupOf S) ((R.subgroupOf S).conjBy g)) :
    let S := K ⊔ R
    IsFrobeniusGroupWithKernelComplement
      (K.subgroupOf S) (R.subgroupOf S) := by
  let S := K ⊔ R
  change IsFrobeniusGroupWithKernelComplement
    (K.subgroupOf S) (R.subgroupOf S)
  have hKnormal : (K.subgroupOf S).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact sup_le Subgroup.le_normalizer hRnormalizesK
  letI : (K.subgroupOf S).Normal := hKnormal
  have hKsub_ne : K.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hKne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    let xS : S := ⟨x, (show K ≤ S by exact le_sup_left) hx⟩
    have hxsub : xS ∈ K.subgroupOf S := hx
    rw [hbot] at hxsub
    simpa [xS] using congrArg Subtype.val (Subgroup.mem_bot.mp hxsub)
  have hRsub_ne : R.subgroupOf S ≠ ⊥ := by
    intro hbot
    apply hRne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    let xS : S := ⟨x, (show R ≤ S by exact le_sup_right) hx⟩
    have hxsub : xS ∈ R.subgroupOf S := hx
    rw [hbot] at hxsub
    simpa [xS] using congrArg Subtype.val (Subgroup.mem_bot.mp hxsub)
  have hdisjointSub :
      Disjoint (K.subgroupOf S) (R.subgroupOf S) := by
    rw [Subgroup.disjoint_def]
    intro x hxK hxR
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hdisjoint) hxK hxR
  have hsup :
      K.subgroupOf S ⊔ R.subgroupOf S = ⊤ := by
    calc
      K.subgroupOf S ⊔ R.subgroupOf S = (K ⊔ R).subgroupOf S := by
        symm
        simpa [S] using
          (Subgroup.subgroupOf_sup
            (A := K) (A' := R) (B := S) le_sup_left le_sup_right)
      _ = ⊤ := by
        apply (Subgroup.subgroupOf_eq_top).2
        simp [S]
  exact ⟨hKnormal,
    isComplement'_of_disjoint_sup_eq_top_of_normal
      (K.subgroupOf S) (R.subgroupOf S) hdisjointSub hsup,
    hTI, hKsub_ne, hRsub_ne⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_twoPointStabilizer_TI
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ x y z : Omega,
          x ≠ y → x ≠ z → y ≠ z →
            ¬ (g • x = x ∧ g • y = y ∧ g • z = z))
    (a b : Omega) (hab : a ≠ b) :
    let H := MulAction.stabilizer G a
    let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
    let D := MulAction.stabilizer H b'
    ∀ h : H, h ∉ D → Disjoint D (D.conjBy h) := by
  let H := MulAction.stabilizer G a
  let X := SubMulAction.ofStabilizer G a
  let b' : X := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change ∀ h : H, h ∉ D → Disjoint D (D.conjBy h)
  intro h hhD
  rw [Subgroup.disjoint_def]
  intro x hxD hxconj
  have hxb' : x • b' = b' := MulAction.mem_stabilizer_iff.mp hxD
  have hhc_ne : (h • b' : X) ≠ b' := by
    intro heq
    apply hhD
    exact MulAction.mem_stabilizer_iff.mpr heq
  have hxc : x • (h • b') = h • b' := by
    rw [Subgroup.conjBy, Subgroup.mem_map] at hxconj
    rcases hxconj with ⟨r, hrD, hrx⟩
    rw [← hrx]
    change (h * r * h⁻¹) • (h • b') = h • b'
    rw [mul_smul, mul_smul, inv_smul_smul,
      MulAction.mem_stabilizer_iff.mp hrD]
  by_contra hxne
  have hxGne : ((x : H) : G) ≠ 1 := by
    intro hxone
    apply hxne
    apply Subtype.ext
    exact hxone
  apply hatMostTwoFixedPoints ((x : H) : G) hxGne
      a b ((h • b' : X) : Omega) hab
  · exact Ne.symm (h • b').property
  · exact fun hbc => hhc_ne (Subtype.ext hbc.symm)
  refine ⟨(x : H).property, ?_, ?_⟩
  · exact congrArg Subtype.val hxb'
  · exact congrArg Subtype.val hxc

@[implicit_reducible]
private noncomputable def xi1115_rightNearFieldFieldOfComm
    (K : Type*) [PFAppendixII.RightNearField K]
    (hcomm : ∀ x y : K, x * y = y * x) : Field K :=
  { (inferInstance : PFAppendixII.RightNearField K) with
    mul_comm := hcomm
    left_distrib := by
      intro a b c
      calc
        a * (b + c) = (b + c) * a := hcomm _ _
        _ = b * a + c * a :=
          PFAppendixII.RightNearField.right_distrib _ _ _
        _ = a * b + a * c := by rw [hcomm b a, hcomm c a]
    nnqsmul := _
    nnqsmul_def _ _ := rfl
    qsmul := _
    qsmul_def _ _ := rfl }

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_fixedPointFree_of_odd_card_fixed_triple
    {H : Type*} [Group H] [Finite H]
    (phi : MulAut H) (hodd : Odd (Nat.card H))
    (hfixed3 : ∀ x y z : H,
      phi x = x → phi y = y → phi z = z →
        x = y ∨ x = z ∨ y = z) :
    MonoidHom.FixedPointFree phi := by
  intro x hx
  by_contra hx1
  have hxpow : phi (x ^ 2) = x ^ 2 := by simp [hx]
  rcases hfixed3 1 x (x ^ 2) (by simp) hx hxpow with
    h1x | h1sq | hxsq
  · exact hx1 h1x.symm
  · have hsq : x ^ 2 = 1 := h1sq.symm
    have hord_dvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).mp hord_dvd with hord | hord
    · exact hx1 (orderOf_eq_one_iff.mp hord)
    · exact hodd.not_two_dvd_nat (hord ▸ orderOf_dvd_natCard x)
  · have hx_eq_one : x = 1 := by
      apply mul_left_cancel (a := x)
      simpa [pow_two] using hxsq
    exact hx1 hx_eq_one

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_sharpSwap_nearField_inverse_and_commutative
    {G Omega K : Type*} [Group G] [MulAction G Omega]
    [Fintype Omega] [PFAppendixII.RightNearField K] [Finite K] [DecidableEq K]
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (ePoint : Omega ≃ Option K)
    (hPointA : ePoint a = none)
    (hPointB : ePoint b = some 0)
    (eUnits :
      MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a) ≃* Kˣ)
    (hUnitsAction :
      ∀ d : MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a),
        ∀ y : Option K,
          ePoint
              ((((d : MulAction.stabilizer G a) : G)⁻¹) •
                ePoint.symm y) =
            Option.map (fun x => x * (eUnits d : K)) y)
    (t : G) (htne : t ≠ 1) (htsq : t ^ 2 = 1)
    (hta : t • a = b) (htb : t • b = a)
    (htone : t • ePoint.symm (some 1) = ePoint.symm (some 1))
    {f : ℕ} (hf : 0 < f) (hKcard : Nat.card K = 2 ^ f) :
    (∀ y : Option K,
      ePoint (t • ePoint.symm y) =
        match y with
        | none => some 0
        | some x => if x = 0 then none else some x⁻¹) ∧
      ∀ x y : K, x * y = y * x := by
  let H := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H b'
  change D ≃* Kˣ at eUnits
  change ∀ d : D, ∀ y : Option K,
    ePoint ((((d : H) : G)⁻¹) • ePoint.symm y) =
      Option.map (fun x => x * (eUnits d : K)) y at hUnitsAction
  have htInv : t⁻¹ = t := by
    apply inv_eq_of_mul_eq_one_right
    simpa [pow_two] using htsq
  let conjD : D → D := fun d => by
    let dG : G := ((d : H) : G)
    have hda : dG • a = a := (d : H).property
    have hdb : dG • b = b := by
      simpa [dG, D, b', H] using congrArg Subtype.val d.property
    refine ⟨⟨t * dG * t⁻¹, ?_⟩, ?_⟩
    · change (t * dG * t⁻¹) • a = a
      rw [mul_smul, mul_smul, htInv, hta, hdb, htb]
    · apply Subtype.ext
      change (t * dG * t⁻¹) • b = b
      rw [mul_smul, mul_smul, htInv, htb, hda, hta]
  let conjDHom : D →* D :=
    { toFun := conjD
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        change t * (1 : G) * t⁻¹ = 1
        simp
      map_mul' := by
        intro d e
        apply Subtype.ext
        apply Subtype.ext
        change t * ((((d : H) : G) * ((e : H) : G))) * t⁻¹ =
          (t * ((d : H) : G) * t⁻¹) *
            (t * ((e : H) : G) * t⁻¹)
        group }
  have hconjDInv : Function.Involutive conjDHom := by
    intro d
    apply Subtype.ext
    apply Subtype.ext
    change t * (t * ((d : H) : G) * t⁻¹) * t⁻¹ = ((d : H) : G)
    rw [htInv]
    have htt : t * t = 1 := by
      simpa [pow_two] using htsq
    calc
      t * (t * ((d : H) : G) * t) * t =
          (t * t) * ((d : H) : G) * (t * t) := by group
      _ = ((d : H) : G) := by rw [htt]; simp
  let conjDEquiv : D ≃* D :=
    MulEquiv.ofBijective conjDHom
      ⟨hconjDInv.injective, hconjDInv.surjective⟩
  let theta : Kˣ ≃* Kˣ :=
    (eUnits.symm.trans conjDEquiv).trans eUnits
  have hthetaInv : Function.Involutive theta := by
    intro u
    change eUnits
        (conjDEquiv
          (eUnits.symm (eUnits (conjDEquiv (eUnits.symm u))))) = u
    rw [eUnits.symm_apply_apply]
    change eUnits
        (conjDHom (conjDHom (eUnits.symm u))) = u
    rw [hconjDInv, eUnits.apply_symm_apply]
  let pOne : Omega := ePoint.symm (some 1)
  have hthetaPoint : ∀ u : Kˣ,
      ePoint (t • ePoint.symm (some (u : K))) =
        some ((theta u : Kˣ) : K) := by
    intro u
    let d : D := eUnits.symm u
    let d' : D := conjDHom d
    have hpointU : ePoint.symm (some (u : K)) =
        (((d : H) : G)⁻¹) • pOne := by
      apply ePoint.injective
      rw [ePoint.apply_symm_apply]
      simpa [pOne, d] using (hUnitsAction d (some 1)).symm
    have hd'Inv : (((d' : H) : G)⁻¹) =
        t * (((d : H) : G)⁻¹) * t⁻¹ := by
      dsimp [d', conjDHom, conjD]
      group
    have hd'Units : eUnits d' = theta u := by
      change eUnits (conjDHom (eUnits.symm u)) =
        eUnits (conjDEquiv (eUnits.symm u))
      rfl
    calc
      ePoint (t • ePoint.symm (some (u : K))) =
          ePoint (t • ((((d : H) : G)⁻¹) • pOne)) := by rw [hpointU]
      _ = ePoint ((t * (((d : H) : G)⁻¹)) • pOne) := by
            exact congrArg ePoint
              (mul_smul t (((d : H) : G)⁻¹) pOne).symm
      _ = ePoint
          ((t * (((d : H) : G)⁻¹) * t⁻¹) • (t • pOne)) := by
            rw [← mul_smul]
            congr 2
            group
      _ = ePoint ((((d' : H) : G)⁻¹) • pOne) := by
            rw [hd'Inv, htone]
      _ = some (eUnits d' : K) := by
            simpa [pOne] using hUnitsAction d' (some 1)
      _ = some ((theta u : Kˣ) : K) := by rw [hd'Units]
  have hthetaFixedTriple : ∀ x y z : Kˣ,
      theta x = x → theta y = y → theta z = z →
        x = y ∨ x = z ∨ y = z := by
    have hfixedPoint : ∀ x : Kˣ, theta x = x →
        t • ePoint.symm (some (x : K)) =
          ePoint.symm (some (x : K)) := by
      intro x hx
      apply ePoint.injective
      rw [ePoint.apply_symm_apply, hthetaPoint x, hx]
    intro x y z hx hy hz
    by_cases hxy : x = y
    · exact Or.inl hxy
    by_cases hxz : x = z
    · exact Or.inr (Or.inl hxz)
    by_cases hyz : y = z
    · exact Or.inr (Or.inr hyz)
    exfalso
    let px : Omega := ePoint.symm (some (x : K))
    let py : Omega := ePoint.symm (some (y : K))
    let pz : Omega := ePoint.symm (some (z : K))
    have hpxy : px ≠ py := by
      intro h
      apply hxy
      apply Units.ext
      exact Option.some.inj (by
        simpa [px, py] using congrArg ePoint h)
    have hpxz : px ≠ pz := by
      intro h
      apply hxz
      apply Units.ext
      exact Option.some.inj (by
        simpa [px, pz] using congrArg ePoint h)
    have hpyz : py ≠ pz := by
      intro h
      apply hyz
      apply Units.ext
      exact Option.some.inj (by
        simpa [py, pz] using congrArg ePoint h)
    exact hatMostTwoFixedPoints t htne px py pz
      hpxy hpxz hpyz
      ⟨hfixedPoint x hx, hfixedPoint y hy, hfixedPoint z hz⟩
  have hKcardEven : Even (Nat.card K) := by
    rw [hKcard]
    exact Nat.even_pow.mpr ⟨even_two, hf.ne'⟩
  have hUnitsOdd : Odd (Nat.card Kˣ) := by
    rw [Nat.card_units]
    exact Nat.Even.sub_odd Nat.card_pos hKcardEven odd_one
  have hthetaFree : MonoidHom.FixedPointFree theta :=
    xi1115_fixedPointFree_of_odd_card_fixed_triple
      theta hUnitsOdd hthetaFixedTriple
  have hthetaEqInv : ∀ u : Kˣ, theta u = u⁻¹ := by
    intro u
    exact congrFun (hthetaFree.coe_eq_inv_of_involutive hthetaInv) u
  have hcommUnits : ∀ x y : Kˣ, x * y = y * x := by
    intro x y
    exact (hthetaFree.commute_all_of_involutive hthetaInv x y).eq
  constructor
  · intro y
    cases y with
    | none =>
        have hPointA_symm : ePoint.symm none = a := by
          apply ePoint.injective
          rw [ePoint.apply_symm_apply, hPointA]
        rw [hPointA_symm, hta, hPointB]
    | some x =>
        by_cases hx : x = 0
        · subst x
          have hPointB_symm : ePoint.symm (some 0) = b := by
            apply ePoint.injective
            rw [ePoint.apply_symm_apply, hPointB]
          rw [hPointB_symm, htb, hPointA]
          simp
        · let u : Kˣ := Units.mk0 x hx
          have htheta := hthetaPoint u
          rw [hthetaEqInv u] at htheta
          simpa [u, hx] using htheta
  · intro x y
    by_cases hx : x = 0
    · simp [hx]
    by_cases hy : y = 0
    · simp [hy]
    let ux : Kˣ := Units.mk0 x hx
    let uy : Kˣ := Units.mk0 y hy
    have hxy : ux * uy = uy * ux := hcommUnits ux uy
    simpa [ux, uy] using congrArg (fun z : Kˣ => (z : K)) hxy
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_sharpTriple_charTwo_pgl
    {G : Type u} {Omega : Type v} [Group G] [Finite G] [MulAction G Omega]
    [Fintype Omega]
    (htwo : MulAction.IsMultiplyPretransitive G Omega 2)
    (hsharp :
      ∀ a b c a' b' c' : Omega,
        a ≠ b → a ≠ c → b ≠ c →
        a' ≠ b' → a' ≠ c' → b' ≠ c' →
          ∃! g : G,
            g • a = a' ∧ g • b = b' ∧ g • c = c')
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob :
      IsFrobeniusGroupWithKernelComplement F
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFcomm : IsMulCommutative F)
    {f : ℕ} (hf : 0 < f) (hFcard : Nat.card F = 2 ^ f)
    (hGcard :
      Nat.card G = (2 ^ f + 1) * 2 ^ f * (2 ^ f - 1)) :
    ∃ (K : Type u) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ f ∧
        Nonempty (G ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
  classical
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  rcases
      huppert_blackburn_XI_sharpTriple_exists_rightNearField
        htwo hsharp a b hab F hFrob hFcomm with
    ⟨K, hNF, hKfinite, eAdd, eUnits, hmulCoordinate⟩
  letI : PFAppendixII.RightNearField K := hNF
  letI : Finite K := hKfinite
  have hKcard : Nat.card K = 2 ^ f := by
    calc
      Nat.card K = Nat.card (Additive F) :=
        Nat.card_congr eAdd.symm.toEquiv
      _ = Nat.card F := rfl
      _ = 2 ^ f := hFcard
  obtain ⟨ePoint, hPointA, hPointB, hPointF⟩ :=
    huppert_blackburn_XI_pointStabilizer_exists_projectivePointEquiv
      htwo a b hab F hFrob eAdd
  have hKernelAction :=
    huppert_blackburn_XI_projectivePointEquiv_kernel_action
      a b F eAdd ePoint hPointA hPointF
  have hUnitsAction :=
    huppert_blackburn_XI_projectivePointEquiv_twoPointStabilizer_action
      a b hab F eAdd eUnits hmulCoordinate ePoint hPointA hPointF
  obtain ⟨t, htne, htsq, hta, htb, htone⟩ :=
    huppert_blackburn_XI_projectivePointEquiv_exists_normalized_swap
      hsharp a b hab ePoint hPointA hPointB zero_ne_one
  letI : DecidableEq K := Classical.decEq K
  obtain ⟨hTauInverse, hcomm⟩ :=
    xi1115_sharpSwap_nearField_inverse_and_commutative
      hatMostTwoFixedPoints a b hab ePoint hPointA hPointB
      eUnits hUnitsAction t htne htsq hta htb htone hf hKcard
  let fieldInst : Field K := xi1115_rightNearFieldFieldOfComm K hcomm
  letI : Field K := fieldInst
  have hStabilizerAffine (h : MulAction.stabilizer G a) :
      ∃ f0 : F,
        ∃ d0 : MulAction.stabilizer (MulAction.stabilizer G a) b',
          h = (f0 : MulAction.stabilizer G a) *
              (d0 : MulAction.stabilizer G a)⁻¹ ∧
            ∀ y : Option K,
              ePoint ((h : G) • ePoint.symm y) =
                Option.map
                  (fun x =>
                    eAdd (Additive.ofMul f0) + x * (eUnits d0 : K)) y := by
    obtain ⟨fd, hfd, _hfdUnique⟩ := hFrob.isComplement'.existsUnique h
    let f0 : F := fd.1
    let d0 : MulAction.stabilizer (MulAction.stabilizer G a) b' := fd.2⁻¹
    have hdecomp :
        h = (f0 : MulAction.stabilizer G a) *
          (d0 : MulAction.stabilizer G a)⁻¹ := by
      simpa [f0, d0] using hfd.symm
    refine ⟨f0, d0, hdecomp, ?_⟩
    intro y
    have hdActionPoint :
        (((d0 : MulAction.stabilizer G a) : G)⁻¹) •
            ePoint.symm y =
          ePoint.symm
            (Option.map (fun x => x * (eUnits d0 : K)) y) := by
      apply ePoint.injective
      rw [hUnitsAction d0 y, ePoint.apply_symm_apply]
    have hdecompG :
        (h : G) =
          ((f0 : MulAction.stabilizer G a) : G) *
            (((d0 : MulAction.stabilizer G a) : G)⁻¹) :=
      congrArg Subtype.val hdecomp
    calc
      ePoint ((h : G) • ePoint.symm y) =
          ePoint
            (((f0 : MulAction.stabilizer G a) : G) •
              ((((d0 : MulAction.stabilizer G a) : G)⁻¹) •
                ePoint.symm y)) := by
        rw [hdecompG, mul_smul]
      _ = ePoint
            (((f0 : MulAction.stabilizer G a) : G) •
              ePoint.symm
                (Option.map (fun x => x * (eUnits d0 : K)) y)) := by
        rw [hdActionPoint]
      _ = Option.map
            (fun x => eAdd (Additive.ofMul f0) + x)
            (Option.map (fun x => x * (eUnits d0 : K)) y) :=
        hKernelAction f0 _
      _ = Option.map
            (fun x =>
              eAdd (Additive.ofMul f0) + x * (eUnits d0 : K)) y := by
        cases y <;> rfl
  have htMoves : t • a ≠ a := by
    rw [hta]
    exact hab.symm
  have hDoubleCoset :=
    huppert_II_1_12_b_doubleCoset_decomposition htwo a t htMoves
  let tau : Equiv.Perm (Option K) :=
    ePoint.symm.trans ((MulAction.toPerm t).trans ePoint)
  have hTau :
      ∀ y : Option K,
        tau y =
          match y with
          | none => some 0
          | some x => if x = 0 then none else some x⁻¹ := by
    intro y
    change ePoint (t • ePoint.symm y) = _
    exact hTauInverse y
  let affinePerm (c : K) (u : Kˣ) : Equiv.Perm (Option K) :=
    Equiv.optionCongr (u.mulRight.trans (Equiv.addLeft c))
  have hAffinePerm (c : K) (u : Kˣ) (y : Option K) :
      affinePerm c u y =
        Option.map (fun x => c + x * (u : K)) y := rfl
  let rho : G →* Equiv.Perm (Option K) :=
    ePoint.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G Omega)
  have hrhoApply (g : G) (y : Option K) :
      rho g y = ePoint (g • ePoint.symm y) := rfl
  have hrhoT : rho t = tau := rfl
  let c : Omega := ePoint.symm (some 1)
  have hac : a ≠ c := by
    intro h
    have heq := congrArg ePoint h
    simp [c, hPointA] at heq
  have hbc : b ≠ c := by
    intro h
    have heq := congrArg ePoint h
    simp [c, hPointB] at heq
  have hrhoInjective : Function.Injective rho := by
    intro g h hgh
    have hactionEq (x : Omega) : g • x = h • x := by
      apply ePoint.injective
      have heq :=
        congrArg (fun sigma : Equiv.Perm (Option K) => sigma (ePoint x)) hgh
      simpa [hrhoApply] using heq
    have hgab : g • a ≠ g • b := by
      intro heq
      exact hab ((MulAction.toPerm g).injective heq)
    have hgac : g • a ≠ g • c := by
      intro heq
      exact hac ((MulAction.toPerm g).injective heq)
    have hgbc : g • b ≠ g • c := by
      intro heq
      exact hbc ((MulAction.toPerm g).injective heq)
    exact ExistsUnique.unique
      (hsharp a b c (g • a) (g • b) (g • c)
        hab hac hbc hgab hgac hgbc)
      ⟨rfl, rfl, rfl⟩
      ⟨(hactionEq a).symm, (hactionEq b).symm, (hactionEq c).symm⟩
  have hAffineRealized (f0 : F)
      (d0 : MulAction.stabilizer (MulAction.stabilizer G a) b') :
      rho
          (((f0 : MulAction.stabilizer G a) *
            (d0 : MulAction.stabilizer G a)⁻¹ :
              MulAction.stabilizer G a) : G) =
        affinePerm (eAdd (Additive.ofMul f0)) (eUnits d0) := by
    apply Equiv.Perm.ext
    intro y
    have hdActionPoint :
        (((d0 : MulAction.stabilizer G a) : G)⁻¹) •
            ePoint.symm y =
          ePoint.symm
            (Option.map (fun x => x * (eUnits d0 : K)) y) := by
      apply ePoint.injective
      rw [hUnitsAction d0 y, ePoint.apply_symm_apply]
    calc
      rho
          (((f0 : MulAction.stabilizer G a) *
            (d0 : MulAction.stabilizer G a)⁻¹ :
              MulAction.stabilizer G a) : G) y =
          ePoint
            (((f0 : MulAction.stabilizer G a) : G) •
              ((((d0 : MulAction.stabilizer G a) : G)⁻¹) •
                ePoint.symm y)) := by
        rw [hrhoApply]
        change ePoint
          (((((f0 : MulAction.stabilizer G a) : G) *
            (((d0 : MulAction.stabilizer G a) : G)⁻¹)) •
              ePoint.symm y)) = _
        rw [mul_smul]
      _ = ePoint
            (((f0 : MulAction.stabilizer G a) : G) •
              ePoint.symm
                (Option.map (fun x => x * (eUnits d0 : K)) y)) := by
        rw [hdActionPoint]
      _ = Option.map
            (fun x => eAdd (Additive.ofMul f0) + x)
            (Option.map (fun x => x * (eUnits d0 : K)) y) :=
        hKernelAction f0 _
      _ = Option.map
            (fun x =>
              eAdd (Additive.ofMul f0) + x * (eUnits d0 : K)) y := by
        cases y <;> rfl
      _ = affinePerm (eAdd (Additive.ofMul f0)) (eUnits d0) y :=
        (hAffinePerm _ _ y).symm
  let stabilizerRho :
      MulAction.stabilizer G a →* Equiv.Perm (Option K) :=
    rho.comp (Subgroup.subtype (MulAction.stabilizer G a))
  let A : Subgroup (Equiv.Perm (Option K)) := stabilizerRho.range
  have hA :
      (A : Set (Equiv.Perm (Option K))) =
        {sigma | ∃ c : K, ∃ u : Kˣ, sigma = affinePerm c u} := by
    ext sigma
    constructor
    · intro hsigma
      change sigma ∈ stabilizerRho.range at hsigma
      rcases hsigma with ⟨h, rfl⟩
      rcases hStabilizerAffine h with
        ⟨f0, d0, _hdecomp, haction⟩
      refine ⟨eAdd (Additive.ofMul f0), eUnits d0, ?_⟩
      apply Equiv.Perm.ext
      intro y
      change rho (h : G) y =
        affinePerm (eAdd (Additive.ofMul f0)) (eUnits d0) y
      rw [hrhoApply, haction y, hAffinePerm]
    · rintro ⟨c0, u0, rfl⟩
      change affinePerm c0 u0 ∈ stabilizerRho.range
      let f0 : F := (eAdd.symm c0).toMul
      let d0 :
          MulAction.stabilizer (MulAction.stabilizer G a) b' :=
        eUnits.symm u0
      refine ⟨(f0 : MulAction.stabilizer G a) *
        (d0 : MulAction.stabilizer G a)⁻¹, ?_⟩
      change rho
          ((((f0 : MulAction.stabilizer G a) *
            (d0 : MulAction.stabilizer G a)⁻¹ :
              MulAction.stabilizer G a) : G)) =
        affinePerm c0 u0
      simpa [f0, d0] using hAffineRealized f0 d0
  have hRange :
      (rho.range : Set (Equiv.Perm (Option K))) =
        (A : Set (Equiv.Perm (Option K))) ∪
          DoubleCoset.doubleCoset tau
            (A : Set (Equiv.Perm (Option K)))
            (A : Set (Equiv.Perm (Option K))) := by
    ext sigma
    constructor
    · intro hsigma
      change sigma ∈ rho.range at hsigma
      rcases hsigma with ⟨g, rfl⟩
      have hg :
          g ∈ (MulAction.stabilizer G a : Set G) ∪
            DoubleCoset.doubleCoset t
              (MulAction.stabilizer G a)
              (MulAction.stabilizer G a) := by
        rw [hDoubleCoset]
        exact Set.mem_univ g
      rcases hg with hg | hg
      · left
        change rho g ∈ stabilizerRho.range
        exact ⟨⟨g, hg⟩, rfl⟩
      · right
        rcases DoubleCoset.mem_doubleCoset.mp hg with
          ⟨h1, hh1, h2, hh2, heq⟩
        apply DoubleCoset.mem_doubleCoset.mpr
        refine ⟨stabilizerRho ⟨h1, hh1⟩, ⟨⟨h1, hh1⟩, rfl⟩,
          stabilizerRho ⟨h2, hh2⟩, ⟨⟨h2, hh2⟩, rfl⟩, ?_⟩
        change rho g = rho h1 * tau * rho h2
        rw [heq, map_mul, map_mul, hrhoT]
    · intro hsigma
      rcases hsigma with hsigma | hsigma
      · change sigma ∈ stabilizerRho.range at hsigma
        rcases hsigma with ⟨h, rfl⟩
        change rho (h : G) ∈ rho.range
        exact ⟨(h : G), rfl⟩
      · rcases DoubleCoset.mem_doubleCoset.mp hsigma with
          ⟨sigma1, hsigma1, sigma2, hsigma2, hsigma⟩
        change sigma1 ∈ stabilizerRho.range at hsigma1
        change sigma2 ∈ stabilizerRho.range at hsigma2
        rcases hsigma1 with ⟨h1, rfl⟩
        rcases hsigma2 with ⟨h2, rfl⟩
        change sigma ∈ rho.range
        refine ⟨(h1 : G) * t * (h2 : G), ?_⟩
        rw [map_mul, map_mul, hrhoT]
        exact hsigma.symm
  let q := 2 ^ f
  have hfactor : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    let r := q - 1
    have hqpos : 0 < q := by simp [q]
    have hq : q = r + 1 := by
      dsimp [r]
      omega
    rw [hq]
    simp only [Nat.add_sub_cancel]
    apply (tsub_eq_iff_eq_add_of_le (Nat.one_le_pow' 2 r)).2
    ring
  have hGcardField :
      Nat.card G = Nat.card K * (Nat.card K ^ 2 - 1) := by
    calc
      Nat.card G = (q + 1) * q * (q - 1) := by simpa [q] using hGcard
      _ = q * (q ^ 2 - 1) := by rw [hfactor]; ac_rfl
      _ = Nat.card K * (Nat.card K ^ 2 - 1) := by rw [hKcard]
  have hRangeCard :
      Nat.card rho.range = Nat.card K * (Nat.card K ^ 2 - 1) := by
    calc
      Nat.card rho.range = Nat.card G :=
        (Nat.card_congr (Equiv.ofInjective rho hrhoInjective)).symm
      _ = Nat.card K * (Nat.card K ^ 2 - 1) := hGcardField
  rcases
      xi26_pglRange_of_tau rho A tau affinePerm
        hAffinePerm hA hTau hRange hRangeCard with
    ⟨ePGL⟩
  let eRange : G ≃* rho.range := MonoidHom.ofInjective hrhoInjective
  exact ⟨K, fieldInst, hKfinite, hKcard, ⟨eRange.trans ePGL⟩⟩

private theorem xi1115_card_pgl2
    {K : Type u} [Field K] [Finite K] :
    Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) =
      Nat.card K * (Nat.card K ^ 2 - 1) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let GL2 := GL (Fin 2) K
  let PGL2 := Matrix.ProjGenLinGroup (Fin 2) K
  let centerGL := Subgroup.center GL2
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin 2) : Kˣ → GL2) := by
    intro x y hxy
    apply Units.ext
    have h := congrArg (fun A : GL2 =>
      ((A : Matrix (Fin 2) (Fin 2) K) 0 0)) hxy
    simpa [Matrix.GeneralLinearGroup.scalar] using h
  have hcenter : Nat.card centerGL = Nat.card K - 1 := by
    dsimp [centerGL, GL2]
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    calc
      Nat.card
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range =
          Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofInjective
          (Matrix.GeneralLinearGroup.scalar (Fin 2)) hscalar_inj)).symm
      _ = Nat.card K - 1 := by
        simpa [Nat.card_eq_fintype_card] using Fintype.card_units K
  have hGL : Nat.card GL2 =
      (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 2 - Nat.card K) := by
    simpa [GL2, Fin.prod_univ_two] using
      (Matrix.card_GL_field (𝔽 := K) 2)
  let mkPGL : GL2 →* PGL2 := Matrix.ProjGenLinGroup.mk
  have hrange : mkPGL.range = ⊤ :=
    MonoidHom.range_eq_top.mpr Matrix.ProjGenLinGroup.mk_surjective
  have hindex : centerGL.index = Nat.card PGL2 := by
    calc
      centerGL.index = mkPGL.ker.index := by
        rw [Matrix.ProjGenLinGroup.ker_mk]
      _ = Nat.card mkPGL.range := Subgroup.index_ker mkPGL
      _ = Nat.card PGL2 := by rw [hrange]; simp
  have hmul := centerGL.index_mul_card
  rw [hindex, hcenter, hGL] at hmul
  have hdiff : Nat.card K ^ 2 - Nat.card K =
      Nat.card K * (Nat.card K - 1) := by
    rw [pow_two]
    calc
      Nat.card K * Nat.card K - Nat.card K =
          Nat.card K * Nat.card K - Nat.card K * 1 := by simp
      _ = Nat.card K * (Nat.card K - 1) :=
        (Nat.mul_sub_left_distrib _ _ _).symm
  rw [hdiff] at hmul
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.sub_pos_iff_lt.mpr (Finite.one_lt_card (α := K)))
  calc
    (Nat.card K - 1) * Nat.card PGL2 =
        Nat.card PGL2 * (Nat.card K - 1) := by ac_rfl
    _ = (Nat.card K ^ 2 - 1) *
        (Nat.card K * (Nat.card K - 1)) := hmul
    _ = (Nat.card K - 1) *
        (Nat.card K * (Nat.card K ^ 2 - 1)) := by ring

private theorem xi1115_charTwo_pslEquivPgl
    {K : Type u} [Field K] [Finite K] {f : ℕ}
    (hKcard : Nat.card K = 2 ^ f) :
    Nonempty
      (PSL2MatrixGroup K ≃*
        Matrix.ProjGenLinGroup (Fin 2) K) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  letI : Finite (Matrix.ProjGenLinGroup (Fin 2) K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk
      Matrix.ProjGenLinGroup.mk_surjective
  letI : CharP K 2 :=
    charP_of_card_eq_prime_pow (by
      simpa [Nat.card_eq_fintype_card] using hKcard)
  have htwozero : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hneg_one : (-1 : K) = 1 := by
    apply (neg_eq_iff_add_eq_zero).2
    rw [show (1 : K) + 1 = 2 by norm_num, htwozero]
  have hcenter :
      Nat.card
          (Subgroup.center
            (Matrix.SpecialLinearGroup (Fin 2) K)) = 1 :=
    huppert614_card_center_of_neg_one_eq_one hneg_one
  have hPSLcard := huppert614_card_psl_mul_center (K := K)
  rw [hcenter, mul_one] at hPSLcard
  have hPSLPGLcard :
      Nat.card (PSL2MatrixGroup K) =
        Nat.card (Matrix.ProjGenLinGroup (Fin 2) K) :=
    hPSLcard.trans (xi1115_card_pgl2 (K := K)).symm
  obtain ⟨_, _, iota, _, hiota, _⟩ :=
    huppert_blackburn_XI_example_1_3_a K
  exact ⟨MulEquiv.ofBijective iota
    ((Nat.bijective_iff_injective_and_card iota).2
      ⟨hiota, hPSLPGLcard⟩)⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_pgl_charTwo_nonsplitTorus
    {K : Type u} [Field K] [Finite K] {l : ℕ}
    (hl : 0 < l) (hKcard : Nat.card K = 2 ^ l) :
    ∃ S : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K),
      ∃ w : Matrix.ProjGenLinGroup (Fin 2) K,
        IsCyclic S ∧
        Nat.card S = 2 ^ l + 1 ∧
        w ∈ Subgroup.normalizer
          (S : Set (Matrix.ProjGenLinGroup (Fin 2) K)) ∧
        w ∉ S ∧
        w * w = 1 ∧
        (∀ t : Matrix.ProjGenLinGroup (Fin 2) K,
          t ∈ S → w * t * w⁻¹ = t⁻¹) ∧
        Nat.card (S ⊔ Subgroup.zpowers w :
          Subgroup (Matrix.ProjGenLinGroup (Fin 2) K)) =
            2 * Nat.card S ∧
        ∀ R : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K),
          R ≤ S → R ≠ ⊥ →
            Subgroup.normalizer
              (R : Set (Matrix.ProjGenLinGroup (Fin 2) K)) =
                S ⊔ Subgroup.zpowers w := by
  obtain ⟨e⟩ := xi1115_charTwo_pslEquivPgl hKcard
  obtain ⟨S0, w0, hcyclic0, hS0card, hw0_normalizer,
      hw0_not_mem, hw0_sq, hw0_inv, hcandidate_card,
      hnormalizer0⟩ :=
    huppert_II_8_4_nonsplit_torus_reflection_data
      (p := 2) (f := l) hKcard
  have hqEven : Even (2 ^ l) :=
    Nat.even_pow.mpr ⟨even_two, hl.ne'⟩
  have hqSubOdd : Odd (2 ^ l - 1) :=
    Nat.Even.sub_odd
      (pow_pos (by norm_num : 0 < (2 : ℕ)) l) hqEven odd_one
  have hgcd : Nat.gcd (2 ^ l - 1) 2 = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp hqSubOdd.coprime_two_right
  have hS0card' : Nat.card S0 = 2 ^ l + 1 := by
    rw [hKcard, hgcd, Nat.div_one] at hS0card
    exact hS0card
  let S := S0.map e.toMonoidHom
  let w := e w0
  refine ⟨S, w, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · letI : IsCyclic S0 := hcyclic0
    exact isCyclic_of_surjective (e.subgroupMap S0).toMonoidHom
      (e.subgroupMap S0).surjective
  · dsimp [S]
    rw [Subgroup.card_map_of_injective e.injective, hS0card']
  · dsimp [S, w]
    have hw_map : e w0 ∈
        (Subgroup.normalizer
          (S0 : Set (PSL2MatrixGroup K))).map e.toMonoidHom :=
      Subgroup.mem_map_of_mem e.toMonoidHom hw0_normalizer
    rwa [Subgroup.map_equiv_normalizer_eq S0 e] at hw_map
  · dsimp [S, w]
    intro hwmem
    apply hw0_not_mem
    have hw0mem : e.symm (e w0) ∈ S0 :=
      Subgroup.mem_map_equiv.mp hwmem
    simpa using hw0mem
  · dsimp [w]
    simpa using congrArg e hw0_sq
  · dsimp [S, w]
    intro t ht
    have ht0 : e.symm t ∈ S0 :=
      Subgroup.mem_map_equiv.mp ht
    simpa using congrArg e (hw0_inv (e.symm t) ht0)
  · dsimp [S, w]
    have heq : (S0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom =
        S0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) := by
      simpa using
        (Subgroup.map_sup S0 (Subgroup.zpowers w0) e.toMonoidHom).trans
          (congrArg
            (fun R : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K) =>
              S0.map e.toMonoidHom ⊔ R)
            (MonoidHom.map_zpowers e.toMonoidHom w0))
    calc
      Nat.card
          (S0.map e.toMonoidHom ⊔ Subgroup.zpowers (e w0) :
            Subgroup (Matrix.ProjGenLinGroup (Fin 2) K)) =
          Nat.card ((S0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom) :=
        congrArg
          (fun R : Subgroup (Matrix.ProjGenLinGroup (Fin 2) K) =>
            Nat.card R) heq.symm
      _ = Nat.card (S0 ⊔ Subgroup.zpowers w0 :
          Subgroup (PSL2MatrixGroup K)) := by
        rw [Subgroup.card_map_of_injective e.injective]
      _ = 2 * Nat.card S0 := hcandidate_card
      _ = 2 * Nat.card (S0.map e.toMonoidHom) := by
        rw [Subgroup.card_map_of_injective e.injective]
  · dsimp [S, w]
    intro R hR_le hR_ne
    let R0 : Subgroup (PSL2MatrixGroup K) :=
      R.map e.symm.toMonoidHom
    have hR0_le : R0 ≤ S0 := by
      intro x hx
      have hex : e x ∈ R := by
        change x ∈ R.map e.symm.toMonoidHom at hx
        rwa [Subgroup.mem_map_equiv] at hx
      have hexS : e x ∈ S0.map e.toMonoidHom := hR_le hex
      rw [Subgroup.mem_map_equiv] at hexS
      simpa using hexS
    have hR0_ne : R0 ≠ ⊥ := by
      intro hR0
      apply hR_ne
      apply (Subgroup.map_eq_bot_iff_of_injective R
        (f := e.symm.toMonoidHom) e.symm.injective).mp
      exact hR0
    have hR0_map : R0.map e.toMonoidHom = R := by
      apply (Subgroup.map_symm_eq_iff_map_eq (K := R0) (e := e)).mp
      rfl
    have hmap := congrArg
      (fun T : Subgroup (PSL2MatrixGroup K) => T.map e.toMonoidHom)
      (hnormalizer0 R0 hR0_le hR0_ne)
    change (Subgroup.normalizer
        (R0 : Set (PSL2MatrixGroup K))).map e.toMonoidHom =
      (S0 ⊔ Subgroup.zpowers w0).map e.toMonoidHom at hmap
    rw [Subgroup.map_equiv_normalizer_eq R0 e, hR0_map,
      Subgroup.map_sup, MonoidHom.map_zpowers] at hmap
    exact hmap


set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_rankOneOrbit_charTwo_pgl
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [Fintype Omega]
    (M I R : Subgroup G) (a b : Omega) (hab : a ≠ b)
    (hI_le_M : I ≤ M) (hR_le_M : R ≤ M)
    (hstab :
      MulAction.stabilizer M a = (I ⊔ R).subgroupOf M)
    (hbOrbit : b ∈ MulAction.orbit M a)
    (hRmem : ∀ g : G, g ∈ R ↔ g • a = a ∧ g • b = b)
    (hRnormalizesI : R ≤ Subgroup.normalizer I)
    (hdisjoint : Disjoint I R)
    (hIne : I ≠ ⊥) (hRne : R ≠ ⊥)
    (hIcomm : IsMulCommutative I)
    {f : ℕ} (hf : 0 < f)
    (hIcard : Nat.card I = 2 ^ f)
    (hRcard : Nat.card R = 2 ^ f - 1)
    (hMcard : Nat.card M = (2 ^ f + 1) * 2 ^ f * (2 ^ f - 1))
    (hsharp :
      let O := MulAction.orbit M a
      ∀ x y z x' y' z' : O,
        x ≠ y → x ≠ z → y ≠ z →
          x' ≠ y' → x' ≠ z' → y' ≠ z' →
            ∃! g : M,
              g • x = x' ∧ g • y = y' ∧ g • z = z')
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ x y z : Omega,
          x ≠ y → x ≠ z → y ≠ z →
            ¬ (g • x = x ∧ g • y = y ∧ g • z = z)) :
    ∃ (K : Type u) (_ : Field K) (_ : Finite K),
      Nat.card K = 2 ^ f ∧
        Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
  classical
  let O := MulAction.orbit M a
  let aO : O := ⟨a, MulAction.mem_orbit_self a⟩
  let bO : O := ⟨b, hbOrbit⟩
  have habO : aO ≠ bO := by
    intro h
    exact hab (congrArg Subtype.val h)
  let K0 : Subgroup M := I.subgroupOf M
  let R0 : Subgroup M := R.subgroupOf M
  let H := MulAction.stabilizer M aO
  have hstabO : H = (I ⊔ R).subgroupOf M := by
    ext x
    have hx := SetLike.ext_iff.mp hstab x
    constructor
    · intro hxH
      have hx_stab : x • aO = aO := MulAction.mem_stabilizer_iff.mp hxH
      have hx_a : (x : M) • a = a := congrArg Subtype.val hx_stab
      have hx_stabM : x ∈ MulAction.stabilizer M a :=
        MulAction.mem_stabilizer_iff.mpr (by
          -- (x : M) • a = (x : G) • a since M is a subgroup of G
          simpa using hx_a)
      exact (hx.mp hx_stabM)
    · intro hx_mem
      have hx_stabM : x • a = a :=
        MulAction.mem_stabilizer_iff.mp (hx.mpr hx_mem)
      have hx_a : (x : M) • a = a := by
        -- (x : M) • a = (x : G) • a
        simpa using hx_stabM
      have hx_stab : x • aO = aO := Subtype.ext hx_a
      exact MulAction.mem_stabilizer_iff.mpr hx_stab
  let S0 : Subgroup M := K0 ⊔ R0
  have hS0 : S0 = H := by
    calc
      S0 = (I ⊔ R).subgroupOf M := by
        dsimp [S0]
        symm
        simpa [K0, R0] using
          (Subgroup.subgroupOf_sup
            (A := I) (A' := R) (B := M) hI_le_M hR_le_M)
      _ = H := hstabO.symm
  have hR0normalizesK0 : R0 ≤ Subgroup.normalizer K0 := by
    intro d hd
    change (d : G) ∈ R at hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    simpa [K0, Subgroup.mem_subgroupOf] using
      ((Subgroup.mem_normalizer_iff.mp (hRnormalizesI hd)) (x : G))
  have hdisjoint0 : Disjoint K0 R0 := by
    rw [Subgroup.disjoint_def]
    intro x hxI hxR
    apply Subtype.ext
    exact (Subgroup.disjoint_def.mp hdisjoint) hxI hxR
  have hK0ne : K0 ≠ ⊥ := by
    intro hbot
    apply hIne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    let xM : M := ⟨x, hI_le_M hx⟩
    have hx0 : xM ∈ K0 := hx
    rw [hbot] at hx0
    exact Subgroup.mem_bot.mpr
      (by simpa [xM] using congrArg Subtype.val (Subgroup.mem_bot.mp hx0))
  have hR0ne : R0 ≠ ⊥ := by
    intro hbot
    apply hRne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    let xM : M := ⟨x, hR_le_M hx⟩
    have hx0 : xM ∈ R0 := hx
    rw [hbot] at hx0
    exact Subgroup.mem_bot.mpr
      (by simpa [xM] using congrArg Subtype.val (Subgroup.mem_bot.mp hx0))
  have hK0leH : K0 ≤ H := by
    rw [← hS0]
    exact le_sup_left
  have hR0leH : R0 ≤ H := by
    rw [← hS0]
    exact le_sup_right
  let bH : SubMulAction.ofStabilizer M aO := ⟨bO, habO.symm⟩
  have hD :
      MulAction.stabilizer H bH = R0.subgroupOf H := by
    ext x
    have hxa : (((x : H) : M) : G) • a = a := by
      have hx_stab : x • aO = aO := MulAction.mem_stabilizer_iff.mp x.property
      exact congrArg Subtype.val hx_stab
    constructor
    · intro hx
      have hxbH := MulAction.mem_stabilizer_iff.mp hx
      have hxb : (((x : H) : M) : G) • b = b := by
        calc
          (((x : H) : M) : G) • b = (x • bH : Omega) := by
            simp [bH, bO, H, aO]
          _ = (bH : Omega) := congrArg (fun q : SubMulAction.ofStabilizer M aO => (q : Omega)) hxbH
          _ = b := by simp [bH, bO]
      have hxR : (((x : H) : M) : G) ∈ R :=
        (hRmem _).2 ⟨hxa, hxb⟩
      simpa [R0, Subgroup.mem_subgroupOf] using hxR
    · intro hx
      have hxR : (((x : H) : M) : G) ∈ R := by
        simpa [R0, Subgroup.mem_subgroupOf] using hx
      have hxb : (((x : H) : M) : G) • b = b :=
        ((hRmem _).1 hxR).2
      rw [MulAction.mem_stabilizer_iff]
      apply Subtype.ext
      apply Subtype.ext
      exact hxb
  have hAtMostO :
      ∀ g : M, g ≠ 1 →
        ∀ x y z : O,
          x ≠ y → x ≠ z → y ≠ z →
            ¬ (g • x = x ∧ g • y = y ∧ g • z = z) := by
    intro g hg x y z hxy hxz hyz hfix
    have hgG : (g : G) ≠ 1 := by
      intro h
      apply hg
      exact Subtype.ext h
    have hxyG : (x : Omega) ≠ (y : Omega) := by
      intro h
      exact hxy (Subtype.ext h)
    have hxzG : (x : Omega) ≠ (z : Omega) := by
      intro h
      exact hxz (Subtype.ext h)
    have hyzG : (y : Omega) ≠ (z : Omega) := by
      intro h
      exact hyz (Subtype.ext h)
    apply hatMostTwoFixedPoints (g : G) hgG
      (x : Omega) (y : Omega) (z : Omega) hxyG hxzG hyzG
    exact ⟨congrArg Subtype.val hfix.1,
      congrArg Subtype.val hfix.2.1,
      congrArg Subtype.val hfix.2.2⟩
  have hTIH := xi1115_twoPointStabilizer_TI
    hAtMostO aO bO habO
  have hTIS0 :
      ∀ g : S0, g ∉ R0.subgroupOf S0 →
        Disjoint (R0.subgroupOf S0)
          ((R0.subgroupOf S0).conjBy g) := by
    rw [hS0, ← hD]
    simpa [H, bH] using hTIH
  have hFrobS0 :
      IsFrobeniusGroupWithKernelComplement
        (K0.subgroupOf S0) (R0.subgroupOf S0) :=
    xi1115_frobenius_subgroupOf_sup
      K0 R0 hR0normalizesK0 hdisjoint0 hK0ne hR0ne hTIS0
  have hFrobH :
      IsFrobeniusGroupWithKernelComplement
        (K0.subgroupOf H) (MulAction.stabilizer H bH) := by
    rw [hD, ← hS0]
    exact hFrobS0
  have hK0card : Nat.card K0 = Nat.card I :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hI_le_M).toEquiv
  have hR0card : Nat.card R0 = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR_le_M).toEquiv
  have hKHcard : Nat.card (K0.subgroupOf H) = Nat.card I := by
    calc
      Nat.card (K0.subgroupOf H) = Nat.card K0 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0leH).toEquiv
      _ = Nat.card I := hK0card
  have hDHcard :
      Nat.card (MulAction.stabilizer H bH) = Nat.card R := by
    rw [hD]
    calc
      Nat.card (R0.subgroupOf H) = Nat.card R0 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hR0leH).toEquiv
      _ = Nat.card R := hR0card
  have hHcard : Nat.card H = 2 ^ f * (2 ^ f - 1) := by
    calc
      Nat.card H =
          Nat.card (K0.subgroupOf H) *
            Nat.card (MulAction.stabilizer H bH) :=
        hFrobH.isComplement'.card_mul_card.symm
      _ = 2 ^ f * (2 ^ f - 1) := by
        rw [hKHcard, hDHcard, hIcard, hRcard]
  have hstabEqH : MulAction.stabilizer M a = H :=
    hstab.trans hstabO.symm
  letI : Fintype M := Fintype.ofFinite M
  letI : Fintype O := Fintype.ofFinite O
  have hOrbitMul :
      Nat.card O * Nat.card (MulAction.stabilizer M a) = Nat.card M := by
    simpa [O] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group M a)
  have hq : 2 ≤ 2 ^ f := by
    have hq' : 1 < 2 ^ f := Nat.one_lt_pow hf.ne' (by norm_num)
    omega
  have hfactorPos : 0 < 2 ^ f * (2 ^ f - 1) := by
    exact Nat.mul_pos (by omega) (by omega)
  have hOcard : Nat.card O = 2 ^ f + 1 := by
    apply Nat.eq_of_mul_eq_mul_right hfactorPos
    calc
      Nat.card O * (2 ^ f * (2 ^ f - 1)) =
          Nat.card O * Nat.card (MulAction.stabilizer M a) := by
        rw [hstabEqH, hHcard]
      _ = Nat.card M := hOrbitMul
      _ = (2 ^ f + 1) * 2 ^ f * (2 ^ f - 1) := hMcard
      _ = (2 ^ f + 1) * (2 ^ f * (2 ^ f - 1)) := by ring
  have hOthree : 3 ≤ ENat.card O := by
    rw [ENat.card_eq_coe_fintype_card]
    have hOcard' : Fintype.card O = 2 ^ f + 1 := by
      simpa only [Nat.card_eq_fintype_card] using hOcard
    rw [hOcard']
    exact_mod_cast (show 3 ≤ 2 ^ f + 1 by omega)
  have hsharpO :
      ∀ x y z x' y' z' : O,
        x ≠ y → x ≠ z → y ≠ z →
          x' ≠ y' → x' ≠ z' → y' ≠ z' →
            ∃! g : M,
              g • x = x' ∧ g • y = y' ∧ g • z = z' := by
    simpa [O] using hsharp
  have htwoO : MulAction.IsMultiplyPretransitive M O 2 := by
    rw [MulAction.is_two_pretransitive_iff]
    intro x y x' y' hxy hx'y'
    obtain ⟨z, hzx, hzy⟩ :=
      ENat.exists_ne_ne_of_three_le hOthree x y
    obtain ⟨z', hz'x', hz'y'⟩ :=
      ENat.exists_ne_ne_of_three_le hOthree x' y'
    rcases hsharpO x y z x' y' z'
        hxy hzx.symm hzy.symm hx'y' hz'x'.symm hz'y'.symm with
      ⟨g, hg, _⟩
    exact ⟨g, hg.1, hg.2.1⟩
  letI : IsMulCommutative I := hIcomm
  letI : IsMulCommutative K0 := by
    dsimp [K0]
    infer_instance
  have hKHcomm : IsMulCommutative (K0.subgroupOf H) := by
    infer_instance
  exact xi1115_sharpTriple_charTwo_pgl
    htwoO hsharpO hAtMostO aO bO habO
    (K0.subgroupOf H) hFrobH hKHcomm hf
    (hKHcard.trans hIcard) hMcard
private theorem xi1115_punctured_subgroup_card
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) :
    Nat.card {x : A // (x : G) ≠ 1} = Nat.card A - 1 := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype {x : A // (x : G) ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp

private theorem xi1115_eq_one_of_sq_eq_one_of_odd_card
    {G : Type*} [Group G] [Finite G]
    (hodd : Odd (Nat.card G)) (x : G) (hx : x ^ 2 = 1) :
    x = 1 := by
  have hordTwo : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx
  have hcop : Nat.Coprime 2 (Nat.card G) := hodd.coprime_two_left
  have hordOne : orderOf x ∣ 1 := by
    rw [← hcop.gcd_eq_one]
    exact Nat.dvd_gcd hordTwo (orderOf_dvd_natCard x)
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hordOne)

private theorem xi1115_nonsplit_count_arithmetic
    (q split nonsplit : ℕ)
    (hq : 2 ≤ q)
    (hsum : 1 + split + nonsplit = q)
    (hsplit : split * 2 = q - 2) :
    nonsplit * 2 = q := by
  omega

private theorem xi1115_not_succ_le_pred (q : ℕ) :
    ¬ q + 1 ≤ q - 1 := by
  omega

private theorem xi1115_global_count_n_le_succ
    (n q B C : ℕ)
    (hnTwo : 2 ≤ n) (hqTwo : 2 ≤ q)
    (hHalfMul : 2 * B = (n + 1) * n)
    (hAQuotMul : (2 * (q + 1)) * C = (n + 1) * n * (q - 1))
    (hCountInequality :
      n ^ 2 - 1 + B * (q - 2) + C * q ≤
        (n + 1) * n * (q - 1)) :
    n ≤ q + 1 := by
  obtain ⟨n0, rfl⟩ := Nat.exists_eq_add_of_le hnTwo
  obtain ⟨q0, rfl⟩ := Nat.exists_eq_add_of_le hqTwo
  norm_num at hHalfMul hAQuotMul hCountInequality ⊢
  have hScaled :=
    Nat.mul_le_mul_left (2 * ((2 + q0) + 1)) hCountInequality
  have hScaledLeft :
      2 * ((2 + q0) + 1) *
          ((2 + n0) ^ 2 - 1 + B * q0 + C * (2 + q0)) =
        2 * ((2 + q0) + 1) * ((2 + n0) ^ 2 - 1) +
          ((2 + q0) + 1) * (2 * B) * q0 +
          (2 * ((2 + q0) + 1) * C) * (2 + q0) := by
    ring
  rw [hScaledLeft, hHalfMul, hAQuotMul] at hScaled
  have hNSq : (2 + n0) ^ 2 - 1 = n0 ^ 2 + 4 * n0 + 3 := by
    rw [show (2 + n0) ^ 2 = n0 ^ 2 + 4 * n0 + 4 by ring]
    omega
  rw [hNSq] at hScaled
  nlinarith

private theorem xi1115_even_le_of_le_succ
    (n q : ℕ) (hnEven : Even n) (hqEven : Even q)
    (hle : n ≤ q + 1) :
    n ≤ q := by
  rcases hnEven with ⟨u, rfl⟩
  rcases hqEven with ⟨v, rfl⟩
  omega

private theorem xi1115_le_of_pred_le_pred
    (n q : ℕ) (hqTwo : 2 ≤ q) (hle : q - 1 ≤ n - 1) :
    q ≤ n := by
  omega

private theorem xi1115_descFactorial_three
    (n : ℕ) (hnTwo : 2 ≤ n) :
    (n + 1).descFactorial 3 = (n + 1) * n * (n - 1) := by
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero,
    Nat.sub_zero, mul_one]
  rw [show n + 1 - 1 = n by omega,
    show n + 1 - 2 = n - 1 by omega]
  ring

private theorem xi1115_mem_eq_one_of_coprime_card
    {G : Type*} [Group G] [Finite G]
    (A B : Subgroup G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card B))
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) :
    x = 1 := by
  have horderA : orderOf x ∣ Nat.card A := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxA⟩ : A))
  have horderB : orderOf x ∣ Nat.card B := by
    simpa [Subgroup.orderOf_coe] using
      (orderOf_dvd_natCard (⟨x, hxB⟩ : B))
  exact orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcoprime horderA horderB)

private theorem xi1115_cyclic_le_unique_partition_family
    {G : Type*} [Group G]
    (Family : Subgroup G → Prop)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G, x ∈ T ∧ Family T)
    {x : G} (hx : x ≠ 1)
    {T V : Subgroup G}
    (hxT : x ∈ T) (hTfamily : Family T)
    (hxV : x ∈ V) (hVcyclic : IsCyclic V) :
    V ≤ T := by
  letI : IsCyclic V := hVcyclic
  rcases IsCyclic.exists_zpow_surjective (G := V) with ⟨v, hv⟩
  have hvne : (v : G) ≠ 1 := by
    intro hvone
    obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
    have hnval : (v : G) ^ n = x := congrArg Subtype.val hn
    simp [hvone] at hnval
    exact hx hnval.symm
  obtain ⟨Tv, hvTv, _hTvUnique⟩ := hpartition (v : G) hvne
  have hxTv : x ∈ Tv := by
    obtain ⟨n, hn⟩ := hv ⟨x, hxV⟩
    have hnval : (v : G) ^ n = x := congrArg Subtype.val hn
    have hvpow : (v : G) ^ n ∈ Tv := Tv.zpow_mem hvTv.1 n
    rwa [hnval] at hvpow
  have hTvT : Tv = T :=
    (hpartition x hx).unique ⟨hxTv, hvTv.2⟩ ⟨hxT, hTfamily⟩
  intro y hyV
  obtain ⟨n, hn⟩ := hv ⟨y, hyV⟩
  have hnval : (v : G) ^ n = y := congrArg Subtype.val hn
  have hypow : (v : G) ^ n ∈ Tv := Tv.zpow_mem hvTv.1 n
  rw [hTvT, hnval] at hypow
  exact hypow

private theorem xi1115_cyclic_align_partition_middle
    {G : Type*} [Group G] [Finite G]
    (P U S A : Subgroup G)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G,
        x ∈ T ∧
          ((∃ g, T = P.map (MulAut.conj g).toMonoidHom) ∨
           (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
           (∃ g, T = S.map (MulAut.conj g).toMonoidHom)))
    (hAcyclic : IsCyclic A) (hAne : A ≠ ⊥)
    (hAcardU : Nat.card A = Nat.card U)
    (hAPcoprime : Nat.Coprime (Nat.card A) (Nat.card P))
    (hAScoprime : Nat.Coprime (Nat.card A) (Nat.card S)) :
    ∃ g : G, A = U.map (MulAut.conj g).toMonoidHom := by
  let Family : Subgroup G → Prop := fun T =>
    (∃ g, T = P.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
    (∃ g, T = S.map (MulAut.conj g).toMonoidHom)
  have hpartition' : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G, x ∈ T ∧ Family T := by
    simpa [Family] using hpartition
  obtain ⟨a, hane⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hAne
  have haGne : (a : G) ≠ 1 := by
    intro h
    exact hane (Subtype.ext h)
  obtain ⟨T, haT, hTfamily⟩ := (hpartition' (a : G) haGne).exists
  have hAleT : A ≤ T :=
    xi1115_cyclic_le_unique_partition_family Family hpartition'
      haGne haT hTfamily a.property hAcyclic
  rcases hTfamily with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exfalso
    have hcop : Nat.Coprime (Nat.card A)
        (Nat.card (P.map (MulAut.conj g).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hAPcoprime
    exact haGne (xi1115_mem_eq_one_of_coprime_card A
      (P.map (MulAut.conj g).toMonoidHom) hcop a.property (hAleT a.property))
  · exact ⟨g, Subgroup.eq_of_le_of_card_ge hAleT (by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
        ← hAcardU])⟩
  · exfalso
    have hcop : Nat.Coprime (Nat.card A)
        (Nat.card (S.map (MulAut.conj g).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      exact hAScoprime
    exact haGne (xi1115_mem_eq_one_of_coprime_card A
      (S.map (MulAut.conj g).toMonoidHom) hcop a.property (hAleT a.property))

private theorem xi1115_cyclic_align_partition_right
    {G : Type*} [Group G] [Finite G]
    (P U S A : Subgroup G)
    (hpartition : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G,
        x ∈ T ∧
          ((∃ g, T = P.map (MulAut.conj g).toMonoidHom) ∨
           (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
           (∃ g, T = S.map (MulAut.conj g).toMonoidHom)))
    (hAcyclic : IsCyclic A) (hAne : A ≠ ⊥)
    (hAcardS : Nat.card A = Nat.card S)
    (hAPcoprime : Nat.Coprime (Nat.card A) (Nat.card P))
    (hAUcoprime : Nat.Coprime (Nat.card A) (Nat.card U)) :
    ∃ g : G, A = S.map (MulAut.conj g).toMonoidHom := by
  have hpartitionSwap : ∀ x : G, x ≠ 1 →
      ∃! T : Subgroup G,
        x ∈ T ∧
          ((∃ g, T = P.map (MulAut.conj g).toMonoidHom) ∨
           (∃ g, T = S.map (MulAut.conj g).toMonoidHom) ∨
           (∃ g, T = U.map (MulAut.conj g).toMonoidHom)) := by
    intro x hx
    obtain ⟨T, hT, huniq⟩ := hpartition x hx
    refine ⟨T, ⟨hT.1, ?_⟩, ?_⟩
    · rcases hT.2 with hP | hU | hS
      · exact Or.inl hP
      · exact Or.inr (Or.inr hU)
      · exact Or.inr (Or.inl hS)
    · intro V hV
      apply huniq
      refine ⟨hV.1, ?_⟩
      rcases hV.2 with hP | hS | hU
      · exact Or.inl hP
      · exact Or.inr (Or.inr hS)
      · exact Or.inr (Or.inl hU)
  exact xi1115_cyclic_align_partition_middle P S U A hpartitionSwap
    hAcyclic hAne hAcardS hAPcoprime hAUcoprime

private theorem xi1115_twoPointSubgroup_fusion_inverse
    {G Omega : Type*} [Group G] [MulAction G Omega]
    (hatMostTwoFixedPoints :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (D : Subgroup G)
    (hDmem : ∀ x : G, x ∈ D ↔ x • a = a ∧ x • b = b)
    (hDcomm : IsMulCommutative D)
    (s : G) (hsa : s • a = b) (hsb : s • b = a)
    (hsInverts : ∀ x : G, x ∈ D → s * x * s⁻¹ = x⁻¹)
    (x y : G) (hxD : x ∈ D) (hyD : y ∈ D)
    (hxne : x ≠ 1) (hyne : y ≠ 1) :
    IsConj x y ↔ y = x ∨ y = x⁻¹ := by
  constructor
  · intro hxy
    rw [isConj_iff] at hxy
    rcases hxy with ⟨g, hg⟩
    have hxfix := (hDmem x).1 hxD
    have hyfix := (hDmem y).1 hyD
    have hyfixga : y • (g • a) = g • a := by
      calc
        y • (g • a) = (g * x * g⁻¹) • (g • a) := by rw [hg]
        _ = g • (x • a) := by simp only [mul_smul, inv_smul_smul]
        _ = g • a := by rw [hxfix.1]
    have hyfixgb : y • (g • b) = g • b := by
      calc
        y • (g • b) = (g * x * g⁻¹) • (g • b) := by rw [hg]
        _ = g • (x • b) := by simp only [mul_smul, inv_smul_smul]
        _ = g • b := by rw [hxfix.2]
    have hga : g • a = a ∨ g • a = b := by
      by_contra h
      rw [not_or] at h
      exact hatMostTwoFixedPoints y hyne a b (g • a)
        hab (Ne.symm h.1) (Ne.symm h.2)
        ⟨hyfix.1, hyfix.2, hyfixga⟩
    have hgb : g • b = a ∨ g • b = b := by
      by_contra h
      rw [not_or] at h
      exact hatMostTwoFixedPoints y hyne a b (g • b)
        hab (Ne.symm h.1) (Ne.symm h.2)
        ⟨hyfix.1, hyfix.2, hyfixgb⟩
    rcases hga with hgaa | hgab
    · rcases hgb with hgba | hgbb
      · exfalso
        apply hab
        exact (MulAction.toPerm g).injective (hgaa.trans hgba.symm)
      · left
        have hgD : g ∈ D := (hDmem g).2 ⟨hgaa, hgbb⟩
        letI : IsMulCommutative D := hDcomm
        have hcomm : g * x = x * g := by
          exact congrArg Subtype.val
            (mul_comm (⟨g, hgD⟩ : D) (⟨x, hxD⟩ : D))
        calc
          y = g * x * g⁻¹ := hg.symm
          _ = x := by rw [hcomm]; simp
    · rcases hgb with hgba | hgbb
      · right
        have hsinva : s⁻¹ • a = b := by
          rw [← hsb, inv_smul_smul]
        have hsinvb : s⁻¹ • b = a := by
          rw [← hsa, inv_smul_smul]
        let d : G := s⁻¹ * g
        have hdD : d ∈ D := (hDmem d).2 ⟨by
            dsimp [d]
            rw [mul_smul, hgab, hsinvb], by
            dsimp [d]
            rw [mul_smul, hgba, hsinva]⟩
        letI : IsMulCommutative D := hDcomm
        have hcomm : d * x = x * d := by
          exact congrArg Subtype.val
            (mul_comm (⟨d, hdD⟩ : D) (⟨x, hxD⟩ : D))
        have hgform : g = s * d := by
          dsimp [d]
          group
        calc
          y = g * x * g⁻¹ := hg.symm
          _ = s * (d * x * d⁻¹) * s⁻¹ := by rw [hgform]; group
          _ = s * x * s⁻¹ := by rw [hcomm]; simp
          _ = x⁻¹ := hsInverts x hxD
      · exfalso
        apply hab
        exact (MulAction.toPerm g).injective (hgab.trans hgbb.symm)
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · rw [isConj_iff]
      exact ⟨s, hsInverts _ hxD⟩

private theorem xi1115_conjClass_range_card_of_fusion_inverse
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hodd : Odd (Nat.card A))
    (hfusion : ∀ x y : G,
      x ∈ A → y ∈ A → x ≠ 1 → y ≠ 1 →
        (IsConj x y ↔ y = x ∨ y = x⁻¹)) :
    Nat.card (Set.range fun x : {x : A // (x : G) ≠ 1} =>
        ConjClasses.mk (x : G)) * 2 =
      Nat.card A - 1 := by
  classical
  let X := {x : A // (x : G) ≠ 1}
  let cls : X → ConjClasses G := fun x => ConjClasses.mk (x : G)
  let clsRange : X → Set.range cls := Set.rangeFactorization cls
  have hfiber (y : Set.range cls) :
      Nat.card {x : X // clsRange x = y} = 2 := by
    rcases y.property with ⟨x, hx⟩
    let xinv : X := ⟨x.1⁻¹, by simpa using x.2⟩
    have hclsInv : cls xinv = cls x := by
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      apply (hfusion (xinv : G) (x : G)
        xinv.1.property x.1.property xinv.2 x.2).mpr
      right
      simp [xinv]
    let u : {z : X // clsRange z = y} := ⟨x, by
      apply Subtype.ext
      exact hx⟩
    let v : {z : X // clsRange z = y} := ⟨xinv, by
      apply Subtype.ext
      exact hclsInv.trans hx⟩
    have huv : u ≠ v := by
      intro huv
      have hxinv : x.1 = x.1⁻¹ := by
        exact congrArg (fun z : {z : X // clsRange z = y} => z.1.1) huv
      have hxsq : x.1 ^ 2 = 1 := by
        simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp hxinv)
      have hxone : x.1 = 1 :=
        xi1115_eq_one_of_sq_eq_one_of_odd_card hodd x.1 hxsq
      exact x.2 (congrArg Subtype.val hxone)
    apply (Nat.card_eq_two_iff).2
    refine ⟨u, v, huv, ?_⟩
    ext z
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    have hzcls : cls z.1 = cls x := by
      exact congrArg Subtype.val z.2 |>.trans hx.symm
    have hzconj : IsConj (z.1 : G) (x : G) :=
      ConjClasses.mk_eq_mk_iff_isConj.mp (by simpa [cls] using hzcls)
    rcases (hfusion (z.1 : G) (x : G)
        z.1.1.property x.1.property z.1.2 x.2).mp hzconj with
      hzx | hzx
    · left
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      exact hzx.symm
    · right
      apply Subtype.ext
      apply Subtype.ext
      apply Subtype.ext
      change (z.1.1 : G) = ((x.1⁻¹ : A) : G)
      have := congrArg Inv.inv hzx
      simpa [xinv] using this.symm
  letI : Fintype (Set.range cls) := Fintype.ofFinite _
  letI (y : Set.range cls) : Fintype {x : X // clsRange x = y} :=
    Fintype.ofFinite _
  have hcardSigma :
      Nat.card (Σ y : Set.range cls, {x : X // clsRange x = y}) =
        Nat.card X :=
    Nat.card_congr (Equiv.sigmaFiberEquiv clsRange)
  rw [Nat.card_sigma] at hcardSigma
  simp_rw [hfiber] at hcardSigma
  rw [Finset.sum_const, Finset.card_univ] at hcardSigma
  have hcardSigma' : Nat.card (Set.range cls) * 2 = Nat.card X := by
    simpa only [Nat.card_eq_fintype_card, nsmul_eq_mul, Nat.cast_id] using hcardSigma
  simpa [X, cls] using hcardSigma'.trans
    (xi1115_punctured_subgroup_card A)

private theorem xi1115_fusion_inverse_of_conjClass_range_card
    {G : Type*} [Group G] [Finite G]
    (A : Subgroup G) (hodd : Odd (Nat.card A))
    (w : G)
    (hwinv : ∀ x : G, x ∈ A → w * x * w⁻¹ = x⁻¹)
    (hcard :
      Nat.card (Set.range fun x : {x : A // (x : G) ≠ 1} =>
          ConjClasses.mk (x : G)) * 2 =
        Nat.card A - 1) :
    ∀ x y : G,
      x ∈ A → y ∈ A → x ≠ 1 → y ≠ 1 →
        (IsConj x y ↔ y = x ∨ y = x⁻¹) := by
  classical
  let X := {x : A // (x : G) ≠ 1}
  let cls : X → ConjClasses G := fun x => ConjClasses.mk (x : G)
  let clsRange : X → Set.range cls := Set.rangeFactorization cls
  let invX : X → X := fun x => ⟨x.1⁻¹, by simpa using x.2⟩
  have hinvX_ne (x : X) : x ≠ invX x := by
    intro hx
    have hxinv : x.1 = x.1⁻¹ :=
      congrArg (fun z : X => z.1) hx
    have hxsq : x.1 ^ 2 = 1 := by
      simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp hxinv)
    have hxone : x.1 = 1 :=
      xi1115_eq_one_of_sq_eq_one_of_odd_card hodd x.1 hxsq
    exact x.2 (congrArg Subtype.val hxone)
  have hclsInv (x : X) : cls (invX x) = cls x := by
    apply ConjClasses.mk_eq_mk_iff_isConj.mpr
    have hconj : IsConj (x : G) ((invX x : X) : G) := by
      rw [isConj_iff]
      exact ⟨w, by simpa [invX] using hwinv (x : G) x.1.property⟩
    exact hconj.symm
  let rep : Set.range cls → X := fun c => Classical.choose c.2
  have hrep (c : Set.range cls) : cls (rep c) = c :=
    Classical.choose_spec c.2
  let pair : Set.range cls × Bool → X := fun z =>
    if z.2 then invX (rep z.1) else rep z.1
  have hpairClass (z : Set.range cls × Bool) :
      cls (pair z) = z.1 := by
    rcases z with ⟨c, b⟩
    cases b <;> simp [pair, hrep, hclsInv]
  have hpairInjective : Function.Injective pair := by
    rintro ⟨c, b⟩ ⟨d, e⟩ hpair
    have hcd : c = d := by
      apply Subtype.ext
      calc
        (c : ConjClasses G) = cls (pair (c, b)) :=
          (hpairClass (c, b)).symm
        _ = cls (pair (d, e)) := congrArg cls hpair
        _ = (d : ConjClasses G) := hpairClass (d, e)
    subst d
    cases b <;> cases e
    · rfl
    · exact False.elim
        (hinvX_ne (rep c) (by simpa [pair] using hpair))
    · exact False.elim
        (hinvX_ne (rep c) (by simpa [pair] using hpair.symm))
    · rfl
  have hpairCard :
      Nat.card (Set.range cls × Bool) = Nat.card X := by
    rw [Nat.card_prod]
    have hXcard := xi1115_punctured_subgroup_card A
    change
      Nat.card (Set.range fun x : {x : A // (x : G) ≠ 1} =>
          ConjClasses.mk (x : G)) * Nat.card Bool =
        Nat.card {x : A // (x : G) ≠ 1}
    simpa using hcard.trans hXcard.symm
  have hpairBijective : Function.Bijective pair :=
    (Nat.bijective_iff_injective_and_card pair).2
      ⟨hpairInjective, hpairCard⟩
  have hdecomp (x : X) :
      x = rep (clsRange x) ∨ x = invX (rep (clsRange x)) := by
    obtain ⟨z, hz⟩ := hpairBijective.2 x
    rcases z with ⟨c, b⟩
    have hc : c = clsRange x := by
      apply Subtype.ext
      calc
        (c : ConjClasses G) = cls (pair (c, b)) :=
          (hpairClass (c, b)).symm
        _ = cls x := congrArg cls hz
        _ = (clsRange x : ConjClasses G) := rfl
    subst c
    cases b
    · left
      simpa [pair] using hz.symm
    · right
      simpa [pair] using hz.symm
  intro x y hxA hyA hxne hyne
  constructor
  · intro hxy
    let xX : X := ⟨⟨x, hxA⟩, hxne⟩
    let yX : X := ⟨⟨y, hyA⟩, hyne⟩
    have hclsEq : cls xX = cls yX := by
      exact ConjClasses.mk_eq_mk_iff_isConj.mpr hxy
    have hRangeEq : clsRange xX = clsRange yX := by
      apply Subtype.ext
      exact hclsEq
    have hxCases := hdecomp xX
    have hyCases := hdecomp yX
    rw [← hRangeEq] at hyCases
    rcases hxCases with hxRep | hxInv
    · rcases hyCases with hyRep | hyInv
      · left
        simpa [xX, yX] using
          congrArg (fun z : X => (z : G)) (hyRep.trans hxRep.symm)
      · right
        calc
          y = ((yX : X) : G) := rfl
          _ = ((invX (rep (clsRange xX)) : X) : G) :=
            congrArg (fun z : X => (z : G)) hyInv
          _ = ((rep (clsRange xX) : X) : G)⁻¹ := rfl
          _ = ((xX : X) : G)⁻¹ := by
            exact (congrArg Inv.inv
              (congrArg (fun z : X => (z : G)) hxRep)).symm
          _ = x⁻¹ := rfl
    · rcases hyCases with hyRep | hyInv
      · right
        calc
          y = ((yX : X) : G) := rfl
          _ = ((rep (clsRange xX) : X) : G) :=
            congrArg (fun z : X => (z : G)) hyRep
          _ = ((invX (rep (clsRange xX)) : X) : G)⁻¹ := by
            simp [invX]
          _ = ((xX : X) : G)⁻¹ := by
            exact (congrArg Inv.inv
              (congrArg (fun z : X => (z : G)) hxInv)).symm
          _ = x⁻¹ := rfl
      · left
        simpa [xX, yX] using
          congrArg (fun z : X => (z : G)) (hyInv.trans hxInv.symm)
  · rintro (rfl | rfl)
    · exact IsConj.refl _
    · rw [isConj_iff]
      exact ⟨w, hwinv x hxA⟩

private theorem xi1115_conjugacy_orbit_card
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) :
    Nat.card {W : Subgroup G // ∃ g : G,
      W = A.map (MulAut.conj g).toMonoidHom} =
      (Subgroup.normalizer (A : Set G)).index := by
  classical
  letI : MulAction G (Subgroup G) := MulAction.compHom _ MulAut.conj
  have horbit :
      MulAction.orbit G A =
        {W : Subgroup G | ∃ g : G,
          W = A.map (MulAut.conj g).toMonoidHom} := by
    ext W
    constructor
    · intro hW
      rcases hW with ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  have hstab : MulAction.stabilizer G A =
      Subgroup.normalizer (A : Set G) := by
    ext g
    change g • A = A ↔ g ∈ Subgroup.normalizer (A : Set G)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer A),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact
      forall_congr' fun h =>
        iff_congr Iff.rfl
          ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
            fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
              MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  change Nat.card ↥{W : Subgroup G | ∃ g : G,
    W = A.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer G A, hstab]

private theorem xi1115_conjugate_family_punctured_card
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) :
    Nat.card (Σ W : {W : Subgroup G // ∃ g : G,
        W = A.map (MulAut.conj g).toMonoidHom},
      {x : (W.1 : Subgroup G) // (x : G) ≠ 1}) =
      (Subgroup.normalizer (A : Set G)).index * (Nat.card A - 1) := by
  classical
  let Family := {W : Subgroup G // ∃ g : G,
    W = A.map (MulAut.conj g).toMonoidHom}
  have hWcard (W : Family) : Nat.card W.1 = Nat.card A := by
    rcases W.2 with ⟨g, hg⟩
    rw [hg]
    exact Nat.card_congr ((MulAut.conj g).subgroupMap A).toEquiv.symm
  letI : Fintype Family := Fintype.ofFinite _
  letI (W : Family) : Fintype {x : W.1 // (x : G) ≠ 1} :=
    Fintype.ofFinite _
  change Nat.card (Σ W : Family, {x : W.1 // (x : G) ≠ 1}) = _
  rw [Nat.card_sigma]
  simp_rw [xi1115_punctured_subgroup_card, hWcard]
  rw [Finset.sum_const, Finset.card_univ]
  change Fintype.card Family * (Nat.card A - 1) = _
  rw [← Nat.card_eq_fintype_card, xi1115_conjugacy_orbit_card]

private theorem xi1115_conjugates_disjoint_of_TI
    {G : Type*} [Group G] (A : Subgroup G)
    (hTI : ∀ k : G, k ∉ Subgroup.normalizer (A : Set G) →
      Disjoint A (A.map (MulAut.conj k).toMonoidHom))
    (g h : G)
    (hne : A.map (MulAut.conj g).toMonoidHom ≠
      A.map (MulAut.conj h).toMonoidHom) :
    Disjoint (A.map (MulAut.conj g).toMonoidHom)
      (A.map (MulAut.conj h).toMonoidHom) := by
  let k := g⁻¹ * h
  have hknot : k ∉ Subgroup.normalizer (A : Set G) := by
    intro hknorm
    apply hne
    ext x
    constructor
    · rintro ⟨a, haA, hax⟩
      let b := k⁻¹ * a * k
      have hbA : b ∈ A := by
        apply (Subgroup.mem_normalizer_iff.mp hknorm b).mpr
        have hconj : k * b * k⁻¹ = a := by
          dsimp [b]
          group
        rw [hconj]
        exact haA
      refine ⟨b, hbA, ?_⟩
      change h * b * h⁻¹ = x
      rw [← hax]
      dsimp [b, k]
      group
    · rintro ⟨b, hbA, hbx⟩
      let a := k * b * k⁻¹
      have haA : a ∈ A :=
        (Subgroup.mem_normalizer_iff.mp hknorm b).mp hbA
      refine ⟨a, haA, ?_⟩
      change g * a * g⁻¹ = x
      rw [← hbx]
      dsimp [a, k]
      group
  rw [Subgroup.disjoint_def]
  intro x hxg hxh
  rcases hxg with ⟨a, haA, hax⟩
  rcases hxh with ⟨b, hbA, hbx⟩
  let y := g⁻¹ * x * g
  have hax' : g * a * g⁻¹ = x := by simpa using hax
  have hbx' : h * b * h⁻¹ = x := by simpa using hbx
  have hyA : y ∈ A := by
    have hy : y = a := by
      dsimp [y]
      rw [← hax']
      group
    rw [hy]
    exact haA
  have hyAk : y ∈ A.map (MulAut.conj k).toMonoidHom := by
    refine ⟨b, hbA, ?_⟩
    change k * b * k⁻¹ = y
    dsimp [k, y]
    rw [← hbx']
    group
  have hyOne : y = 1 :=
    Subgroup.mem_bot.mp (Subgroup.disjoint_def.mp (hTI k hknot) hyA hyAk)
  calc
    x = g * y * g⁻¹ := by dsimp [y]; group
    _ = 1 := by rw [hyOne]; simp
private theorem xi1115_disjoint_conjugate_families_card_le
    {G : Type*} [Group G] [Finite G] {r : ℕ}
    (A : Fin r → Subgroup G)
    (hdecode : Function.Injective
      (fun z : Σ i : Fin r,
          Σ W : {W : Subgroup G // ∃ g : G,
            W = (A i).map (MulAut.conj g).toMonoidHom},
            {x : (W.1 : Subgroup G) // (x : G) ≠ 1} =>
        (z.2.2.1 : G))) :
    (∑ i, (Subgroup.normalizer (A i : Set G)).index *
      (Nat.card (A i) - 1)) ≤ Nat.card G := by
  classical
  let Piece := Σ i : Fin r,
    Σ W : {W : Subgroup G // ∃ g : G,
      W = (A i).map (MulAut.conj g).toMonoidHom},
      {x : (W.1 : Subgroup G) // (x : G) ≠ 1}
  have hPieceCard :
      Nat.card Piece =
        ∑ i, (Subgroup.normalizer (A i : Set G)).index *
          (Nat.card (A i) - 1) := by
    letI (i : Fin r) : Fintype {W : Subgroup G // ∃ g : G,
        W = (A i).map (MulAut.conj g).toMonoidHom} :=
      Fintype.ofFinite _
    letI (i : Fin r)
        (W : {W : Subgroup G // ∃ g : G,
          W = (A i).map (MulAut.conj g).toMonoidHom}) :
        Fintype {x : W.1 // (x : G) ≠ 1} :=
      Fintype.ofFinite _
    change Nat.card (Σ i : Fin r,
      Σ W : {W : Subgroup G // ∃ g : G,
        W = (A i).map (MulAut.conj g).toMonoidHom},
        {x : W.1 // (x : G) ≠ 1}) = _
    rw [Nat.card_sigma]
    simp_rw [xi1115_conjugate_family_punctured_card]
  rw [← hPieceCard]
  exact Nat.card_le_card_of_injective _ hdecode
private theorem xi1115_disjoint_conjugate_families_card_le_of_TI
    {G : Type*} [Group G] [Finite G] {r : ℕ}
    (A : Fin r → Subgroup G)
    (hTI : ∀ i, ∀ k : G,
      k ∉ Subgroup.normalizer (A i : Set G) →
        Disjoint (A i) ((A i).map (MulAut.conj k).toMonoidHom))
    (hcross : ∀ i j, i ≠ j → ∀ g h : G,
      Disjoint ((A i).map (MulAut.conj g).toMonoidHom)
        ((A j).map (MulAut.conj h).toMonoidHom)) :
    (∑ i, (Subgroup.normalizer (A i : Set G)).index *
      (Nat.card (A i) - 1)) ≤ Nat.card G := by
  apply xi1115_disjoint_conjugate_families_card_le A
  intro z w hzw
  rcases z with ⟨i, W, x⟩
  rcases w with ⟨j, V, y⟩
  have hxy : (x : G) = (y : G) := hzw
  by_cases hij : i = j
  · subst j
    have hWVsub : W.1 = V.1 := by
      by_contra hne
      rcases W.2 with ⟨g, hg⟩
      rcases V.2 with ⟨h, hh⟩
      have hdisj := xi1115_conjugates_disjoint_of_TI
        (A i) (hTI i) g h (by simpa [hg, hh] using hne)
      have hxV : (x : G) ∈ V.1 := by
        rw [hxy]
        exact y.1.property
      have hxOne : (x : G) = 1 :=
        Subgroup.disjoint_def.mp (by simpa [hg, hh] using hdisj)
          x.1.property hxV
      exact x.2 hxOne
    have hWV : W = V := Subtype.ext hWVsub
    subst V
    have hxy' : x = y := by
      apply Subtype.ext
      apply Subtype.ext
      exact hxy
    subst y
    rfl
  · rcases W.2 with ⟨g, hg⟩
    rcases V.2 with ⟨h, hh⟩
    have hdisj := hcross i j hij g h
    have hxV : (x : G) ∈ V.1 := by
      rw [hxy]
      exact y.1.property
    have hxOne : (x : G) = 1 :=
      Subgroup.disjoint_def.mp (by simpa [hg, hh] using hdisj)
        x.1.property hxV
    exact False.elim (x.2 hxOne)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_pgl_charTwo_threeFamilyPartition
    {M K : Type u} [Group M] [Finite M] [Field K] [Finite K]
    {l : ℕ} (hl : 0 < l) (hKcard : Nat.card K = 2 ^ l)
    (eM : M ≃* Matrix.ProjGenLinGroup (Fin 2) K) :
    ∃ P U S : Subgroup M,
      IsPGroup 2 P ∧
      Nat.card P = 2 ^ l ∧
      IsCyclic U ∧ Nat.card U = 2 ^ l - 1 ∧
      IsCyclic S ∧ Nat.card S = 2 ^ l + 1 ∧
      ∀ x : M, x ≠ 1 →
        ∃! T : Subgroup M,
          x ∈ T ∧
            ((∃ g, T = P.map (MulAut.conj g).toMonoidHom) ∨
             (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
             (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by
  obtain ⟨eP⟩ := xi1115_charTwo_pslEquivPgl hKcard
  let e : PSL2MatrixGroup K ≃* M := eP.trans eM.symm
  let P0 : Sylow 2 (PSL2MatrixGroup K) := default
  obtain ⟨U0, S0, hU0cyclic, hU0cardRaw,
      hS0cyclic, hS0cardRaw, hpartition0⟩ :=
    huppert_II_8_5_a_psl2_partition
      (p := 2) (f := l) hKcard P0
  let P1 : Subgroup M := (P0 : Subgroup (PSL2MatrixGroup K)).map e.toMonoidHom
  let U1 : Subgroup M := U0.map e.toMonoidHom
  let S1 : Subgroup M := S0.map e.toMonoidHom
  have hqEven : Even (2 ^ l) :=
    Nat.even_pow.mpr ⟨even_two, hl.ne'⟩
  have hqSubOdd : Odd (2 ^ l - 1) :=
    Nat.Even.sub_odd (pow_pos (by norm_num : 0 < (2 : ℕ)) l)
      hqEven odd_one
  have hgcd : Nat.gcd (2 ^ l - 1) 2 = 1 :=
    Nat.coprime_iff_gcd_eq_one.mp hqSubOdd.coprime_two_right
  have hU0card : Nat.card U0 = 2 ^ l - 1 := by
    simpa [hKcard, hgcd] using hU0cardRaw
  have hS0card : Nat.card S0 = 2 ^ l + 1 := by
    simpa [hKcard, hgcd] using hS0cardRaw
  have hP1 : IsPGroup 2 P1 := by
    exact P0.isPGroup'.map e.toMonoidHom
  have hP0card :
      Nat.card (P0 : Subgroup (PSL2MatrixGroup K)) = 2 ^ l := by
    obtain ⟨eP0⟩ :=
      huppert_II_8_2_a_sylow_equiv_additive hKcard P0
    exact (Nat.card_congr eP0.toEquiv).symm.trans hKcard
  have hP1card : Nat.card P1 = 2 ^ l := by
    calc
      Nat.card P1 = Nat.card (P0 : Subgroup (PSL2MatrixGroup K)) :=
        Subgroup.card_map_of_injective e.injective
      _ = 2 ^ l := hP0card
  have hU1cyclic : IsCyclic U1 := by
    let eU := e.subgroupMap U0
    letI : IsCyclic U0 := hU0cyclic
    exact isCyclic_of_surjective eU.toMonoidHom eU.surjective
  have hS1cyclic : IsCyclic S1 := by
    let eS := e.subgroupMap S0
    letI : IsCyclic S0 := hS0cyclic
    exact isCyclic_of_surjective eS.toMonoidHom eS.surjective
  have hU1card : Nat.card U1 = 2 ^ l - 1 := by
    calc
      Nat.card U1 = Nat.card U0 :=
        Subgroup.card_map_of_injective e.injective
      _ = 2 ^ l - 1 := hU0card
  have hS1card : Nat.card S1 = 2 ^ l + 1 := by
    calc
      Nat.card S1 = Nat.card S0 :=
        Subgroup.card_map_of_injective e.injective
      _ = 2 ^ l + 1 := hS0card
  have hmapConj (R : Subgroup (PSL2MatrixGroup K))
      (g : PSL2MatrixGroup K) :
      (R.map (MulAut.conj g).toMonoidHom).map e.toMonoidHom =
        (R.map e.toMonoidHom).map
          (MulAut.conj (e g)).toMonoidHom := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hmapBack (R : Subgroup M) :
      (R.map e.symm.toMonoidHom).map e.toMonoidHom = R := by
    rw [Subgroup.map_map]
    have heq : e.toMonoidHom.comp e.symm.toMonoidHom =
        MonoidHom.id M := by
      ext x
      simp
    rw [heq, Subgroup.map_id]
  have hfamilyBack (V : Subgroup M)
      (hV :
        (∃ g, V = P1.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, V = U1.map (MulAut.conj g).toMonoidHom) ∨
        (∃ g, V = S1.map (MulAut.conj g).toMonoidHom)) :
      (∃ g, V.map e.symm.toMonoidHom =
          (P0 : Subgroup (PSL2MatrixGroup K)).map
            (MulAut.conj g).toMonoidHom) ∨
      (∃ g, V.map e.symm.toMonoidHom =
          U0.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, V.map e.symm.toMonoidHom =
          S0.map (MulAut.conj g).toMonoidHom) := by
    rcases hV with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
    · left
      refine ⟨e.symm g, ?_⟩
      apply Subgroup.ext
      intro x
      simp [P1]
    · right
      left
      refine ⟨e.symm g, ?_⟩
      apply Subgroup.ext
      intro x
      simp [U1]
    · right
      right
      refine ⟨e.symm g, ?_⟩
      apply Subgroup.ext
      intro x
      simp [S1]
  refine ⟨P1, U1, S1, hP1, hP1card, hU1cyclic, hU1card,
    hS1cyclic, hS1card, ?_⟩
  intro x hx
  have hx0 : e.symm x ≠ 1 := by
    intro h
    apply hx
    simpa using congrArg e h
  obtain ⟨T0, hT0, hT0unique⟩ :=
    hpartition0 (e.symm x) hx0
  let T : Subgroup M := T0.map e.toMonoidHom
  have hxT : x ∈ T := by
    have : e (e.symm x) ∈ T :=
      Subgroup.mem_map_of_mem e.toMonoidHom hT0.1
    simpa using this
  have hTfamily :
      (∃ g, T = P1.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, T = U1.map (MulAut.conj g).toMonoidHom) ∨
      (∃ g, T = S1.map (MulAut.conj g).toMonoidHom) := by
    rcases hT0.2 with ⟨g, rfl⟩ | ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact Or.inl ⟨e g, hmapConj _ g⟩
    · exact Or.inr (Or.inl ⟨e g, hmapConj _ g⟩)
    · exact Or.inr (Or.inr ⟨e g, hmapConj _ g⟩)
  refine ⟨T, ⟨hxT, hTfamily⟩, ?_⟩
  intro V hV
  let V0 : Subgroup (PSL2MatrixGroup K) :=
    V.map e.symm.toMonoidHom
  have hxV0 : e.symm x ∈ V0 := by
    exact Subgroup.mem_map_of_mem e.symm.toMonoidHom hV.1
  have hV0family := hfamilyBack V hV.2
  have hV0eq : V0 = T0 :=
    hT0unique V0 ⟨hxV0, hV0family⟩
  calc
    V = V0.map e.toMonoidHom := (hmapBack V).symm
    _ = T0.map e.toMonoidHom := by rw [hV0eq]
    _ = T := rfl
/-- A finite Frobenius complement contains at most one involution.  Both
involutions would act as inversion on the kernel, and the conjugation action
of the complement on the nontrivial kernel is faithful. -/
private theorem xi1115_frobenius_complement_involutions_eq
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H)
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (t u : D) (htorder : orderOf t = 2) (huorder : orderOf u = 2) :
    t = u := by
  letI : F.Normal := hFrob.normal
  have hconjInv : ∀ r : D, orderOf r = 2 → ∀ x : F,
      (r : H) * (x : H) * (r : H)⁻¹ = (x⁻¹ : F) := by
    intro r hrorder x
    have hrne : r ≠ 1 := by
      intro hr
      subst r
      simp at hrorder
    have hrsqD : r ^ 2 = 1 := by
      rw [← hrorder]
      exact pow_orderOf_eq_one r
    have hrsqH : (r : H) ^ 2 = 1 := by
      simpa using congrArg Subtype.val hrsqD
    let phi : MulAut F := MulAut.conjNormal (H := F) (r : H)
    have hphi_sq : phi ^ 2 = 1 := by
      change (MulAut.conjNormal (H := F) (r : H)) ^ 2 = 1
      rw [← map_pow, hrsqH, map_one]
    have hphi_involutive : Function.Involutive phi := by
      intro y
      have hy := congrArg (fun psi : MulAut F => psi y) hphi_sq
      simpa [pow_two] using hy
    have hphi_fixedPointFree : MonoidHom.FixedPointFree phi := by
      intro y hy
      have hyconj :
          (r : H) * (y : H) * (r : H)⁻¹ = (y : H) := by
        simpa [phi] using congrArg Subtype.val hy
      have hycomm : (r : H) * (y : H) = (y : H) * (r : H) := by
        have := congrArg (fun z : H => z * (r : H)) hyconj
        simpa [mul_assoc] using this
      have hycent : (y : H) ∈ elementCentralizerIn F (r : H) :=
        ⟨y.property, Subgroup.mem_centralizer_singleton_iff.mpr hycomm.symm⟩
      have hcent : elementCentralizerIn F (r : H) = ⊥ :=
        (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
          hFrob.normal hFrob.isComplement').mp hFrob r hrne
      have hybot : (y : H) ∈ (⊥ : Subgroup H) := by
        simpa [hcent] using hycent
      exact Subtype.ext (by simpa using hybot)
    have hinv := hphi_fixedPointFree.coe_eq_inv_of_involutive hphi_involutive
    simpa [phi] using congrArg Subtype.val (congrFun hinv x)
  have htInv := hconjInv t htorder
  have huInv := hconjInv u huorder
  let v : D := t⁻¹ * u
  by_contra htu
  have hvne : v ≠ 1 := by
    intro hv
    apply htu
    have := congrArg (fun z : D => t * z) hv
    simpa [v, mul_assoc] using this.symm
  obtain ⟨x, hx⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.kernel_ne_bot
  have hvcomm : (v : H) * (x : H) = (x : H) * (v : H) := by
    have ht := htInv x
    have hu := huInv x
    have ht' : (t : H) * (x : H) * (t : H)⁻¹ = (x : H)⁻¹ := by
      simpa using ht
    have hu' : (u : H) * (x : H) * (u : H)⁻¹ = (x : H)⁻¹ := by
      simpa using hu
    have huMove : (u : H) * (x : H) = (x : H)⁻¹ * (u : H) := by
      calc
        (u : H) * (x : H) =
            ((u : H) * (x : H) * (u : H)⁻¹) * (u : H) := by group
        _ = (x : H)⁻¹ * (u : H) := by rw [hu']
    have htMove : (t : H)⁻¹ * (x : H)⁻¹ =
        (x : H) * (t : H)⁻¹ := by
      calc
        (t : H)⁻¹ * (x : H)⁻¹ =
            (t : H)⁻¹ * ((t : H) * (x : H) * (t : H)⁻¹) := by rw [ht']
        _ = (x : H) * (t : H)⁻¹ := by group
    change ((t : H)⁻¹ * (u : H)) * (x : H) =
      (x : H) * ((t : H)⁻¹ * (u : H))
    calc
      ((t : H)⁻¹ * (u : H)) * (x : H) =
          (t : H)⁻¹ * ((x : H)⁻¹ * (u : H)) := by
            rw [mul_assoc, huMove]
      _ = (x : H) * ((t : H)⁻¹ * (u : H)) := by
            rw [← mul_assoc, htMove, mul_assoc]
  have hxcent : (x : H) ∈ elementCentralizerIn F (v : H) :=
    ⟨x.property, Subgroup.mem_centralizer_singleton_iff.mpr hvcomm.symm⟩
  have hcent : elementCentralizerIn F (v : H) = ⊥ :=
    (lemma_3_1 F D hFrob.kernel_ne_bot hFrob.complement_ne_bot
      hFrob.normal hFrob.isComplement').mp hFrob v hvne
  have hxbot : (x : H) ∈ (⊥ : Subgroup H) := by
    simpa [hcent] using hxcent
  apply hx
  apply Subtype.ext
  simpa using hxbot

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_global_class_count_tail
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (f : ℕ) (hf : 0 < f)
    (n : ℕ) (hdegree : Fintype.card Omega = n + 1)
    (hFcardN : Nat.card F = n) (hnPower : n = 2 ^ f)
    (hnEven : Even n)
    (hDodd : Odd (Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a))))
    (hDdiv : Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) ∣
      Nat.card F - 1)
    (l : ℕ) (hl : 0 < l)
    (hDcard : Nat.card
        (MulAction.stabilizer (MulAction.stabilizer G a)
          (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)) =
      2 ^ l - 1)
    (Dg : Subgroup G)
    (hDgCard : Nat.card Dg = Nat.card
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hDgNormalizerRelIndex :
      Dg.relIndex (Subgroup.normalizer (Dg : Set G)) = 2)
    (hDgCentralizer : ∀ x : G, x ∈ Dg → x ≠ 1 →
      Subgroup.centralizer ({x} : Set G) = Dg)
    (A : Subgroup G) (hAcard : Nat.card A = 2 ^ l + 1)
    (hANormalizerCard :
      Nat.card (Subgroup.normalizer (A : Set G)) = 2 * (2 ^ l + 1))
    (hATI : ∀ k : G, k ∉ Subgroup.normalizer (A : Set G) →
      Disjoint A (A.map (MulAut.conj k).toMonoidHom)) :
    ∀ x y z x' y' z' : Omega,
      x ≠ y → x ≠ z → y ≠ z →
      x' ≠ y' → x' ≠ z' → y' ≠ z' →
        ∃! g : G,
          g • x = x' ∧ g • y = y' ∧ g • z = z' := by
  let H0 := MulAction.stabilizer G a
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer H0 b'
  change IsFrobeniusGroupWithKernelComplement F D at hFrob
  have hFrobD : IsFrobeniusGroupWithKernelComplement F D := hFrob
  letI : F.Normal := hFrob.normal
  let Fg : Subgroup G := F.map H0.subtype
  have hFgData :
      Nat.card Fg = n ∧
      (Subgroup.normalizer (Fg : Set G)).index = n + 1 ∧
      (∀ k : G, k ∉ Subgroup.normalizer (Fg : Set G) →
        Disjoint Fg (Fg.map (MulAut.conj k).toMonoidHom)) := by
    have hFgCard : Nat.card Fg = n := by
      calc
        Nat.card Fg = Nat.card F := by
          exact Subgroup.card_map_of_injective H0.subtype_injective
        _ = n := hFcardN
    have hFgNormalizer :
        Subgroup.normalizer (Fg : Set G) = H0 := by
      apply le_antisymm
      · intro g hg
        obtain ⟨z, hzne⟩ :=
          Subgroup.ne_bot_iff_exists_ne_one.mp hFrob.kernel_ne_bot
        let zG : G := ((z : F) : H0)
        have hzFg : zG ∈ Fg := ⟨(z : H0), z.property, rfl⟩
        have hginv : g⁻¹ ∈ Subgroup.normalizer (Fg : Set G) :=
          (Subgroup.normalizer (Fg : Set G)).inv_mem hg
        have hzConj : g⁻¹ * zG * g ∈ Fg := by
          have h :=
            (Subgroup.mem_normalizer_iff.mp hginv zG).mp hzFg
          simpa [zG] using h
        rcases hzConj with ⟨z0, hz0F, hz0eq⟩
        have hconjFix : (g⁻¹ * zG * g) • a = a := by
          rw [← hz0eq]
          exact z0.property
        have hzFixGa : zG • (g • a) = g • a := by
          calc
            zG • (g • a) = (zG * g) • a := by rw [mul_smul]
            _ = (g * (g⁻¹ * zG * g)) • a := by
              congr 1
              group
            _ = g • ((g⁻¹ * zG * g) • a) := by rw [mul_smul]
            _ = g • a := by rw [hconjFix]
        have hga : g • a = a :=
          (xi1115_frobeniusKernel_uniqueFixedPoint
            htwo_transitive a b hab F hFrob z hzne (g • a)).mp
              (by simpa [zG] using hzFixGa)
        simpa [H0] using hga
      · intro g hg
        let g0 : H0 := ⟨g, hg⟩
        have hg0norm : g0 ∈ Subgroup.normalizer (F : Set H0) := by
          rw [Subgroup.normalizer_eq_top F]
          exact Subgroup.mem_top g0
        exact (Subgroup.le_normalizer_map H0.subtype)
          ⟨g0, hg0norm, rfl⟩
    have hFgNormalizerIndex :
        (Subgroup.normalizer (Fg : Set G)).index = n + 1 := by
      rw [hFgNormalizer]
      letI : MulAction.IsMultiplyPretransitive G Omega 2 :=
        htwo_transitive
      letI : MulAction.IsPretransitive G Omega :=
        MulAction.isPretransitive_of_is_two_pretransitive
      calc
        H0.index = Fintype.card Omega := by
          simpa [H0, Nat.card_eq_fintype_card] using
            (MulAction.index_stabilizer_of_transitive G a)
        _ = n + 1 := hdegree
    have hFgTI : ∀ k : G,
        k ∉ Subgroup.normalizer (Fg : Set G) →
          Disjoint Fg (Fg.map (MulAut.conj k).toMonoidHom) := by
      intro k hk
      rw [Subgroup.disjoint_def]
      intro z hzFg hzConj
      rcases hzFg with ⟨z0, hz0F, hz0eq⟩
      let zF : F := ⟨z0, hz0F⟩
      by_contra hzOne
      have hzFne : zF ≠ 1 := by
        intro hzFone
        apply hzOne
        calc
          z = (z0 : G) := hz0eq.symm
          _ = 1 := by
            simpa [zF] using congrArg
              (fun q : F => (((q : F) : H0) : G)) hzFone
      rcases hzConj with ⟨x, hxFg, hxz⟩
      rcases hxFg with ⟨x0, hx0F, hx0eq⟩
      have hxFix : x • a = a := by
        rw [← hx0eq]
        exact x0.property
      change k * x * k⁻¹ = z at hxz
      have hzFixKa : z • (k • a) = k • a := by
        rw [← hxz]
        calc
          (k * x * k⁻¹) • (k • a) = k • (x • a) := by
            simp only [mul_smul, inv_smul_smul]
          _ = k • a := by rw [hxFix]
      have hzFixKa' := hzFixKa
      rw [← hz0eq] at hzFixKa'
      have hka : k • a = a :=
        (xi1115_frobeniusKernel_uniqueFixedPoint
          htwo_transitive a b hab F hFrob zF hzFne (k • a)).mp
            (by simpa [zF] using hzFixKa')
      apply hk
      rw [hFgNormalizer]
      simpa [H0] using hka
    exact ⟨hFgCard, hFgNormalizerIndex, hFgTI⟩
  have hDgData :
      Nat.card Dg = 2 ^ l - 1 ∧
      (Subgroup.normalizer (Dg : Set G)).index = (n + 1) * n / 2 ∧
      (∀ k : G, k ∉ Subgroup.normalizer (Dg : Set G) →
        Disjoint Dg (Dg.map (MulAut.conj k).toMonoidHom)) := by
    have hDgCardData : Nat.card Dg = 2 ^ l - 1 := by
      exact hDgCard.trans hDcard
    have hDgIndex : Dg.index = (n + 1) * n := by
      obtain ⟨_hOmega, _hHcard, hGcard, _hdiv⟩ :=
        xi1115_action_parameters_core
          htwo_transitive a b hab F hFrob
      apply Nat.eq_of_mul_eq_mul_left ((show 0 < Nat.card D from Nat.card_pos))
      calc
        Nat.card D * Dg.index = Nat.card Dg * Dg.index := by
          rw [hDgCard]
        _ = Nat.card G := Dg.card_mul_index
        _ = Fintype.card Omega * Nat.card F * Nat.card D := hGcard
        _ = Nat.card D * ((n + 1) * n) := by
          rw [hdegree, hFcardN]
          ac_rfl
    have hDgNormalizerIndex :
        (Subgroup.normalizer (Dg : Set G)).index = (n + 1) * n / 2 := by
      have hmul := Subgroup.relIndex_mul_index
        (H := Dg) (K := Subgroup.normalizer (Dg : Set G))
        Subgroup.le_normalizer
      rw [hDgNormalizerRelIndex, hDgIndex] at hmul
      exact Nat.eq_div_of_mul_eq_right (by norm_num : (2 : ℕ) ≠ 0) hmul
    have hDgTI : ∀ k : G,
        k ∉ Subgroup.normalizer (Dg : Set G) →
          Disjoint Dg (Dg.map (MulAut.conj k).toMonoidHom) := by
      have hDgNe : Dg ≠ ⊥ := by
        rw [← Subgroup.one_lt_card_iff_ne_bot, hDgCard]
        exact (Subgroup.one_lt_card_iff_ne_bot D).2
          hFrobD.complement_ne_bot
      obtain ⟨x, hxneSub⟩ :=
        Subgroup.ne_bot_iff_exists_ne_one.mp hDgNe
      have hxne : (x : G) ≠ 1 := by
        intro hxone
        apply hxneSub
        exact Subtype.ext hxone
      have hCx :
          Subgroup.centralizer ({(x : G)} : Set G) = Dg :=
        hDgCentralizer (x : G) x.property hxne
      intro k hk
      rw [disjoint_iff, ← hCx]
      apply xi1115_centralizer_TI_core (x : G)
      · intro z hz hzNe
        have hzDg : z ∈ Dg := by rw [← hCx]; exact hz
        exact (hDgCentralizer z hzDg hzNe).trans hCx.symm
      · simpa [hCx] using hk
    exact ⟨hDgCardData, hDgNormalizerIndex, hDgTI⟩
  have hAData :
      (Subgroup.normalizer (A : Set G)).index =
          (n + 1) * n * (2 ^ l - 1) / (2 * (2 ^ l + 1)) ∧
      (∀ k : G, k ∉ Subgroup.normalizer (A : Set G) →
        Disjoint A (A.map (MulAut.conj k).toMonoidHom)) := by
    have hANormalizerIndex :
        (Subgroup.normalizer (A : Set G)).index =
          (n + 1) * n * (2 ^ l - 1) / (2 * (2 ^ l + 1)) := by
      obtain ⟨_hOmega, _hHcard, hGcard, _hdiv⟩ :=
        xi1115_action_parameters_core
          htwo_transitive a b hab F hFrob
      apply Nat.eq_div_of_mul_eq_left
        (by positivity : 2 * (2 ^ l + 1) ≠ 0)
      calc
        (Subgroup.normalizer (A : Set G)).index *
              (2 * (2 ^ l + 1)) =
            (Subgroup.normalizer (A : Set G)).index *
              Nat.card (Subgroup.normalizer (A : Set G)) := by
                rw [hANormalizerCard]
        _ = Nat.card G :=
          (Subgroup.normalizer (A : Set G)).index_mul_card
        _ = Fintype.card Omega * Nat.card F * Nat.card D := hGcard
        _ = (n + 1) * n * (2 ^ l - 1) := by
          rw [hdegree, hFcardN, hDcard]
    have hATIData : ∀ k : G,
        k ∉ Subgroup.normalizer (A : Set G) →
          Disjoint A (A.map (MulAut.conj k).toMonoidHom) := by
      exact hATI
    exact ⟨hANormalizerIndex, hATIData⟩
  let Families : Fin 3 → Subgroup G := ![Fg, Dg, A]
  have hFamiliesTI : ∀ i, ∀ k : G,
      k ∉ Subgroup.normalizer (Families i : Set G) →
        Disjoint (Families i)
          ((Families i).map (MulAut.conj k).toMonoidHom) := by
    intro i
    fin_cases i
    · simpa [Families] using hFgData.2.2
    · simpa [Families] using hDgData.2.2
    · simpa [Families] using hAData.2
  have hFamiliesCross : ∀ i j, i ≠ j → ∀ g h : G,
      Disjoint ((Families i).map (MulAut.conj g).toMonoidHom)
        ((Families j).map (MulAut.conj h).toMonoidHom) := by
    have hFgDgCoprime : Nat.Coprime (Nat.card Fg) (Nat.card Dg) := by
      rw [hFgData.1, hnPower, hDgCard]
      exact Nat.Coprime.pow_left f hDodd.coprime_two_left
    have hFgACoprime : Nat.Coprime (Nat.card Fg) (Nat.card A) := by
      have hAoddCard : Odd (Nat.card A) := by
        rw [hAcard]
        exact (Nat.even_pow.mpr ⟨even_two, hl.ne'⟩).add_one
      rw [hFgData.1, hnPower]
      exact Nat.Coprime.pow_left f hAoddCard.coprime_two_left
    have hDgACoprime : Nat.Coprime (Nat.card Dg) (Nat.card A) := by
      have hqEven : Even (2 ^ l) :=
        Nat.even_pow.mpr ⟨even_two, hl.ne'⟩
      have hqSubOdd : Odd (2 ^ l - 1) :=
        Nat.Even.sub_odd (pow_pos (by norm_num : 0 < (2 : ℕ)) l)
          hqEven odd_one
      have hcop : Nat.Coprime (2 ^ l - 1) ((2 ^ l - 1) + 2) :=
        (Nat.coprime_self_add_right).mpr hqSubOdd.coprime_two_right
      have heq : (2 ^ l - 1) + 2 = 2 ^ l + 1 := by
        rw [show 2 = 1 + 1 by norm_num, ← Nat.add_assoc,
          Nat.sub_add_cancel (Nat.one_le_pow l 2 (by norm_num))]
      rw [hDgData.1, hAcard]
      rwa [heq] at hcop
    have hConjDisjointOfCoprime :
        ∀ (U V : Subgroup G),
          Nat.Coprime (Nat.card U) (Nat.card V) →
            ∀ g h : G,
              Disjoint (U.map (MulAut.conj g).toMonoidHom)
                (V.map (MulAut.conj h).toMonoidHom) := by
      intro U V hcop g h
      rw [Subgroup.disjoint_def]
      intro x hxU hxV
      have hcopMap : Nat.Coprime
          (Nat.card (U.map (MulAut.conj g).toMonoidHom))
          (Nat.card (V.map (MulAut.conj h).toMonoidHom)) := by
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective,
          Subgroup.card_map_of_injective (MulAut.conj h).injective]
        exact hcop
      exact xi1115_mem_eq_one_of_coprime_card
        (U.map (MulAut.conj g).toMonoidHom)
        (V.map (MulAut.conj h).toMonoidHom) hcopMap hxU hxV
    intro i j hij g h
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · simpa [Families] using
        hConjDisjointOfCoprime Fg Dg hFgDgCoprime g h
    · simpa [Families] using
        hConjDisjointOfCoprime Fg A hFgACoprime g h
    · simpa [Families] using
        hConjDisjointOfCoprime Dg Fg hFgDgCoprime.symm g h
    · exact False.elim (hij rfl)
    · simpa [Families] using
        hConjDisjointOfCoprime Dg A hDgACoprime g h
    · simpa [Families] using
        hConjDisjointOfCoprime A Fg hFgACoprime.symm g h
    · simpa [Families] using
        hConjDisjointOfCoprime A Dg hDgACoprime.symm g h
    · exact False.elim (hij rfl)
  have hGlobalFamilyCount :
      (∑ i, (Subgroup.normalizer (Families i : Set G)).index *
        (Nat.card (Families i) - 1)) ≤ Nat.card G := by
    exact xi1115_disjoint_conjugate_families_card_le_of_TI
      Families hFamiliesTI hFamiliesCross
  have hGcardCount :
      Nat.card G = (n + 1) * n * (2 ^ l - 1) := by
    obtain ⟨_hOmega, _hHcard, hGcard, _hdiv⟩ :=
      xi1115_action_parameters_core
        htwo_transitive a b hab F hFrob
    calc
      Nat.card G =
          Fintype.card Omega * Nat.card F * Nat.card D := hGcard
      _ = (n + 1) * n * (2 ^ l - 1) := by
        rw [hdegree, hFcardN, hDcard]
  have hCountInequality :
      n ^ 2 - 1 +
          ((n + 1) * n / 2) * (2 ^ l - 2) +
          ((n + 1) * n * (2 ^ l - 1) / (2 * (2 ^ l + 1))) *
            (2 ^ l) ≤
        (n + 1) * n * (2 ^ l - 1) := by
    have hqTwo : 2 ≤ 2 ^ l := by
      have hqOne : 1 < 2 ^ l :=
        Nat.one_lt_pow hl.ne' (by norm_num)
      omega
    have hFgPuncturedTerm :
        (n + 1) * (n - 1) = n ^ 2 - 1 := by
      have hfactor : n ^ 2 - 1 = (n - 1) * (n + 1) := by
        let r0 := n - 1
        have hneq : n = r0 + 1 := by
          dsimp [r0]
          rw [hnPower]
          have hnOne : 1 ≤ 2 ^ f :=
            Nat.one_le_pow f 2 (by norm_num)
          omega
        rw [hneq]
        simp only [Nat.add_sub_cancel]
        apply (tsub_eq_iff_eq_add_of_le
          (Nat.one_le_pow' 2 r0)).2
        ring
      calc
        (n + 1) * (n - 1) = (n - 1) * (n + 1) := mul_comm _ _
        _ = n ^ 2 - 1 := hfactor.symm
    have hDgPunctured : Nat.card Dg - 1 = 2 ^ l - 2 := by
      rw [hDgData.1]
      omega
    have hAPunctured : Nat.card A - 1 = 2 ^ l := by
      rw [hAcard]
      omega
    have hFamilySumExpanded :
        (∑ i, (Subgroup.normalizer (Families i : Set G)).index *
            (Nat.card (Families i) - 1)) =
          n ^ 2 - 1 +
            ((n + 1) * n / 2) * (2 ^ l - 2) +
            ((n + 1) * n * (2 ^ l - 1) /
              (2 * (2 ^ l + 1))) * (2 ^ l) := by
      rw [Fin.sum_univ_three]
      simp [Families, hFgData.1, hFgData.2.1,
        hDgData.2.1, hAData.1, hFgPuncturedTerm,
        hDgPunctured, hAPunctured]
    rw [← hFamilySumExpanded, ← hGcardCount]
    exact hGlobalFamilyCount
  have hnLe : n ≤ 2 ^ l := by
    have hnTwo : 2 ≤ n := by
      rw [hnPower]
      have hnOne : 1 < 2 ^ f :=
        Nat.one_lt_pow hf.ne' (by norm_num)
      omega
    have hqTwo : 2 ≤ 2 ^ l := by
      have hqOne : 1 < 2 ^ l :=
        Nat.one_lt_pow hl.ne' (by norm_num : 1 < (2 : ℕ))
      omega
    have hHalfMul :
        2 * ((n + 1) * n / 2) = (n + 1) * n := by
      apply Nat.mul_div_cancel'
      exact dvd_mul_of_dvd_right
        (even_iff_two_dvd.mp hnEven) (n + 1)
    have hAQuotMul :
        (2 * (2 ^ l + 1)) *
            ((n + 1) * n * (2 ^ l - 1) /
              (2 * (2 ^ l + 1))) =
          (n + 1) * n * (2 ^ l - 1) := by
      calc
        (2 * (2 ^ l + 1)) *
              ((n + 1) * n * (2 ^ l - 1) /
                (2 * (2 ^ l + 1))) =
            (2 * (2 ^ l + 1)) *
              (Subgroup.normalizer (A : Set G)).index := by
                rw [hAData.1]
        _ = (Subgroup.normalizer (A : Set G)).index *
              (2 * (2 ^ l + 1)) := mul_comm _ _
        _ = (Subgroup.normalizer (A : Set G)).index *
              Nat.card (Subgroup.normalizer (A : Set G)) := by
                rw [hANormalizerCard]
        _ = Nat.card G :=
          (Subgroup.normalizer (A : Set G)).index_mul_card
        _ = (n + 1) * n * (2 ^ l - 1) := hGcardCount
    have hnLeSucc : n ≤ 2 ^ l + 1 :=
      xi1115_global_count_n_le_succ n (2 ^ l)
        ((n + 1) * n / 2)
        ((n + 1) * n * (2 ^ l - 1) / (2 * (2 ^ l + 1)))
        hnTwo hqTwo hHalfMul hAQuotMul hCountInequality
    have hqEven : Even (2 ^ l) :=
      Nat.even_pow.mpr ⟨even_two, hl.ne'⟩
    exact xi1115_even_le_of_le_succ n (2 ^ l) hnEven hqEven hnLeSucc
  have hqLe : 2 ^ l ≤ n := by
    have hqTwo : 2 ≤ 2 ^ l := by
      have hqOne : 1 < 2 ^ l :=
        Nat.one_lt_pow hl.ne' (by norm_num : 1 < (2 : ℕ))
      omega
    have hnOne : 1 < n := by
      rw [hnPower]
      exact Nat.one_lt_pow hf.ne' (by norm_num : 1 < (2 : ℕ))
    have hFpredPos : 0 < Nat.card F - 1 := by
      rw [hFcardN]
      exact Nat.sub_pos_of_lt hnOne
    have hDle : Nat.card D ≤ Nat.card F - 1 :=
      Nat.le_of_dvd hFpredPos hDdiv
    rw [hDcard, hFcardN] at hDle
    exact xi1115_le_of_pred_le_pred n (2 ^ l) hqTwo hDle
  have hnEq : n = 2 ^ l := Nat.le_antisymm hnLe hqLe
  have hSharpCard :
      Nat.card G = (Fintype.card Omega).descFactorial 3 := by
    calc
      Nat.card G = (n + 1) * n * (2 ^ l - 1) := hGcardCount
      _ = (n + 1) * n * (n - 1) := by rw [hnEq]
      _ = (Fintype.card Omega).descFactorial 3 := by
        rw [hdegree]
        exact (xi1115_descFactorial_three n
          (by rw [hnPower];
              have hnOne : 1 < 2 ^ f :=
                Nat.one_lt_pow hf.ne' (by norm_num : 1 < (2 : ℕ))
              omega)).symm
  exact xi1115_sharpTriple_of_card_eq_descFactorial
    hSharpCard hat_most_two_fixed_points

set_option maxHeartbeats 800000 in
private theorem xi1115_nonsplit_centralizer_eq
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hdegreeOdd : Odd (Fintype.card Omega))
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hF2 : IsPGroup 2 F)
    (hFSuzuki : PFAppendixIII.IsSuzukiTwoGroup F)
    (s : G)
    (hallInvolutionsConj : ∀ t : G, orderOf t = 2 → IsConj t s)
    (l : ℕ) (hl : 0 < l)
    (D : Subgroup (MulAction.stabilizer G a))
    (hFrobD : IsFrobeniusGroupWithKernelComplement F D)
    (hDcard : Nat.card D = 2 ^ l - 1)
    (A C : Subgroup G) (agen : A)
    (hCdef : C = Subgroup.centralizer ({(agen : G)} : Set G))
    (hAcard : Nat.card A = 2 ^ l + 1)
    (hx0order : orderOf agen = Nat.card A)
    (NonsplitClasses : Set (ConjClasses G))
    (hNonsplitDef : NonsplitClasses =
      Set.range (fun x : {x : A // (x : G) ≠ 1} =>
        ConjClasses.mk (x : G)))
    (hAClassRange : Nat.card NonsplitClasses * 2 = 2 ^ l)
    (hx0Strong : PFAppendixIII.IsStronglyReal (agen : G))
    (hx0sq : (agen : G) ^ 2 ≠ 1)
    (hA_le_C : A ≤ C)
    (hCodd : Odd (Nat.card C))
    (hCcomm : IsMulCommutative C)
    (t : G) (htInv : PFAppendixIII.IsInvolution t)
    (htInverts : ∀ z : G, z ∈ C → t * z * t⁻¹ = z⁻¹)
    (hCnontrivial : ∀ z : G, z ∈ C → z ≠ 1 →
      PFAppendixIII.IsStronglyReal z ∧
        Subgroup.centralizer ({z} : Set G) = C)
    (hApreTI : ∀ k : G,
      k ∉ Subgroup.normalizer (A : Set G) →
        Disjoint A (A.map (MulAut.conj k).toMonoidHom))
    (hCConjA : ∀ z : G, z ∈ C → z ≠ 1 →
      ∃ y : G, y ∈ A ∧ IsConj z y) :
    C = A := by
  letI : F.Normal := hFrob.normal
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hCne
  let x0 : G := (agen : G)
  have hAltC : A < C := lt_of_le_of_ne hA_le_C (fun h => hCne h.symm)
  have hCHall : Nat.Coprime (Nat.card C) C.index := by
    simpa [hCdef, x0] using
      xi1115_stronglyReal_centralizer_card_coprime_index
        htwo_transitive hdegreeOdd hat_most_two_fixed_points
        hno_regular_normal a b hab F hFrob hF2 hFSuzuki
        s hallInvolutionsConj x0 hx0Strong hx0sq
  let N : Subgroup G := Subgroup.normalizer (C : Set G)
  let CN : Subgroup N := C.subgroupOf N
  have hComplementData :
      ∃ R : Subgroup N,
        Disjoint CN R ∧ CN ⊔ R = ⊤ ∧
          Nat.card R = CN.index ∧ IsPGroup 2 R := by
    letI : CN.Normal := by
      dsimp [CN, N]
      infer_instance
    have hCNcard : Nat.card CN = Nat.card C := by
      exact Nat.card_congr
        (Subgroup.subgroupOfEquivOfLe C.le_normalizer).toEquiv
    have hCNindexDvd : CN.index ∣ C.index := by
      simpa [CN, N, Subgroup.relIndex] using
        (Subgroup.relIndex_dvd_index_of_le C.le_normalizer)
    have hCNcop : Nat.Coprime (Nat.card CN) CN.index := by
      rw [hCNcard]
      exact hCHall.coprime_dvd_right hCNindexDvd
    obtain ⟨R, hcomp⟩ :=
      Subgroup.exists_right_complement'_of_coprime
        (N := CN) hCNcop
    have hRcard : Nat.card R = CN.index :=
      hcomp.symm.index_eq_card.symm
    have htNormalizerC : t ∈ Subgroup.normalizer (C : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hzC
        rw [htInverts z hzC]
        exact C.inv_mem hzC
      · intro hzC
        let y : G := t * z * t⁻¹
        have hyC : y ∈ C := hzC
        have hback : t * y * t⁻¹ = z := by
          dsimp [y]
          rw [htInv.inv_eq_self]
          calc
            t * (t * z * t) * t = (t * t) * z * (t * t) := by group
            _ = z := by
              rw [show t * t = 1 by
                simpa [pow_two] using htInv.sq_eq_one]
              simp
        have hyInv := htInverts y hyC
        have hzEq : z = y⁻¹ := hback.symm.trans hyInv
        rw [hzEq]
        exact C.inv_mem hyC
    have htNotC : t ∉ C := by
      intro htC
      let tC : C := ⟨t, htC⟩
      have htCorder : orderOf tC = 2 := by
        simpa [tC] using
          orderOf_eq_prime htInv.sq_eq_one htInv.ne_one
      have htwoDvd : 2 ∣ Nat.card C := by
        rw [← htCorder]
        exact orderOf_dvd_natCard tC
      exact hCodd.not_two_dvd_nat htwoDvd
    let tN : N := ⟨t, htNormalizerC⟩
    have htNnotCN : tN ∉ CN := by
      simpa [tN, CN, Subgroup.mem_subgroupOf] using htNotC
    let tq : N ⧸ CN := QuotientGroup.mk' CN tN
    have htqSq : tq ^ 2 = 1 := by
      have htNsq : tN ^ 2 = 1 := by
        apply Subtype.ext
        simpa using htInv.sq_eq_one
      change (QuotientGroup.mk' CN tN) ^ 2 = 1
      rw [← map_pow, htNsq, map_one]
    have htqNe : tq ≠ 1 := by
      intro htqOne
      apply htNnotCN
      exact (QuotientGroup.eq_one_iff (N := CN) tN).mp htqOne
    have htqOrder : orderOf tq = 2 :=
      orderOf_eq_prime htqSq htqNe
    have htwoIndex : 2 ∣ CN.index := by
      rw [← htqOrder]
      exact orderOf_dvd_natCard tq
    have hRcardEven : Even (Nat.card R) := by
      rw [hRcard]
      exact even_iff_two_dvd.mpr htwoIndex
    have hCNne : CN ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot, hCNcard]
      have hAone : 1 < Nat.card A := by
        rw [hAcard]
        have hpowPos : 0 < 2 ^ l := pow_pos (by norm_num) l
        omega
      exact lt_of_lt_of_le hAone
        (Subgroup.card_le_of_le hA_le_C)
    have hRne : R ≠ ⊥ := by
      rw [← Subgroup.one_lt_card_iff_ne_bot]
      have hRpos : 0 < Nat.card R := Nat.card_pos
      have hRtwo : 2 ∣ Nat.card R := even_iff_two_dvd.mp hRcardEven
      omega
    have hFrobCR : IsFrobeniusGroupWithKernelComplement CN R := by
      refine (lemma_3_1 CN R hCNne hRne inferInstance hcomp).2 ?_
      intro r hrne
      rw [Subgroup.eq_bot_iff_forall]
      intro c hc
      rcases hc with ⟨hcCN, hccomm⟩
      by_contra hcne
      have hcG : (((c : N) : G)) ∈ C := by
        simpa [CN, Subgroup.mem_subgroupOf] using hcCN
      have hcGne : (((c : N) : G)) ≠ 1 := by
        intro h
        apply hcne
        apply Subtype.ext
        exact h
      have hCc :
          Subgroup.centralizer ({(((c : N) : G))} : Set G) = C :=
        (hCnontrivial (((c : N) : G)) hcG hcGne).2
      have hrcomm : ((r : N) : G) * ((c : N) : G) =
          ((c : N) : G) * ((r : N) : G) := by
        have h := Subgroup.mem_centralizer_singleton_iff.mp hccomm
        exact congrArg Subtype.val h.symm
      have hrC : ((r : N) : G) ∈ C := by
        rw [← hCc]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hrcomm
      have hrCN : (r : N) ∈ CN := by
        simpa [CN, Subgroup.mem_subgroupOf] using hrC
      have hrOneN : (r : N) = 1 :=
        Subgroup.disjoint_def.mp hcomp.disjoint hrCN r.property
      exact hrne (Subtype.ext hrOneN)
    obtain ⟨r0, hr0order⟩ :=
      exists_prime_orderOf_dvd_card' (G := R) 2
        (even_iff_two_dvd.mp hRcardEven)
    have hr0center : r0 ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro u
      let r1 : R := u * r0 * u⁻¹
      have hr1order : orderOf r1 = 2 := by
        exact ((MulAut.conj u).orderOf_eq r0).trans hr0order
      have hr1eq : r1 = r0 :=
        xi1115_frobenius_complement_involutions_eq
          CN R hFrobCR r1 r0 hr1order hr0order
      have h := congrArg (fun z : R => z * u) hr1eq
      simpa [r1, mul_assoc] using h
    let rG : G := ((r0 : R) : N)
    have hrGorder : orderOf rG = 2 := by
      simpa [rG] using hr0order
    have hallR : ∀ u : G, orderOf u = 2 → IsConj u rG := by
      intro u hu
      exact (hallInvolutionsConj u hu).trans
        (hallInvolutionsConj rG hrGorder).symm
    have hCrCard :
        Nat.card (Subgroup.centralizer ({rG} : Set G)) = Nat.card F :=
      xi1115_involution_centralizer_card_eq_kernel
        htwo_transitive a b hab F hFrob hF2 rG hallR
    have hCr2 : IsPGroup 2
        (Subgroup.centralizer ({rG} : Set G)) := by
      rcases IsPGroup.iff_card.mp hF2 with ⟨e, he⟩
      exact IsPGroup.iff_card.mpr ⟨e, hCrCard.trans he⟩
    let phiR : R →* Subgroup.centralizer ({rG} : Set G) :=
      { toFun := fun u => ⟨((u : R) : N), by
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          have hcommR : r0 * u = u * r0 :=
            (Subgroup.mem_center_iff.mp hr0center u).symm
          simpa [rG] using congrArg
            (fun z : R => (((z : R) : N) : G)) hcommR.symm⟩
        map_one' := by apply Subtype.ext; rfl
        map_mul' := by intro x y; apply Subtype.ext; rfl }
    have hphiR : Function.Injective phiR := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg
        (fun z : Subgroup.centralizer ({rG} : Set G) => (z : G)) hxy
    have hR2 : IsPGroup 2 R := hCr2.of_injective phiR hphiR
    exact ⟨R, hcomp.disjoint, hcomp.sup_eq_top, hRcard, hR2⟩

  obtain ⟨R, hCNRdisjoint, hCNRtop, hRcardIndex, hR2⟩ :=
    hComplementData
  have hCClassCount :
      (Nat.card C - 1) * 2 = Nat.card R * (2 ^ l) := by
    classical
    letI : CN.Normal := by
      dsimp [CN, N]
      infer_instance
    let X := {z : C // (z : G) ≠ 1}
    let clsC : X → ConjClasses G := fun z => ConjClasses.mk (z : G)
    let clsCRange : X → Set.range clsC :=
      Set.rangeFactorization clsC
    have hRangeEq : Set.range clsC = NonsplitClasses := by
      rw [hNonsplitDef]
      apply Set.Subset.antisymm
      · rintro c ⟨z, rfl⟩
        obtain ⟨y, hyA, hzy⟩ := hCConjA (z : G) z.1.property z.2
        have hyne : y ≠ 1 := by
          intro hyone
          apply z.2
          rw [isConj_iff] at hzy
          rcases hzy with ⟨g, hg⟩
          calc
            (z : G) = g⁻¹ * y * g := by
              rw [← hg]
              group
            _ = 1 := by rw [hyone]; simp
        refine ⟨⟨⟨y, hyA⟩, hyne⟩, ?_⟩
        exact ConjClasses.mk_eq_mk_iff_isConj.mpr hzy.symm
      · rintro c ⟨y, rfl⟩
        let zC : C := ⟨(y : G), hA_le_C y.1.property⟩
        let zX : X := ⟨zC, y.2⟩
        exact ⟨zX, rfl⟩
    let conjX : R → X → X := fun r z =>
      ⟨⟨((r : N) : G) * (z : G) * ((r : N) : G)⁻¹, by
          have hrNorm : ((r : N) : G) ∈
              Subgroup.normalizer (C : Set G) := by
            exact (r : N).property
          exact (Subgroup.mem_normalizer_iff.mp hrNorm (z : G)).mp
            z.1.property⟩,
        by
          intro hOne
          apply z.2
          have hOneG :
              ((r : N) : G) * (z : G) * ((r : N) : G)⁻¹ = 1 := hOne
          calc
            (z : G) = ((r : N) : G)⁻¹ *
                (((r : N) : G) * (z : G) * ((r : N) : G)⁻¹) *
                  ((r : N) : G) := by group
            _ = 1 := by rw [hOneG]; simp⟩
    have hclsConj (r : R) (z : X) : clsC (conjX r z) = clsC z := by
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      rw [isConj_iff]
      refine ⟨((r : N) : G)⁻¹, ?_⟩
      dsimp [conjX]
      group
    have hfiber (c : Set.range clsC) :
        Nat.card {z : X // clsCRange z = c} = Nat.card R := by
      rcases c.2 with ⟨x, hx⟩
      let orbit : R → {z : X // clsCRange z = c} := fun r =>
        ⟨conjX r x, by
          apply Subtype.ext
          exact (hclsConj r x).trans hx⟩
      have horbitInjective : Function.Injective orbit := by
        intro r s hrs
        have hconjEq :
            ((r : N) : G) * (x : G) * ((r : N) : G)⁻¹ =
              ((s : N) : G) * (x : G) * ((s : N) : G)⁻¹ := by
          exact congrArg (fun z : {z : X // clsCRange z = c} =>
            (((z.1.1 : C) : G))) hrs
        let k : N := (s : N)⁻¹ * (r : N)
        have hkcomm : (k : G) * (x : G) = (x : G) * (k : G) := by
          change (((s : N) : G)⁻¹ * ((r : N) : G)) * (x : G) =
            (x : G) * (((s : N) : G)⁻¹ * ((r : N) : G))
          calc
            (((s : N) : G)⁻¹ * ((r : N) : G)) * (x : G) =
                ((s : N) : G)⁻¹ *
                  (((r : N) : G) * (x : G) * ((r : N) : G)⁻¹) *
                    ((r : N) : G) := by group
            _ = ((s : N) : G)⁻¹ *
                  (((s : N) : G) * (x : G) * ((s : N) : G)⁻¹) *
                    ((r : N) : G) := by rw [hconjEq]
            _ = (x : G) *
                (((s : N) : G)⁻¹ * ((r : N) : G)) := by group
        have hCx : Subgroup.centralizer ({(x : G)} : Set G) = C :=
          (hCnontrivial (x : G) x.1.property x.2).2
        have hkC : (k : G) ∈ C := by
          rw [← hCx]
          exact Subgroup.mem_centralizer_singleton_iff.mpr hkcomm
        have hkCN : k ∈ CN := by simpa [CN, Subgroup.mem_subgroupOf] using hkC
        have hkR : k ∈ R := R.mul_mem (R.inv_mem s.property) r.property
        have hkOne : k = 1 :=
          Subgroup.disjoint_def.mp hCNRdisjoint hkCN hkR
        apply Subtype.ext
        have h := congrArg (fun z : N => (s : N) * z) hkOne
        simpa [k, mul_assoc] using h
      have horbitSurjective : Function.Surjective orbit := by
        intro z
        have hclsEq : clsC x = clsC z.1 := by
          exact hx.trans (congrArg Subtype.val z.2).symm
        have hxz : IsConj (x : G) (z.1 : G) :=
          ConjClasses.mk_eq_mk_iff_isConj.mp hclsEq
        rw [isConj_iff] at hxz
        rcases hxz with ⟨g, hg⟩
        have hCx : Subgroup.centralizer ({(x : G)} : Set G) = C :=
          (hCnontrivial (x : G) x.1.property x.2).2
        have hCz : Subgroup.centralizer ({(z.1 : G)} : Set G) = C :=
          (hCnontrivial (z.1 : G) z.1.1.property z.1.2).2
        have hmapC : C.map (MulAut.conj g).toMonoidHom = C := by
          calc
            C.map (MulAut.conj g).toMonoidHom =
                (Subgroup.centralizer ({(x : G)} : Set G)).map
                  (MulAut.conj g).toMonoidHom := by rw [hCx]
            _ = Subgroup.centralizer ({g * (x : G) * g⁻¹} : Set G) :=
              (xi1115_centralizer_conj_eq (x : G) g).symm
            _ = Subgroup.centralizer ({(z.1 : G)} : Set G) := by rw [hg]
            _ = C := hCz
        have hgNorm : g ∈ Subgroup.normalizer (C : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro q
          constructor
          · intro hqC
            have hqMap : g * q * g⁻¹ ∈
                C.map (MulAut.conj g).toMonoidHom :=
              ⟨q, hqC, rfl⟩
            rwa [hmapC] at hqMap
          · intro hqConj
            have hqMap : g * q * g⁻¹ ∈
                C.map (MulAut.conj g).toMonoidHom := by
              rw [hmapC]
              exact hqConj
            rcases hqMap with ⟨q0, hq0C, hq0eq⟩
            have hq0q : q0 = q := (MulAut.conj g).injective
              (by simpa using hq0eq)
            simpa [← hq0q] using hq0C
        let gN : N := ⟨g, hgNorm⟩
        have hgSup : gN ∈ CN ⊔ R := by
          rw [hCNRtop]
          exact Subgroup.mem_top gN
        rcases Subgroup.mem_sup_of_normal_left.mp hgSup with
          ⟨cN, hcN, rN, hrN, hcr⟩
        let r0 : R := ⟨rN, hrN⟩
        refine ⟨r0, ?_⟩
        apply Subtype.ext
        apply Subtype.ext
        apply Subtype.ext
        have hcG : (cN : G) ∈ C := by simpa [CN, Subgroup.mem_subgroupOf] using hcN
        have hrxC :
            (rN : G) * (x : G) * (rN : G)⁻¹ ∈ C :=
          (conjX r0 x).1.property
        have hcomm : cN *
              ((rN : G) * (x : G) * (rN : G)⁻¹) =
            ((rN : G) * (x : G) * (rN : G)⁻¹) * cN := by
          exact congrArg Subtype.val
            ((@IsMulCommutative.is_comm C _ hCcomm).comm
              (⟨(cN : G), hcG⟩ : C)
              (⟨(rN : G) * (x : G) * (rN : G)⁻¹, hrxC⟩ : C))
        have hgform : g = (cN : G) * (rN : G) := by
          exact congrArg Subtype.val hcr.symm
        calc
          (rN : G) * (x : G) * (rN : G)⁻¹ =
              (cN : G) *
                ((rN : G) * (x : G) * (rN : G)⁻¹) *
                  (cN : G)⁻¹ := by
            rw [hcomm]
            simp
          _ = g * (x : G) * g⁻¹ := by rw [hgform]; group
          _ = (z.1 : G) := hg
      exact (Nat.card_congr
        (Equiv.ofBijective orbit ⟨horbitInjective, horbitSurjective⟩)).symm
    letI : Fintype (Set.range clsC) := Fintype.ofFinite _
    letI (c : Set.range clsC) : Fintype {z : X // clsCRange z = c} :=
      Fintype.ofFinite _
    have hcardSigma :
        Nat.card (Σ c : Set.range clsC, {z : X // clsCRange z = c}) =
          Nat.card X :=
      Nat.card_congr (Equiv.sigmaFiberEquiv clsCRange)
    rw [Nat.card_sigma] at hcardSigma
    simp_rw [hfiber] at hcardSigma
    rw [Finset.sum_const, Finset.card_univ] at hcardSigma
    have hXcard : Nat.card X = Nat.card NonsplitClasses * Nat.card R := by
      have htemp : Nat.card X = Nat.card (Set.range clsC) * Nat.card R := by
        simpa only [Nat.card_eq_fintype_card, nsmul_eq_mul, Nat.cast_id] using
          hcardSigma.symm
      rw [hRangeEq] at htemp
      exact htemp
    have hpunctured : Nat.card X = Nat.card C - 1 := by
      simpa [X] using xi1115_punctured_subgroup_card C
    calc
      (Nat.card C - 1) * 2 = Nat.card X * 2 := by rw [hpunctured]
      _ = (Nat.card NonsplitClasses * Nat.card R) * 2 := by rw [hXcard]
      _ = Nat.card R * (Nat.card NonsplitClasses * 2) := by ac_rfl
      _ = Nat.card R * (2 ^ l) := by rw [hAClassRange]

  have hAprime : Nat.Prime (Nat.card A) := by
    have hAcardTwo : 2 ≤ Nat.card A := by
      rw [hAcard]
      have hqpos : 0 < 2 ^ l := pow_pos (by norm_num) l
      omega
    by_contra hnotPrime
    let p := Nat.minFac (Nat.card A)
    have hp : Nat.Prime p :=
      Nat.minFac_prime (by omega : Nat.card A ≠ 1)
    letI : Fact (Nat.Prime p) := ⟨hp⟩
    have hpDvd : p ∣ Nat.card A := Nat.minFac_dvd (Nat.card A)
    have hpLt : p < Nat.card A :=
      (Nat.not_prime_iff_minFac_lt hAcardTwo).mp hnotPrime
    have hconjA_le_C : ∀ z y g : G,
        z ∈ C → z ≠ 1 → y ∈ A → y ≠ 1 →
        g * z * g⁻¹ = y →
          A.map (MulAut.conj g⁻¹).toMonoidHom ≤ C := by
      intro z y g hzC hzne hyA hyne hzy
      have hCz : Subgroup.centralizer ({z} : Set G) = C :=
        (hCnontrivial z hzC hzne).2
      have hCy : Subgroup.centralizer ({y} : Set G) = C :=
        (hCnontrivial y (hA_le_C hyA) hyne).2
      have hback : g⁻¹ * y * (g⁻¹)⁻¹ = z := by
        rw [← hzy]
        group
      have hmapCentralizer :
          (Subgroup.centralizer ({y} : Set G)).map
              (MulAut.conj g⁻¹).toMonoidHom = C := by
        calc
          (Subgroup.centralizer ({y} : Set G)).map
              (MulAut.conj g⁻¹).toMonoidHom =
              Subgroup.centralizer ({g⁻¹ * y * (g⁻¹)⁻¹} : Set G) :=
            (xi1115_centralizer_conj_eq y g⁻¹).symm
          _ = Subgroup.centralizer ({z} : Set G) := by rw [hback]
          _ = C := hCz
      intro u hu
      rcases hu with ⟨u0, hu0A, rfl⟩
      rw [← hmapCentralizer]
      exact Subgroup.mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom
        (by rw [hCy]; exact hA_le_C hu0A)
    obtain ⟨b0, hb0C, hb0A⟩ := SetLike.exists_of_lt hAltC
    have hb0ne : (b0 : G) ≠ 1 := by
      intro hb0one
      apply hb0A
      simp [hb0one]
    obtain ⟨y0, hy0A, hb0y0⟩ := hCConjA (b0 : G) hb0C hb0ne
    have hy0ne : y0 ≠ 1 := by
      intro hy0one
      rw [isConj_iff] at hb0y0
      rcases hb0y0 with ⟨g, hg⟩
      apply hb0ne
      calc
        (b0 : G) = g⁻¹ * y0 * g := by rw [← hg]; group
        _ = 1 := by rw [hy0one]; simp
    rw [isConj_iff] at hb0y0
    rcases hb0y0 with ⟨g, hgb⟩
    let B : Subgroup G := A.map (MulAut.conj g⁻¹).toMonoidHom
    have hbB : (b0 : G) ∈ B := by
      refine ⟨y0, hy0A, ?_⟩
      change g⁻¹ * y0 * (g⁻¹)⁻¹ = (b0 : G)
      rw [← hgb]
      group
    have hB_le_C : B ≤ C := by
      exact hconjA_le_C (b0 : G) y0 g hb0C hb0ne
        hy0A hy0ne hgb
    have hginvNotNorm : g⁻¹ ∉ Subgroup.normalizer (A : Set G) := by
      intro hnorm
      apply hb0A
      have hgNorm : g ∈ Subgroup.normalizer (A : Set G) := by
        simpa using
          (Subgroup.normalizer (A : Set G)).inv_mem hnorm
      have hBA : B = A := by
        ext z
        simp only [B, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
        simpa only [inv_inv] using
          (Subgroup.mem_normalizer_iff.mp hgNorm z).symm
      rw [← hBA]
      exact hbB
    have hABdisjoint : Disjoint A B := by
      simpa [B] using hApreTI g⁻¹ hginvNotNorm
    have hBcard : Nat.card B = Nat.card A := by
      exact Nat.card_congr
        ((MulAut.conj g⁻¹).subgroupMap A).toEquiv.symm
    obtain ⟨cB, hcBorder⟩ :=
      exists_prime_orderOf_dvd_card' (G := B) p (by
        rw [hBcard]
        exact hpDvd)
    let cG : G := (cB : G)
    have hcGne : cG ≠ 1 := by
      intro hcGone
      have hcBone : cB = 1 := Subtype.ext hcGone
      rw [hcBone, orderOf_one] at hcBorder
      exact hp.ne_one hcBorder.symm
    have hcGpow : cG ^ p = 1 := by
      have hcBpow : cB ^ p = 1 := by
        rw [← hcBorder]
        exact pow_orderOf_eq_one cB
      simpa [cG] using congrArg Subtype.val hcBpow
    have hx0p : x0 ^ p ≠ 1 := by
      intro hx0pOne
      have hagenp : agen ^ p = 1 := by
        apply Subtype.ext
        exact hx0pOne
      have hcardDvdP : Nat.card A ∣ p := by
        rw [← hx0order]
        exact orderOf_dvd_of_pow_eq_one hagenp
      exact (not_le_of_gt hpLt) (Nat.le_of_dvd hp.pos hcardDvdP)
    let d : G := x0 * cG
    have hcC : cG ∈ C := hB_le_C cB.property
    have hcomm : Commute x0 cG := by
      exact congrArg Subtype.val
        ((@IsMulCommutative.is_comm C _ hCcomm).comm
          (⟨x0, hA_le_C agen.property⟩ : C)
          (⟨cG, hcC⟩ : C))
    have hdpow : d ^ p = x0 ^ p := by
      dsimp [d]
      rw [hcomm.mul_pow, hcGpow, mul_one]
    have hdne : d ≠ 1 := by
      intro hdone
      apply hx0p
      rw [← hdpow, hdone, one_pow]
    have hdC : d ∈ C := C.mul_mem (hA_le_C agen.property) hcC
    obtain ⟨y1, hy1A, hdy1⟩ := hCConjA d hdC hdne
    have hy1ne : y1 ≠ 1 := by
      intro hy1one
      rw [isConj_iff] at hdy1
      rcases hdy1 with ⟨k, hk⟩
      apply hdne
      calc
        d = k⁻¹ * y1 * k := by rw [← hk]; group
        _ = 1 := by rw [hy1one]; simp
    rw [isConj_iff] at hdy1
    rcases hdy1 with ⟨k, hkd⟩
    let K : Subgroup G := A.map (MulAut.conj k⁻¹).toMonoidHom
    have hdK : d ∈ K := by
      refine ⟨y1, hy1A, ?_⟩
      change k⁻¹ * y1 * (k⁻¹)⁻¹ = d
      rw [← hkd]
      group
    have hxpA : x0 ^ p ∈ A := A.pow_mem agen.property p
    have hxpK : x0 ^ p ∈ K := by
      rw [← hdpow]
      exact K.pow_mem hdK p
    have hkinvNorm : k⁻¹ ∈ Subgroup.normalizer (A : Set G) := by
      by_contra hknot
      have hdis : Disjoint A K := by
        simpa [K] using hApreTI k⁻¹ hknot
      exact hx0p
        (Subgroup.disjoint_def.mp hdis hxpA hxpK)
    have hkNorm : k ∈ Subgroup.normalizer (A : Set G) := by
      simpa using
        (Subgroup.normalizer (A : Set G)).inv_mem hkinvNorm
    have hKA : K = A := by
      ext z
      simp only [K, Subgroup.mem_map_equiv, MulAut.conj_symm_apply]
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp hkNorm z).symm
    have hdA : d ∈ A := by rw [← hKA]; exact hdK
    have hcA : cG ∈ A := by
      have heq : cG = x0⁻¹ * d := by dsimp [d]; group
      rw [heq]
      exact A.mul_mem (A.inv_mem agen.property) hdA
    have hcOne : cG = 1 :=
      Subgroup.disjoint_def.mp hABdisjoint hcA cB.property
    exact hcGne hcOne

  letI : Fact (Nat.Prime (Nat.card A)) := ⟨hAprime⟩
  have hCp : IsPGroup (Nat.card A) C := by
    apply IsPGroup.iff_orderOf.mpr
    intro z
    by_cases hzone : z = 1
    · refine ⟨0, ?_⟩
      simp [hzone]
    · have hzGne : (z : G) ≠ 1 := by
        intro h
        apply hzone
        exact Subtype.ext h
      obtain ⟨y, hyA, hzy⟩ := hCConjA (z : G) z.property hzGne
      have hyne : y ≠ 1 := by
        intro hyone
        rw [isConj_iff] at hzy
        rcases hzy with ⟨g, hg⟩
        apply hzGne
        calc
          (z : G) = g⁻¹ * y * g := by rw [← hg]; group
          _ = 1 := by rw [hyone]; simp
      let yA : A := ⟨y, hyA⟩
      have hyPow : y ^ Nat.card A = 1 := by
        change ((yA : A) : G) ^ Nat.card A = 1
        exact congrArg Subtype.val
          (pow_card_eq_one' (x := yA))
      have hyOrder : orderOf y = Nat.card A :=
        orderOf_eq_prime hyPow hyne
      rw [isConj_iff] at hzy
      rcases hzy with ⟨g, hg⟩
      have hord := (MulAut.conj g).orderOf_eq (z : G)
      have hg' : (MulAut.conj g) (z : G) = y := by
        simpa [MulAut.conj_apply] using hg
      rw [hg'] at hord
      refine ⟨1, ?_⟩
      simpa using hord.symm.trans hyOrder

  obtain ⟨r, hCcardPow⟩ := IsPGroup.iff_card.mp hCp
  have hRcardPow : ∃ e : ℕ, Nat.card R = 2 ^ e :=
    IsPGroup.iff_card.mp hR2
  obtain ⟨e, hRcard⟩ := hRcardPow
  have hAcardLtC : Nat.card A < Nat.card C := by
    apply Set.Finite.card_lt_card (Set.toFinite (C : Set G))
    exact hAltC
  have hDoneLt : 1 < Nat.card D := by
    exact (Subgroup.one_lt_card_iff_ne_bot D).2
      hFrobD.complement_ne_bot
  exact xi1115_nonsplit_centralizer_numeric_impossible
    (Nat.card A) (Nat.card C) (Nat.card R) (Nat.card D)
    l r e hl hAcard hDcard hCcardPow hRcard hCClassCount
    hAcardLtC hAprime hDoneLt
private theorem xi1115_rank_one_card_arithmetic (q : ℕ) :
    q * (q - 1) + q * (q - 1) * q = (q + 1) * q * (q - 1) := by
  ring

private theorem xi1115_eq_zero_of_eq_add_self
    {A : Type*} [AddGroup A] (x : A) (h : x = x + x) : x = 0 := by
  exact add_left_cancel (h.symm.trans (add_zero x).symm)

private theorem xi1115_smul_ne_one
    {D F : Type*} [Group D] [Group F] [MulDistribMulAction D F]
    (d : D) {x : F} (hx : x ≠ 1) :
    d • x ≠ 1 := by
  intro hdx
  apply hx
  calc
    x = d⁻¹ • (d • x) := (inv_smul_smul d x).symm
    _ = d⁻¹ • 1 := by rw [hdx]
    _ = 1 := smul_one d⁻¹

set_option maxHeartbeats 800000 in
private theorem xi1115_inverse_bruhat_coordinates
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H) (s : G)
    (hss : s * s = 1)
    (hInverts :
      ∀ d : D,
        s * (((d : D) : H) : G) * s⁻¹ =
          ((((d⁻¹ : D) : D) : H) : G))
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hcoord :
      ∀ x : {x : F // x ≠ 1},
        s * (((x.1 : F) : H) : G) * s =
          ((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (x : {x : F // x ≠ 1}) :
    (coord ⟨x.1⁻¹, inv_ne_one.mpr x.2⟩).1 = (coord x).2.2⁻¹ ∧
      (coord ⟨x.1⁻¹, inv_ne_one.mpr x.2⟩).2.1 = (coord x).2.1 ∧
        (coord ⟨x.1⁻¹, inv_ne_one.mpr x.2⟩).2.2 = (coord x).1⁻¹ := by
  let xInv : {x : F // x ≠ 1} := ⟨x.1⁻¹, inv_ne_one.mpr x.2⟩
  let candidate : F × D × F :=
    ((coord x).2.2⁻¹, (coord x).2.1, (coord x).1⁻¹)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hxInvVal : (((x.1⁻¹ : F) : H) : G) =
      (((x.1 : F) : H) : G)⁻¹ := rfl
  have hAlphaInvVal : (((((coord x).2.2)⁻¹ : F) : H) : G) =
      ((((coord x).2.2 : F) : H) : G)⁻¹ := rfl
  have hGammaInvVal : (((((coord x).2.1)⁻¹ : D) : H) : G) =
      ((((coord x).2.1 : D) : H) : G)⁻¹ := rfl
  have hBetaInvVal : (((((coord x).1)⁻¹ : F) : H) : G) =
      ((((coord x).1 : F) : H) : G)⁻¹ := rfl
  have hGammaConjInv :
      s * (((((coord x).2.1)⁻¹ : D) : H) : G) * s =
        ((((coord x).2.1 : D) : H) : G) := by
    simpa [hsinv] using hInverts ((coord x).2.1)⁻¹
  have hGammaMove :
      s * (((((coord x).2.1)⁻¹ : D) : H) : G) =
        ((((coord x).2.1 : D) : H) : G) * s := by
    calc
      s * (((((coord x).2.1)⁻¹ : D) : H) : G) =
          (s * (((((coord x).2.1)⁻¹ : D) : H) : G) * s) * s := by
            rw [mul_assoc, hss, mul_one]
      _ = ((((coord x).2.1 : D) : H) : G) * s := by rw [hGammaConjInv]
  have hcandidate :
      s * (((xInv.1 : F) : H) : G) * s =
        (((candidate.1 : F) : H) : G) *
          (((candidate.2.1 : D) : H) : G) * s *
            (((candidate.2.2 : F) : H) : G) := by
    change s * (((x.1⁻¹ : F) : H) : G) * s =
      (((((coord x).2.2)⁻¹ : F) : H) : G) *
        ((((coord x).2.1 : D) : H) : G) * s *
          (((((coord x).1)⁻¹ : F) : H) : G)
    calc
      s * (((x.1⁻¹ : F) : H) : G) * s =
          (s * (((x.1 : F) : H) : G) * s)⁻¹ := by
            rw [hxInvVal, mul_inv_rev, mul_inv_rev, hsinv]
            group
      _ = (((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))⁻¹ := by
                rw [hcoord]
      _ = (((((coord x).2.2)⁻¹ : F) : H) : G) *
            s * (((((coord x).2.1)⁻¹ : D) : H) : G) *
              (((((coord x).1)⁻¹ : F) : H) : G) := by
                simp only [mul_inv_rev, hAlphaInvVal, hGammaInvVal,
                  hBetaInvVal, hsinv]
                group
      _ = (((((coord x).2.2)⁻¹ : F) : H) : G) *
            (s * (((((coord x).2.1)⁻¹ : D) : H) : G)) *
              (((((coord x).1)⁻¹ : F) : H) : G) := by group
      _ = (((((coord x).2.2)⁻¹ : F) : H) : G) *
            (((((coord x).2.1 : D) : H) : G) * s) *
              (((((coord x).1)⁻¹ : F) : H) : G) := by rw [hGammaMove]
      _ = (((((coord x).2.2)⁻¹ : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              (((((coord x).1)⁻¹ : F) : H) : G) := by group
  have hcandEq : candidate = coord xInv := hunique xInv candidate hcandidate
  constructor
  · simpa [candidate, xInv] using
      (congrArg (fun p : F × D × F => p.1) hcandEq).symm
  constructor
  · simpa [candidate, xInv] using
      (congrArg (fun p : F × D × F => p.2.1) hcandEq).symm
  · simpa [candidate, xInv] using
      (congrArg (fun p : F × D × F => p.2.2) hcandEq).symm

set_option maxHeartbeats 800000 in
private theorem xi1115_conjugate_bruhat_coordinates
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H)
    [MulDistribMulAction D F] [IsMulCommutative D]
    (s : G) (hss : s * s = 1)
    (hInverts :
      ∀ d : D,
        s * (((d : D) : H) : G) * s⁻¹ =
          ((((d⁻¹ : D) : D) : H) : G))
    (hAction :
      ∀ (d : D) (x : F),
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hcoord :
      ∀ x : {x : F // x ≠ 1},
        s * (((x.1 : F) : H) : G) * s =
          ((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (d : D) (x : {x : F // x ≠ 1}) :
    let dx : {x : F // x ≠ 1} :=
      ⟨d • x.1, by
        intro hdx
        apply x.2
        calc
          x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
          _ = d⁻¹ • 1 := by rw [hdx]
          _ = 1 := smul_one d⁻¹⟩
    (coord dx).1 = d⁻¹ • (coord x).1 ∧
      (coord dx).2.1 = d⁻¹ * d⁻¹ * (coord x).2.1 ∧
        (coord dx).2.2 = d⁻¹ • (coord x).2.2 := by
  let dx : {x : F // x ≠ 1} :=
    ⟨d • x.1, by
      intro hdx
      apply x.2
      calc
        x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
        _ = d⁻¹ • 1 := by rw [hdx]
        _ = 1 := smul_one d⁻¹⟩
  let candidate : F × D × F :=
    (d⁻¹ • (coord x).1,
      d⁻¹ * d⁻¹ * (coord x).2.1,
      d⁻¹ • (coord x).2.2)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hdInvVal : (((d⁻¹ : D) : H) : G) =
      (((d : D) : H) : G)⁻¹ := rfl
  have hConjD :
      s * (((d : D) : H) : G) * s =
        (((d⁻¹ : D) : H) : G) := by
    simpa [hsinv] using hInverts d
  have hConjDInv :
      s * (((d⁻¹ : D) : H) : G) * s =
        (((d : D) : H) : G) := by
    simpa [hsinv] using hInverts d⁻¹
  have hSDInvMove :
      s * (((d⁻¹ : D) : H) : G) =
        (((d : D) : H) : G) * s := by
    calc
      s * (((d⁻¹ : D) : H) : G) =
          (s * (((d⁻¹ : D) : H) : G) * s) * s := by
            rw [mul_assoc, hss, mul_one]
      _ = (((d : D) : H) : G) * s := by rw [hConjDInv]
  have hGammaDComm :
      ((((coord x).2.1 : D) : H) : G) * (((d : D) : H) : G) =
        (((d : D) : H) : G) * ((((coord x).2.1 : D) : H) : G) := by
    exact congrArg (fun z : D => (((z : D) : H) : G))
      (mul_comm (coord x).2.1 d)
  have hBetaAction :
      (((d⁻¹ • (coord x).1 : F) : H) : G) =
        (((d⁻¹ : D) : H) : G) * ((((coord x).1 : F) : H) : G) *
          (((d : D) : H) : G) := by
    simpa using hAction d⁻¹ (coord x).1
  have hAlphaAction :
      (((d⁻¹ • (coord x).2.2 : F) : H) : G) =
        (((d⁻¹ : D) : H) : G) * ((((coord x).2.2 : F) : H) : G) *
          (((d : D) : H) : G) := by
    simpa using hAction d⁻¹ (coord x).2.2
  have hGammaCandidate :
      ((((d⁻¹ * d⁻¹ * (coord x).2.1 : D) : D) : H) : G) =
        (((d⁻¹ : D) : H) : G) * (((d⁻¹ : D) : H) : G) *
          ((((coord x).2.1 : D) : H) : G) := rfl
  have hdxVal :
      (((dx.1 : F) : H) : G) =
        (((d : D) : H) : G) * (((x.1 : F) : H) : G) *
          (((d : D) : H) : G)⁻¹ := by
    exact hAction d x.1
  have hconjugated :
      s * (((dx.1 : F) : H) : G) * s =
        (((d⁻¹ : D) : H) : G) *
          (s * (((x.1 : F) : H) : G) * s) *
            (((d : D) : H) : G) := by
    rw [hdxVal]
    calc
      s * ((((d : D) : H) : G) * (((x.1 : F) : H) : G) *
            (((d : D) : H) : G)⁻¹) * s =
          s * (((d : D) : H) : G) * (s * s) *
            (((x.1 : F) : H) : G) * (s * s) *
              (((d⁻¹ : D) : H) : G) * s := by
                rw [hdInvVal, hss]
                group
      _ = (s * (((d : D) : H) : G) * s) *
            (s * (((x.1 : F) : H) : G) * s) *
              (s * (((d⁻¹ : D) : H) : G) * s) := by group
      _ = (((d⁻¹ : D) : H) : G) *
            (s * (((x.1 : F) : H) : G) * s) *
              (((d : D) : H) : G) := by rw [hConjD, hConjDInv]
  have hcandidate :
      s * (((dx.1 : F) : H) : G) * s =
        (((candidate.1 : F) : H) : G) *
          (((candidate.2.1 : D) : H) : G) * s *
            (((candidate.2.2 : F) : H) : G) := by
    rw [hconjugated, hcoord]
    change
      (((d⁻¹ : D) : H) : G) *
          (((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G)) *
            (((d : D) : H) : G) =
        (((d⁻¹ • (coord x).1 : F) : H) : G) *
          ((((d⁻¹ * d⁻¹ * (coord x).2.1 : D) : D) : H) : G) * s *
            (((d⁻¹ • (coord x).2.2 : F) : H) : G)
    rw [hBetaAction, hGammaCandidate, hAlphaAction]
    symm
    calc
      ((((d⁻¹ : D) : H) : G) * ((((coord x).1 : F) : H) : G) *
          (((d : D) : H) : G)) *
          ((((d⁻¹ : D) : H) : G) * (((d⁻¹ : D) : H) : G) *
            ((((coord x).2.1 : D) : H) : G)) * s *
            ((((d⁻¹ : D) : H) : G) * ((((coord x).2.2 : F) : H) : G) *
              (((d : D) : H) : G)) =
        (((d⁻¹ : D) : H) : G) * ((((coord x).1 : F) : H) : G) *
          (((d⁻¹ : D) : H) : G) * ((((coord x).2.1 : D) : H) : G) *
            (s * (((d⁻¹ : D) : H) : G)) *
              ((((coord x).2.2 : F) : H) : G) *
                (((d : D) : H) : G) := by
                  simp only [hdInvVal]
                  group
      _ = (((d⁻¹ : D) : H) : G) * ((((coord x).1 : F) : H) : G) *
          (((d⁻¹ : D) : H) : G) * ((((coord x).2.1 : D) : H) : G) *
            ((((d : D) : H) : G) * s) *
              ((((coord x).2.2 : F) : H) : G) *
                (((d : D) : H) : G) := by rw [hSDInvMove]
      _ = (((d⁻¹ : D) : H) : G) * ((((coord x).1 : F) : H) : G) *
          (((d⁻¹ : D) : H) : G) *
            (((((coord x).2.1 : D) : H) : G) * (((d : D) : H) : G)) *
              s * ((((coord x).2.2 : F) : H) : G) *
                (((d : D) : H) : G) := by group
      _ = (((d⁻¹ : D) : H) : G) * ((((coord x).1 : F) : H) : G) *
          (((d⁻¹ : D) : H) : G) *
            ((((d : D) : H) : G) * ((((coord x).2.1 : D) : H) : G)) *
              s * ((((coord x).2.2 : F) : H) : G) *
                (((d : D) : H) : G) := by rw [hGammaDComm]
      _ = (((d⁻¹ : D) : H) : G) *
          (((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G)) *
            (((d : D) : H) : G) := by
              simp only [hdInvVal]
              group
  have hcandEq : candidate = coord dx := hunique dx candidate hcandidate
  constructor
  · simpa [candidate, dx] using
      (congrArg (fun p : F × D × F => p.1) hcandEq).symm
  constructor
  · simpa [candidate, dx] using
      (congrArg (fun p : F × D × F => p.2.1) hcandEq).symm
  · simpa [candidate, dx] using
      (congrArg (fun p : F × D × F => p.2.2) hcandEq).symm

private theorem xi1115_swap_formula_smul
    {F D T : Type*} [Group F] [Group D] [Group T]
    [MulDistribMulAction D F] [IsMulCommutative D]
    (coord : {x : F // x ≠ 1} → F × D × F)
    (phiF : F →* T) (phiD : D →* T) (w : T)
    (hcompat : ∀ d : D, ∀ x : F,
      phiF (d • x) = phiD d * phiF x * (phiD d)⁻¹)
    (hweyl : ∀ d : D, w * phiD d = phiD d⁻¹ * w)
    (d : D) (x : {x : F // x ≠ 1})
    (dx : {x : F // x ≠ 1})
    (hdx : dx.1 = d • x.1)
    (hcoord : coord dx =
      (d⁻¹ • (coord x).1,
        d⁻¹ * d⁻¹ * (coord x).2.1,
        d⁻¹ • (coord x).2.2))
    (hx : phiF (coord x).1 * phiD (coord x).2.1 * w *
          phiF (coord x).2.2 =
        w * phiF x.1 * w) :
    phiF (coord dx).1 * phiD (coord dx).2.1 * w *
          phiF (coord dx).2.2 =
        w * phiF dx.1 * w := by
  rw [hcoord]
  simp only [hcompat, map_mul, map_inv, inv_inv]
  have hcomm : phiD (coord x).2.1 * (phiD d)⁻¹ =
      (phiD d)⁻¹ * phiD (coord x).2.1 := by
    simpa only [map_mul, map_inv] using
      congrArg phiD (mul_comm (coord x).2.1 d⁻¹)
  have hleft : (phiD d)⁻¹ * w = w * phiD d := by
    simpa using (hweyl d).symm
  rw [hdx, hcompat]
  calc
    (((phiD d)⁻¹ * phiF (coord x).1 * phiD d) *
            ((phiD d)⁻¹ * (phiD d)⁻¹ * phiD (coord x).2.1) * w) *
          ((phiD d)⁻¹ * phiF (coord x).2.2 * phiD d) =
        (phiD d)⁻¹ *
          (phiF (coord x).1 * phiD (coord x).2.1 * w *
            phiF (coord x).2.2) * phiD d := by
      calc
        _ = (phiD d)⁻¹ * phiF (coord x).1 *
            ((phiD d)⁻¹ * phiD (coord x).2.1) * w *
              ((phiD d)⁻¹ * phiF (coord x).2.2 * phiD d) := by group
        _ = (phiD d)⁻¹ * phiF (coord x).1 *
            (phiD (coord x).2.1 * (phiD d)⁻¹) * w *
              ((phiD d)⁻¹ * phiF (coord x).2.2 * phiD d) := by
                rw [← hcomm]
        _ = (phiD d)⁻¹ * phiF (coord x).1 *
            phiD (coord x).2.1 * ((phiD d)⁻¹ * w) *
              ((phiD d)⁻¹ * phiF (coord x).2.2 * phiD d) := by group
        _ = (phiD d)⁻¹ * phiF (coord x).1 *
            phiD (coord x).2.1 * (w * phiD d) *
              ((phiD d)⁻¹ * phiF (coord x).2.2 * phiD d) := by
                rw [hleft]
        _ = (phiD d)⁻¹ *
            (phiF (coord x).1 * phiD (coord x).2.1 * w *
              phiF (coord x).2.2) * phiD d := by
                group
    _ = (phiD d)⁻¹ * (w * phiF x.1 * w) * phiD d := by rw [hx]
    _ = w * (phiD d * phiF x.1 * (phiD d)⁻¹) * w := by
      calc
        _ = ((phiD d)⁻¹ * w) * phiF x.1 * (w * phiD d) := by group
        _ = (w * phiD d) * phiF x.1 * ((phiD d)⁻¹ * w) := by
          rw [hleft, hweyl d]
        _ = _ := by group

set_option maxHeartbeats 800000 in
private theorem xi1115_alpha_bruhat_coordinates
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H)
    [MulDistribMulAction D F]
    (s : G) (hss : s * s = 1)
    (hAction :
      ∀ (d : D) (x : F),
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hcoord :
      ∀ x : {x : F // x ≠ 1},
        s * (((x.1 : F) : H) : G) * s =
          ((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (hAlphaNe :
      ∀ x : {x : F // x ≠ 1}, (coord x).2.2 ≠ 1)
    (x : {x : F // x ≠ 1}) :
    let ax : {x : F // x ≠ 1} := ⟨(coord x).2.2, hAlphaNe x⟩
    (coord ax).1 = (coord x).2.1⁻¹ • (coord x).1⁻¹ ∧
      (coord ax).2.1 = (coord x).2.1⁻¹ ∧
        (coord ax).2.2 = x.1 := by
  let ax : {x : F // x ≠ 1} := ⟨(coord x).2.2, hAlphaNe x⟩
  let candidate : F × D × F :=
    ((coord x).2.1⁻¹ • (coord x).1⁻¹, (coord x).2.1⁻¹, x.1)
  have hGammaInvVal : (((((coord x).2.1)⁻¹ : D) : H) : G) =
      ((((coord x).2.1 : D) : H) : G)⁻¹ := rfl
  have hBetaInvVal : (((((coord x).1)⁻¹ : F) : H) : G) =
      ((((coord x).1 : F) : H) : G)⁻¹ := rfl
  have hactionCandidate :
      (((((coord x).2.1⁻¹ • (coord x).1⁻¹ : F) : F) : H) : G) =
        (((((coord x).2.1)⁻¹ : D) : H) : G) *
          (((((coord x).1)⁻¹ : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) := by
    simpa using hAction (coord x).2.1⁻¹ (coord x).1⁻¹
  have hcandidate :
      s * (((ax.1 : F) : H) : G) * s =
        (((candidate.1 : F) : H) : G) *
          (((candidate.2.1 : D) : H) : G) * s *
            (((candidate.2.2 : F) : H) : G) := by
    change s * (((((coord x).2.2 : F) : F) : H) : G) * s =
      (((((coord x).2.1⁻¹ • (coord x).1⁻¹ : F) : F) : H) : G) *
        (((((coord x).2.1)⁻¹ : D) : H) : G) * s *
          (((x.1 : F) : H) : G)
    simp only [hactionCandidate, hGammaInvVal, hBetaInvVal]
    calc
      s * ((((coord x).2.2 : F) : H) : G) * s =
          (((((coord x).2.1 : D) : H) : G)⁻¹ *
            ((((coord x).1 : F) : H) : G)⁻¹) *
              (((((coord x).1 : F) : H) : G) *
                ((((coord x).2.1 : D) : H) : G) * s *
                  ((((coord x).2.2 : F) : H) : G)) * s := by group
      _ = (((((coord x).2.1 : D) : H) : G)⁻¹ *
            ((((coord x).1 : F) : H) : G)⁻¹) *
              (s * (((x.1 : F) : H) : G) * s) * s := by
                rw [← hcoord]
      _ = (((((coord x).2.1 : D) : H) : G)⁻¹ *
            ((((coord x).1 : F) : H) : G)⁻¹) * s *
              (((x.1 : F) : H) : G) := by
                calc
                  (((((coord x).2.1 : D) : H) : G)⁻¹ *
                      ((((coord x).1 : F) : H) : G)⁻¹) *
                        (s * (((x.1 : F) : H) : G) * s) * s =
                    (((((coord x).2.1 : D) : H) : G)⁻¹ *
                      ((((coord x).1 : F) : H) : G)⁻¹) *
                        (s * (((x.1 : F) : H) : G) * (s * s)) := by group
                  _ = (((((coord x).2.1 : D) : H) : G)⁻¹ *
                      ((((coord x).1 : F) : H) : G)⁻¹) * s *
                        (((x.1 : F) : H) : G) := by rw [hss]; group
      _ = ((((((coord x).2.1 : D) : H) : G)⁻¹ *
            ((((coord x).1 : F) : H) : G)⁻¹ *
              ((((coord x).2.1 : D) : H) : G)) *
                (((((coord x).2.1 : D) : H) : G)⁻¹ * s *
                  (((x.1 : F) : H) : G))) := by group
    all_goals group
  have hcandEq : candidate = coord ax := hunique ax candidate hcandidate
  constructor
  · simpa [candidate, ax] using
      (congrArg (fun p : F × D × F => p.1) hcandEq).symm
  constructor
  · simpa [candidate, ax] using
      (congrArg (fun p : F × D × F => p.2.1) hcandEq).symm
  · simpa [candidate, ax] using
      (congrArg (fun p : F × D × F => p.2.2) hcandEq).symm


set_option maxHeartbeats 800000 in
private theorem xi1115_product_middle_ne_one
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H)
    [MulDistribMulAction D F]
    (s : G) (hss : s * s = 1)
    (hInverts :
      ∀ d : D,
        s * (((d : D) : H) : G) * s⁻¹ =
          ((((d⁻¹ : D) : D) : H) : G))
    (hAction :
      ∀ (d : D) (x : F),
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hcoord :
      ∀ x : {x : F // x ≠ 1},
        s * (((x.1 : F) : H) : G) * s =
          ((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (hAlphaNe :
      ∀ x : {x : F // x ≠ 1}, (coord x).2.2 ≠ 1)
    (x₁ x₂ : {x : F // x ≠ 1})
    (hprod : x₁.1 * x₂.1 ≠ 1) :
    (coord x₁).2.2 * (coord x₂).1 ≠ 1 := by
  let alphaX : {x : F // x ≠ 1} → {x : F // x ≠ 1} :=
    fun y => ⟨(coord y).2.2, hAlphaNe y⟩
  let invX : {x : F // x ≠ 1} → {x : F // x ≠ 1} :=
    fun y => ⟨y.1⁻¹, inv_ne_one.mpr y.2⟩
  have hAlphaCoords (y : {x : F // x ≠ 1}) :
      (coord (alphaX y)).2.2 = y.1 := by
    simpa [alphaX] using
      (xi1115_alpha_bruhat_coordinates H F D s hss hAction coord
        hcoord hunique hAlphaNe y).2.2
  have hAlphaInvolutive (y : {x : F // x ≠ 1}) :
      alphaX (alphaX y) = y := by
    apply Subtype.ext
    exact hAlphaCoords y
  have hInvAlpha (y : {x : F // x ≠ 1}) :
      (coord (invX y)).2.2 = (coord y).1⁻¹ := by
    simpa [invX] using
      (xi1115_inverse_bruhat_coordinates H F D s hss hInverts coord
        hcoord hunique y).2.2
  intro hmiddle
  have hAlphaEq : alphaX x₁ = alphaX (invX x₂) := by
    apply Subtype.ext
    change (coord x₁).2.2 = (coord (invX x₂)).2.2
    calc
      (coord x₁).2.2 = (coord x₂).1⁻¹ :=
        eq_inv_of_mul_eq_one_left hmiddle
      _ = (coord (invX x₂)).2.2 := (hInvAlpha x₂).symm
  have hxEq : x₁ = invX x₂ := by
    calc
      x₁ = alphaX (alphaX x₁) := (hAlphaInvolutive x₁).symm
      _ = alphaX (alphaX (invX x₂)) := congrArg alphaX hAlphaEq
      _ = invX x₂ := hAlphaInvolutive (invX x₂)
  apply hprod
  calc
    x₁.1 * x₂.1 = (invX x₂).1 * x₂.1 := by rw [hxEq]
    _ = x₂.1⁻¹ * x₂.1 := rfl
    _ = 1 := inv_mul_cancel x₂.1

set_option maxHeartbeats 800000 in
private theorem xi1115_product_bruhat_coordinates
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H)
    [MulDistribMulAction D F]
    (s : G) (hss : s * s = 1)
    (hInverts :
      ∀ d : D,
        s * (((d : D) : H) : G) * s⁻¹ =
          ((((d⁻¹ : D) : D) : H) : G))
    (hAction :
      ∀ (d : D) (x : F),
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hcoord :
      ∀ x : {x : F // x ≠ 1},
        s * (((x.1 : F) : H) : G) * s =
          ((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (x₁ x₂ : {x : F // x ≠ 1})
    (hprod : x₁.1 * x₂.1 ≠ 1)
    (hzNe : (coord x₁).2.2 * (coord x₂).1 ≠ 1) :
    let x₁₂ : {x : F // x ≠ 1} := ⟨x₁.1 * x₂.1, hprod⟩
    let z : {x : F // x ≠ 1} :=
      ⟨(coord x₁).2.2 * (coord x₂).1, hzNe⟩
    (coord x₁₂).1 =
        (coord x₁).1 * ((coord x₁).2.1 • (coord z).1) ∧
      (coord x₁₂).2.1 =
          (coord x₁).2.1 * (coord z).2.1 * (coord x₂).2.1 ∧
        (coord x₁₂).2.2 =
          ((coord x₂).2.1 • (coord z).2.2) * (coord x₂).2.2 := by
  let x₁₂ : {x : F // x ≠ 1} := ⟨x₁.1 * x₂.1, hprod⟩
  let z : {x : F // x ≠ 1} :=
    ⟨(coord x₁).2.2 * (coord x₂).1, hzNe⟩
  let candidate : F × D × F :=
    ((coord x₁).1 * ((coord x₁).2.1 • (coord z).1),
      (coord x₁).2.1 * (coord z).2.1 * (coord x₂).2.1,
      ((coord x₂).2.1 • (coord z).2.2) * (coord x₂).2.2)
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hGammaTwoInvVal :
      (((((coord x₂).2.1)⁻¹ : D) : H) : G) =
        ((((coord x₂).2.1 : D) : H) : G)⁻¹ := rfl
  have hConjGammaTwo :
      s * ((((coord x₂).2.1 : D) : H) : G) * s =
        (((((coord x₂).2.1)⁻¹ : D) : H) : G) := by
    simpa [hsinv] using hInverts (coord x₂).2.1
  have hGammaTwoSwap :
      ((((coord x₂).2.1 : D) : H) : G) * s *
          ((((coord x₂).2.1 : D) : H) : G) = s := by
    calc
      ((((coord x₂).2.1 : D) : H) : G) * s *
          ((((coord x₂).2.1 : D) : H) : G) =
        (((((coord x₂).2.1 : D) : H) : G) * s *
          ((((coord x₂).2.1 : D) : H) : G)) * (s * s) := by
            rw [hss, mul_one]
      _ = ((((coord x₂).2.1 : D) : H) : G) *
          (s * ((((coord x₂).2.1 : D) : H) : G) * s) * s := by group
      _ = ((((coord x₂).2.1 : D) : H) : G) *
          (((((coord x₂).2.1)⁻¹ : D) : H) : G) * s := by
            rw [hConjGammaTwo]
      _ = s := by
        simp only [hGammaTwoInvVal]
        group
  have hBetaAction :
      (((((coord x₁).2.1 • (coord z).1 : F) : F) : H) : G) =
        ((((coord x₁).2.1 : D) : H) : G) *
          ((((coord z).1 : F) : H) : G) *
            ((((coord x₁).2.1 : D) : H) : G)⁻¹ := by
    simpa using hAction (coord x₁).2.1 (coord z).1
  have hAlphaAction :
      (((((coord x₂).2.1 • (coord z).2.2 : F) : F) : H) : G) =
        ((((coord x₂).2.1 : D) : H) : G) *
          ((((coord z).2.2 : F) : H) : G) *
            ((((coord x₂).2.1 : D) : H) : G)⁻¹ := by
    simpa using hAction (coord x₂).2.1 (coord z).2.2
  have hBetaCandidate :
      ((((coord x₁).1 * ((coord x₁).2.1 • (coord z).1) : F) : H) : G) =
        ((((coord x₁).1 : F) : H) : G) *
          (((((coord x₁).2.1 • (coord z).1 : F) : F) : H) : G) := rfl
  have hGammaCandidate :
      (((((coord x₁).2.1 * (coord z).2.1 * (coord x₂).2.1 : D) : D) : H) : G) =
        ((((coord x₁).2.1 : D) : H) : G) *
          ((((coord z).2.1 : D) : H) : G) *
            ((((coord x₂).2.1 : D) : H) : G) := rfl
  have hAlphaCandidate :
      (((((coord x₂).2.1 • (coord z).2.2) * (coord x₂).2.2 : F) : H) : G) =
        (((((coord x₂).2.1 • (coord z).2.2 : F) : F) : H) : G) *
          ((((coord x₂).2.2 : F) : H) : G) := rfl
  have hzVal :
      (((z.1 : F) : H) : G) =
        ((((coord x₁).2.2 : F) : H) : G) *
          ((((coord x₂).1 : F) : H) : G) := rfl
  have hxProdVal :
      (((x₁.1 * x₂.1 : F) : H) : G) =
        (((x₁.1 : F) : H) : G) * (((x₂.1 : F) : H) : G) := rfl
  have hSZMove :
      s * (((z.1 : F) : H) : G) =
        (s * (((z.1 : F) : H) : G) * s) * s := by
    calc
      s * (((z.1 : F) : H) : G) =
          (s * (((z.1 : F) : H) : G)) * (s * s) := by
            rw [hss, mul_one]
      _ = (s * (((z.1 : F) : H) : G) * s) * s := by group
  have hcandidate :
      s * (((x₁₂.1 : F) : H) : G) * s =
        (((candidate.1 : F) : H) : G) *
          (((candidate.2.1 : D) : H) : G) * s *
            (((candidate.2.2 : F) : H) : G) := by
    change
      s * (((x₁.1 * x₂.1 : F) : H) : G) * s =
        (((((coord x₁).1 * ((coord x₁).2.1 • (coord z).1) : F) : H) : G) *
          (((((coord x₁).2.1 * (coord z).2.1 * (coord x₂).2.1 : D) : D) : H) : G) *
            s *
              (((((coord x₂).2.1 • (coord z).2.2) * (coord x₂).2.2 : F) : H) : G))
    calc
      s * (((x₁.1 * x₂.1 : F) : H) : G) * s =
          s * (((x₁.1 : F) : H) : G) * (((x₂.1 : F) : H) : G) * s := by
            rw [hxProdVal]; group
      _ = (s * (((x₁.1 : F) : H) : G) * s) *
            (s * (((x₂.1 : F) : H) : G) * s) := by
              calc
                s * (((x₁.1 : F) : H) : G) *
                    (((x₂.1 : F) : H) : G) * s =
                  s * (((x₁.1 : F) : H) : G) * (s * s) *
                    (((x₂.1 : F) : H) : G) * s := by
                      rw [hss]
                      group
                _ = (s * (((x₁.1 : F) : H) : G) * s) *
                    (s * (((x₂.1 : F) : H) : G) * s) := by group
      _ = (((((coord x₁).1 : F) : H) : G) *
            ((((coord x₁).2.1 : D) : H) : G) * s *
              ((((coord x₁).2.2 : F) : H) : G)) *
          (((((coord x₂).1 : F) : H) : G) *
            ((((coord x₂).2.1 : D) : H) : G) * s *
              ((((coord x₂).2.2 : F) : H) : G)) := by
                rw [hcoord, hcoord]
      _ = ((((coord x₁).1 : F) : H) : G) *
          ((((coord x₁).2.1 : D) : H) : G) * s *
            (((z.1 : F) : H) : G) *
              ((((coord x₂).2.1 : D) : H) : G) * s *
                ((((coord x₂).2.2 : F) : H) : G) := by
                  rw [hzVal]
                  group
      _ = ((((coord x₁).1 : F) : H) : G) *
          ((((coord x₁).2.1 : D) : H) : G) *
            (s * (((z.1 : F) : H) : G)) *
              ((((coord x₂).2.1 : D) : H) : G) * s *
                ((((coord x₂).2.2 : F) : H) : G) := by group
      _ = ((((coord x₁).1 : F) : H) : G) *
          ((((coord x₁).2.1 : D) : H) : G) *
            ((s * (((z.1 : F) : H) : G) * s) * s) *
              ((((coord x₂).2.1 : D) : H) : G) * s *
                ((((coord x₂).2.2 : F) : H) : G) := by
                  simpa only [mul_assoc] using
                    congrArg (fun t : G =>
                      ((((coord x₁).1 : F) : H) : G) *
                        ((((coord x₁).2.1 : D) : H) : G) * t *
                          ((((coord x₂).2.1 : D) : H) : G) * s *
                            ((((coord x₂).2.2 : F) : H) : G)) hSZMove
      _ = ((((coord x₁).1 : F) : H) : G) *
          ((((coord x₁).2.1 : D) : H) : G) *
            (((((coord z).1 : F) : H) : G) *
              ((((coord z).2.1 : D) : H) : G) * s *
                ((((coord z).2.2 : F) : H) : G)) * s *
              ((((coord x₂).2.1 : D) : H) : G) * s *
                ((((coord x₂).2.2 : F) : H) : G) := by rw [hcoord]; group
      _ = ((((coord x₁).1 : F) : H) : G) *
          ((((coord x₁).2.1 : D) : H) : G) *
            ((((coord z).1 : F) : H) : G) *
              ((((coord z).2.1 : D) : H) : G) * s *
                ((((coord z).2.2 : F) : H) : G) *
                  (s * ((((coord x₂).2.1 : D) : H) : G) * s) *
                    ((((coord x₂).2.2 : F) : H) : G) := by group
      _ = ((((coord x₁).1 : F) : H) : G) *
          ((((coord x₁).2.1 : D) : H) : G) *
            ((((coord z).1 : F) : H) : G) *
              ((((coord z).2.1 : D) : H) : G) * s *
                ((((coord z).2.2 : F) : H) : G) *
                  (((((coord x₂).2.1)⁻¹ : D) : H) : G) *
                    ((((coord x₂).2.2 : F) : H) : G) := by
                      rw [hConjGammaTwo]
      _ = (((((coord x₁).1 * ((coord x₁).2.1 • (coord z).1) : F) : H) : G) *
          (((((coord x₁).2.1 * (coord z).2.1 * (coord x₂).2.1 : D) : D) : H) : G) *
            s *
              (((((coord x₂).2.1 • (coord z).2.2) * (coord x₂).2.2 : F) : H) : G)) := by
                rw [hBetaCandidate, hGammaCandidate, hAlphaCandidate,
                  hBetaAction, hAlphaAction]
                symm
                calc
                  _ = ((((coord x₁).1 : F) : H) : G) *
                      ((((coord x₁).2.1 : D) : H) : G) *
                        ((((coord z).1 : F) : H) : G) *
                          ((((coord z).2.1 : D) : H) : G) *
                            (((((coord x₂).2.1 : D) : H) : G) * s *
                              ((((coord x₂).2.1 : D) : H) : G)) *
                              ((((coord z).2.2 : F) : H) : G) *
                                ((((coord x₂).2.1 : D) : H) : G)⁻¹ *
                                  ((((coord x₂).2.2 : F) : H) : G) := by group
                  _ = ((((coord x₁).1 : F) : H) : G) *
                      ((((coord x₁).2.1 : D) : H) : G) *
                        ((((coord z).1 : F) : H) : G) *
                          ((((coord z).2.1 : D) : H) : G) * s *
                            ((((coord z).2.2 : F) : H) : G) *
                              ((((coord x₂).2.1 : D) : H) : G)⁻¹ *
                                ((((coord x₂).2.2 : F) : H) : G) := by
                                  rw [hGammaTwoSwap]
  have hcandEq : candidate = coord x₁₂ := hunique x₁₂ candidate hcandidate
  dsimp
  constructor
  · simpa [candidate, x₁₂, z] using
      (congrArg (fun p : F × D × F => p.1) hcandEq).symm
  · constructor
    · simpa [candidate, x₁₂, z] using
        (congrArg (fun p : F × D × F => p.2.1) hcandEq).symm
    · simpa [candidate, x₁₂, z] using
        (congrArg (fun p : F × D × F => p.2.2) hcandEq).symm

private theorem xi1115_structure_special_bruhat_coordinates
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H)
    (s : G) (hss : s * s = 1)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (j g : F) (hjne : j ≠ 1) (hgne : g ≠ 1)
    (hstructure :
      s * (((j : F) : H) : G) * s =
        (((g : F) : H) : G) * s * (((g : F) : H) : G)⁻¹) :
    coord ⟨j, hjne⟩ = (g, 1, g⁻¹) ∧
      coord ⟨g, hgne⟩ = (j, 1, g) := by
  have hjCoord :
      (g, 1, g⁻¹) = coord ⟨j, hjne⟩ := by
    apply hunique
    simpa using hstructure
  have hgs :
      (((g : F) : H) : G) * s =
        s * (((j : F) : H) : G) * s * (((g : F) : H) : G) := by
    calc
      (((g : F) : H) : G) * s =
          ((((g : F) : H) : G) * s * (((g : F) : H) : G)⁻¹) *
            (((g : F) : H) : G) := by group
      _ = (s * (((j : F) : H) : G) * s) *
            (((g : F) : H) : G) := by rw [← hstructure]
  have hgFormula :
      s * (((g : F) : H) : G) * s =
        (((j : F) : H) : G) * s * (((g : F) : H) : G) := by
    calc
      s * (((g : F) : H) : G) * s =
          s * ((((g : F) : H) : G) * s) := by group
      _ = s * (s * (((j : F) : H) : G) * s *
            (((g : F) : H) : G)) := by rw [hgs]
      _ = (((j : F) : H) : G) * s * (((g : F) : H) : G) := by
        calc
          s * (s * (((j : F) : H) : G) * s * (((g : F) : H) : G)) =
              (s * s) * (((j : F) : H) : G) * s * (((g : F) : H) : G) := by group
          _ = (((j : F) : H) : G) * s * (((g : F) : H) : G) := by
            rw [hss, one_mul]
  have hgCoord :
      (j, 1, g) = coord ⟨g, hgne⟩ := by
    apply hunique
    simpa using hgFormula
  exact ⟨hjCoord.symm, hgCoord.symm⟩

private theorem xi1115_structure_inverse_bruhat_coordinate
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H)
    (s : G) (hss : s * s = 1)
    (hInverts :
      ∀ d : D,
        s * (((d : D) : H) : G) * s⁻¹ =
          ((((d⁻¹ : D) : D) : H) : G))
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hcoord :
      ∀ x : {x : F // x ≠ 1},
        s * (((x.1 : F) : H) : G) * s =
          ((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (j g : F) (hjInv : j⁻¹ = j) (hgne : g ≠ 1)
    (hgCoord : coord ⟨g, hgne⟩ = (j, 1, g)) :
    coord ⟨g⁻¹, inv_ne_one.mpr hgne⟩ = (g⁻¹, 1, j) := by
  have hInv := xi1115_inverse_bruhat_coordinates H F D s hss hInverts
    coord hcoord hunique ⟨g, hgne⟩
  rw [hgCoord] at hInv
  apply Prod.ext
  · simpa using hInv.1
  apply Prod.ext
  · simpa using hInv.2.1
  · simpa [hjInv] using hInv.2.2


private theorem xi1115_frobenius_complement_smul_fixed_eq_one
    {H : Type*} [Group H] [Finite H]
    (F D : Subgroup H) [MulDistribMulAction D F]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hAction :
      ∀ (d : D) (x : F),
        ((d • x : F) : H) =
          (d : H) * (x : H) * (d : H)⁻¹)
    (d : D) (hd : d ≠ 1) (x : F) (hfix : d • x = x) :
    x = 1 := by
  by_contra hx
  have hfixH : ((d • x : F) : H) = (x : H) :=
    congrArg Subtype.val hfix
  have hconj : (d : H) * (x : H) * (d : H)⁻¹ = (x : H) :=
    (hAction d x).symm.trans hfixH
  have hcomm : (d : H) * (x : H) = (x : H) * (d : H) := by
    have h := congrArg (fun y : H => y * (d : H)) hconj
    simpa [mul_assoc] using h
  have hdcent :
      (d : H) ∈ Subgroup.centralizer ({(x : H)} : Set H) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hdF : (d : H) ∈ F :=
    xi1115_frobenius_kernel_centralizer_le F D hFrob x hx hdcent
  have hdbot : (d : H) ∈ (⊥ : Subgroup H) :=
    hFrob.2.1.disjoint.le_bot ⟨hdF, d.property⟩
  apply hd
  apply Subtype.ext
  simpa using hdbot

set_option maxHeartbeats 800000 in
private theorem xi1115_structure_conjugate_bruhat_coordinates
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H)
    [MulDistribMulAction D F] [IsMulCommutative D]
    (s : G) (hss : s * s = 1)
    (hInverts :
      ∀ d : D,
        s * (((d : D) : H) : G) * s⁻¹ =
          ((((d⁻¹ : D) : D) : H) : G))
    (hAction :
      ∀ (d : D) (x : F),
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hcoord :
      ∀ x : {x : F // x ≠ 1},
        s * (((x.1 : F) : H) : G) * s =
          ((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (hAlphaNe :
      ∀ x : {x : F // x ≠ 1}, (coord x).2.2 ≠ 1)
    (j g : F) (hjne : j ≠ 1) (hgne : g ≠ 1)
    (hjCoord : coord ⟨j, hjne⟩ = (g, 1, g⁻¹))
    (hgCoord : coord ⟨g, hgne⟩ = (j, 1, g))
    (hgInvCoord :
      coord ⟨g⁻¹, inv_ne_one.mpr hgne⟩ = (g⁻¹, 1, j))
    (h k : D)
    (hmiddle : j * (h • j) = (h * h * k⁻¹) • j)
    (hprod : g⁻¹ * (h⁻¹ • g) ≠ 1) :
    let u : {x : F // x ≠ 1} := ⟨g⁻¹ * (h⁻¹ • g), hprod⟩
    let r : D := h * h * k⁻¹
    (coord u).1 = g⁻¹ * (r⁻¹ • g) ∧
      (coord u).2.1 = r⁻¹ * r⁻¹ * (h * h) ∧
        (coord u).2.2 = (h * h) • (r⁻¹ • g⁻¹) * (h • g) := by
  let x₁ : {x : F // x ≠ 1} := ⟨g⁻¹, inv_ne_one.mpr hgne⟩
  have hx₂ne : h⁻¹ • g ≠ 1 := xi1115_smul_ne_one h⁻¹ hgne
  let x₂ : {x : F // x ≠ 1} := ⟨h⁻¹ • g, hx₂ne⟩
  have hx₂Coords0 :=
    xi1115_conjugate_bruhat_coordinates H F D s hss hInverts hAction
      coord hcoord hunique h⁻¹ ⟨g, hgne⟩
  rw [hgCoord] at hx₂Coords0
  have hx₂Coords :
      coord x₂ = (h • j, h * h, h • g) := by
    apply Prod.ext
    · simpa [x₂] using hx₂Coords0.1
    apply Prod.ext
    · simpa [x₂] using hx₂Coords0.2.1
    · simpa [x₂] using hx₂Coords0.2.2
  have hmiddleNe0 :=
    xi1115_product_middle_ne_one H F D s hss hInverts hAction
      coord hcoord hunique hAlphaNe x₁ x₂ (by
        simpa [x₁, x₂] using hprod)
  have hmiddleNe : j * (h • j) ≠ 1 := by
    rw [hgInvCoord, hx₂Coords] at hmiddleNe0
    simpa [x₁, x₂] using hmiddleNe0
  let t : {x : F // x ≠ 1} := ⟨j * (h • j), hmiddleNe⟩
  let z : {x : F // x ≠ 1} :=
    ⟨(coord x₁).2.2 * (coord x₂).1, hmiddleNe0⟩
  have hzt : z = t := by
    apply Subtype.ext
    dsimp [z, t]
    rw [hgInvCoord, hx₂Coords]
  let r : D := h * h * k⁻¹
  have hrjne : r • j ≠ 1 := xi1115_smul_ne_one r hjne
  have htCoords0 :=
    xi1115_conjugate_bruhat_coordinates H F D s hss hInverts hAction
      coord hcoord hunique r ⟨j, hjne⟩
  rw [hjCoord] at htCoords0
  have htEq : t = ⟨r • j, hrjne⟩ := by
    apply Subtype.ext
    exact hmiddle
  have htCoords :
      coord t = (r⁻¹ • g, r⁻¹ * r⁻¹, r⁻¹ • g⁻¹) := by
    rw [htEq]
    apply Prod.ext
    · simpa using htCoords0.1
    apply Prod.ext
    · simpa using htCoords0.2.1
    · simpa using htCoords0.2.2
  have hzCoords :
      coord z = (r⁻¹ • g, r⁻¹ * r⁻¹, r⁻¹ • g⁻¹) := by
    rw [hzt]
    exact htCoords
  have hproduct :=
    xi1115_product_bruhat_coordinates H F D s hss hInverts hAction
      coord hcoord hunique x₁ x₂ (by
        simpa [x₁, x₂] using hprod) hmiddleNe0
  dsimp only at hproduct ⊢
  rw [hzCoords] at hproduct
  rw [hgInvCoord, hx₂Coords] at hproduct
  simpa [x₁, x₂, r] using hproduct


set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem xi1115_structure_conjugate_family_coordinates
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H)
    [Finite H] [MulDistribMulAction D F] [IsMulCommutative D]
    (hFrob : IsFrobeniusGroupWithKernelComplement F D)
    (hregular : PFAppendixIII.ActionRegularOn D F
      (PFAppendixIII.involutions F))
    (hinvolutions :
      PFAppendixIII.involutions F =
        {x : F | x ∈ Subgroup.center F ∧ x ≠ 1})
    (hActionH :
      ∀ (d : D) (x : F),
        ((d • x : F) : H) =
          (d : H) * (x : H) * (d : H)⁻¹)
    (s : G) (hss : s * s = 1)
    (hInverts :
      ∀ d : D,
        s * (((d : D) : H) : G) * s⁻¹ =
          ((((d⁻¹ : D) : D) : H) : G))
    (hAction :
      ∀ (d : D) (x : F),
        (((d • x : F) : H) : G) =
          (((d : D) : H) : G) * (((x : F) : H) : G) *
            (((d : D) : H) : G)⁻¹)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hcoord :
      ∀ x : {x : F // x ≠ 1},
        s * (((x.1 : F) : H) : G) * s =
          ((((coord x).1 : F) : H) : G) *
            ((((coord x).2.1 : D) : H) : G) * s *
              ((((coord x).2.2 : F) : H) : G))
    (hunique :
      ∀ (x : {x : F // x ≠ 1}) (p : F × D × F),
        s * (((x.1 : F) : H) : G) * s =
            (((p.1 : F) : H) : G) *
              (((p.2.1 : D) : H) : G) * s *
                (((p.2.2 : F) : H) : G) →
          p = coord x)
    (hAlphaNe :
      ∀ x : {x : F // x ≠ 1}, (coord x).2.2 ≠ 1)
    (j g : F) (hjInv : PFAppendixIII.IsInvolution j)
    (hjcenter : j ∈ Subgroup.center F) (hgne : g ≠ 1)
    (hjCoord : coord ⟨j, hjInv.ne_one⟩ = (g, 1, g⁻¹))
    (hgCoord : coord ⟨g, hgne⟩ = (j, 1, g))
    (hgInvCoord :
      coord ⟨g⁻¹, inv_ne_one.mpr hgne⟩ = (g⁻¹, 1, j)) :
    ∀ h : D, h ≠ 1 →
      ∃ (k : D) (hprod : g⁻¹ * (h⁻¹ • g) ≠ 1),
        h⁻¹ • ((h⁻¹ • j) * j) = k⁻¹ • j ∧
          let u : {x : F // x ≠ 1} := ⟨g⁻¹ * (h⁻¹ • g), hprod⟩
          let r : D := h * h * k⁻¹
          (coord u).1 = g⁻¹ * (r⁻¹ • g) ∧
            (coord u).2.1 = r⁻¹ * r⁻¹ * (h * h) ∧
              (coord u).2.2 =
                ((h * h) • (r⁻¹ • g⁻¹)) * (h • g) := by
  intro h hh
  let z : F := (h⁻¹ • j) * j
  have hhjCenter : h⁻¹ • j ∈ Subgroup.center F :=
    (MulEquivClass.apply_mem_center_iff
      (MulDistribMulAction.toMulAut D F h⁻¹)).2 hjcenter
  have hzCenter : z ∈ Subgroup.center F :=
    (Subgroup.center F).mul_mem hhjCenter hjcenter
  have hzNe : z ≠ 1 := by
    intro hz
    have hfix : h⁻¹ • j = j := by
      calc
        h⁻¹ • j = j⁻¹ := eq_inv_of_mul_eq_one_left (by
          simpa [z] using hz)
        _ = j := hjInv.inv_eq_self
    have hinvOne : h⁻¹ = 1 :=
      (hregular.2 j hjInv j hjInv).unique hfix.symm (by simp)
    exact hh (inv_eq_one.mp hinvOne)
  have hzInv : z ∈ PFAppendixIII.involutions F := by
    rw [hinvolutions]
    exact ⟨hzCenter, hzNe⟩
  let c : F := h⁻¹ • z
  have hcInv : c ∈ PFAppendixIII.involutions F :=
    hregular.1 z hzInv h⁻¹
  obtain ⟨k, hk, _huniq⟩ := hregular.2 c hcInv j hjInv
  have hcEq : c = k⁻¹ • j := by
    calc
      c = k⁻¹ • (k • c) := (inv_smul_smul k c).symm
      _ = k⁻¹ • j := by rw [← hk]
  have hmiddle : j * (h • j) = (h * h * k⁻¹) • j := by
    calc
      j * (h • j) = h • z := by
        rw [show z = (h⁻¹ • j) * j by rfl, smul_mul',
          smul_smul, mul_inv_cancel, one_smul]
      _ = (h * h) • c := by
        simp [c, mul_smul]
      _ = (h * h) • (k⁻¹ • j) := by rw [hcEq]
      _ = (h * h * k⁻¹) • j := by
        exact (mul_smul (h * h) k⁻¹ j).symm
  have hprod : g⁻¹ * (h⁻¹ • g) ≠ 1 := by
    intro hprod
    have hfix : h⁻¹ • g = g := (inv_mul_eq_one.mp hprod).symm
    have hgOne :=
      xi1115_frobenius_complement_smul_fixed_eq_one F D hFrob
        hActionH h⁻¹ (inv_ne_one.mpr hh) g hfix
    exact hgne hgOne
  refine ⟨k, hprod, ?_, ?_⟩
  · simpa [c, z] using hcEq
  · exact xi1115_structure_conjugate_bruhat_coordinates H F D s hss
      hInverts hAction coord hcoord hunique hAlphaNe
      j g hjInv.ne_one hgne hjCoord hgCoord hgInvCoord
      h k hmiddle hprod

set_option maxHeartbeats 800000 in
/-- The structure-family beta coordinate cannot be the beta coordinate of a
`D`-translate of `g`.  This is the coordinate contradiction used in
XI.11.12, independent of the fixed-field and conjugacy-class counts. -/
private theorem xi1115_structure_family_not_orbit
    {D P : Type*} [Group D] [Group P] [MulDistribMulAction D P]
    {n : ℕ}
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (eK : D ≃* (PFAppendixIII.BinaryGaloisField n)ˣ)
    (pair : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n → P)
    (hone : pair 0 0 = 1)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w =
        pair (a + b) (z + w + a * theta b))
    (haction : ∀ d a z,
      d • pair a z =
        pair ((eK d : PFAppendixIII.BinaryGaloisField n) * a)
          ((eK d : PFAppendixIII.BinaryGaloisField n) *
            theta (eK d : PFAppendixIII.BinaryGaloisField n) * z))
    (j g : P) (rho : PFAppendixIII.BinaryGaloisField n)
    (hj : j = pair 0 1) (hg : g = pair 1 rho)
    (h k d : D)
    (hcentral :
      h⁻¹ • ((h⁻¹ • j) * j) = k⁻¹ • j)
    (hbeta :
      d⁻¹ • j =
        g⁻¹ * ((h * h * k⁻¹)⁻¹ • g)) :
    False := by
  let K := PFAppendixIII.BinaryGaloisField n
  have hgInv : g⁻¹ = pair 1 (rho + 1) := by
    apply inv_eq_of_mul_eq_one_right
    rw [hg, hmul]
    calc
      pair (1 + 1) (rho + (rho + 1) + 1 * theta 1) =
          pair 0 0 := by
            congr 1
            · exact CharTwo.add_self_eq_zero 1
            · rw [map_one, mul_one]
              calc
                rho + (rho + 1) + 1 =
                    (rho + rho) + (1 + 1) := by abel
                _ = 0 := by simp only [CharTwo.add_self_eq_zero]
      _ = 1 := hone
  have hrInvScalar : (eK ((h * h * k⁻¹)⁻¹) : K) = 1 := by
    rw [hj, hgInv, hg, haction, haction, hmul] at hbeta
    have hfirst := (hinj _ _ _ _ hbeta).1
    have hsum : (1 : K) + (eK ((h * h * k⁻¹)⁻¹ : D) : K) = 0 := by
      simpa only [mul_zero, zero_add, one_mul, mul_one] using hfirst.symm
    exact ((eq_neg_of_add_eq_zero_left hsum).trans
      (CharTwo.neg_eq (eK ((h * h * k⁻¹)⁻¹ : D) : K))).symm
  have hr : h * h * k⁻¹ = 1 := by
    have hrInv : (h * h * k⁻¹)⁻¹ = 1 := by
      apply eK.injective
      apply Units.ext
      simpa using hrInvScalar
    exact inv_eq_one.mp hrInv
  have hk : k = h * h := by
    calc
      k = (h * h * k⁻¹) * k := by rw [hr, one_mul]
      _ = h * h := by group
  let lambda : K := (eK h⁻¹ : K)
  have hlambda : lambda ≠ 0 := (eK h⁻¹).ne_zero
  rw [hj, haction, hmul, haction, haction, hk] at hcentral
  have hsecond := (hinj _ _ _ _ hcentral).2
  have hsq : (eK (h * h)⁻¹ : K) = lambda ^ 2 := by
    simp [lambda, pow_two]
  rw [hsq, map_pow] at hsecond
  simp only [mul_one, mul_zero, map_zero, add_zero] at hsecond
  have hprodZero : lambda * theta lambda = 0 := by
    apply add_right_cancel (b := lambda ^ 2 * theta lambda ^ 2)
    rw [zero_add]
    calc
      lambda * theta lambda + lambda ^ 2 * theta lambda ^ 2 =
          lambda * theta lambda * (lambda * theta lambda + 1) := by ring
      _ = lambda ^ 2 * theta lambda ^ 2 := hsecond
  exact (mul_ne_zero hlambda ((map_ne_zero theta).mpr hlambda)) hprodZero

private def xi1115_bruhatEval
    {G : Type*} [Group G]
    (H : Subgroup G) (F : Subgroup H) (s : G) : H × F → G :=
  fun p => (p.1 : G) * s * (((p.2 : F) : H) : G)

private noncomputable def xi1115_bruhatCoord
    {G : Type*} [Group G]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (x : G) (hx : x ∉ H) : H × F :=
  Classical.choose (hBig x hx)

private theorem xi1115_bruhatCoord_spec
    {G : Type*} [Group G]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (x : G) (hx : x ∉ H) :
    x = xi1115_bruhatEval H F s
      (xi1115_bruhatCoord H F s hBig x hx) :=
  (Classical.choose_spec (hBig x hx)).1

private theorem xi1115_existsUnique_bruhatEval
    {G : Type*} [Group G]
    (H : Subgroup G) (F D : Subgroup H) (s : G)
    (hss : s * s = 1)
    (hAmbient : ∀ x : G,
      x ∈ H ∨ ∃ h₁ h₂ : H, x = (h₁ : G) * s * (h₂ : G))
    (hSplitRight : ∀ h : H, ∃ d : D, ∃ f : F,
      h = D.subtype d * F.subtype f)
    (hSD : ∀ d : D,
      s * (((d : D) : H) : G) = (((d⁻¹ : D) : H) : G) * s)
    (hSwapKernelNotH : ∀ x : F, x ≠ 1 →
      s * (((x : F) : H) : G) * s ∉ H) :
    ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p := by
  intro x hx
  obtain ⟨h₁, h₂, hxEval⟩ := (hAmbient x).resolve_left hx
  obtain ⟨d, f, h₂df⟩ := hSplitRight h₂
  let hleft : H := h₁ * D.subtype d⁻¹
  let p : H × F := (hleft, f)
  have hp : x = xi1115_bruhatEval H F s p := by
    rw [hxEval, h₂df]
    simp only [xi1115_bruhatEval, p, hleft, Subgroup.coe_mul]
    calc
      (h₁ : G) * s *
          ((((d : D) : H) : G) * (((f : F) : H) : G)) =
          (h₁ : G) * (s * (((d : D) : H) : G)) *
            (((f : F) : H) : G) := by group
      _ = (h₁ : G) * ((((d⁻¹ : D) : H) : G) * s) *
            (((f : F) : H) : G) := by rw [hSD]
      _ = ((h₁ : G) * (((d⁻¹ : D) : H) : G)) * s *
            (((f : F) : H) : G) := by group
  refine ⟨p, hp, ?_⟩
  intro q hq
  have heval : xi1115_bruhatEval H F s q =
      xi1115_bruhatEval H F s p := hq.symm.trans hp
  let fdiff : F := q.2 * p.2⁻¹
  have hfdiffVal : ((((fdiff : F) : H) : G)) =
      (((q.2 : F) : H) : G) * (((p.2 : F) : H) : G)⁻¹ := by
    rfl
  have hconjEq :
      s * (((fdiff : F) : H) : G) * s =
        (q.1 : G)⁻¹ * (p.1 : G) := by
    rw [hfdiffVal]
    calc
      s * ((((q.2 : F) : H) : G) * (((p.2 : F) : H) : G)⁻¹) * s =
          (q.1 : G)⁻¹ *
            ((q.1 : G) * s * (((q.2 : F) : H) : G)) *
              (((p.2 : F) : H) : G)⁻¹ * s := by group
      _ = (q.1 : G)⁻¹ *
            ((p.1 : G) * s * (((p.2 : F) : H) : G)) *
              (((p.2 : F) : H) : G)⁻¹ * s := by
                simpa only [xi1115_bruhatEval] using
                  congrArg (fun z : G =>
                    (q.1 : G)⁻¹ * z *
                      (((p.2 : F) : H) : G)⁻¹ * s) heval
      _ = ((q.1 : G)⁻¹ * (p.1 : G)) * (s * s) := by group
      _ = (q.1 : G)⁻¹ * (p.1 : G) := by rw [hss, mul_one]
  have hconjH : s * (((fdiff : F) : H) : G) * s ∈ H := by
    rw [hconjEq]
    exact H.mul_mem (H.inv_mem q.1.property) p.1.property
  have hfdiffOne : fdiff = 1 := by
    by_contra hne
    exact hSwapKernelNotH fdiff hne hconjH
  have hright : q.2 = p.2 := by
    exact mul_inv_eq_one.mp hfdiffOne
  have hleft : q.1 = p.1 := by
    have heval' := heval
    simp only [xi1115_bruhatEval] at heval'
    rw [hright] at heval'
    apply Subtype.ext
    exact mul_right_cancel (mul_right_cancel heval')
  exact Prod.ext hleft hright

private theorem xi1115_bruhatEval_not_mem
    {G : Type*} [Group G]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (hs : s ∉ H) (p : H × F) :
    xi1115_bruhatEval H F s p ∉ H := by
  intro hp
  apply hs
  have hback :
      (p.1 : G)⁻¹ * xi1115_bruhatEval H F s p *
          (((p.2 : F) : H) : G)⁻¹ ∈ H :=
    H.mul_mem
      (H.mul_mem (H.inv_mem p.1.property) hp)
      (H.inv_mem (F.subtype p.2).property)
  have hsEq :
      (p.1 : G)⁻¹ * xi1115_bruhatEval H F s p *
          (((p.2 : F) : H) : G)⁻¹ = s := by
    simp only [xi1115_bruhatEval]
    group
  rw [hsEq] at hback
  exact hback

private noncomputable def xi1115_bruhatTransport
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p) : G → K := by
  classical
  exact fun x => if hx : x ∈ H then phiH ⟨x, hx⟩ else
    let p := xi1115_bruhatCoord H F s hBig x hx
    phiH p.1 * w * phiH (F.subtype p.2)

private theorem xi1115_bruhatTransport_on_H
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (h : H) :
    xi1115_bruhatTransport H F s phiH w hBig (h : G) = phiH h := by
  simp [xi1115_bruhatTransport, h.property]

private theorem xi1115_bruhatTransport_on_eval
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hs : s ∉ H)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (p : H × F) :
    xi1115_bruhatTransport H F s phiH w hBig
        (xi1115_bruhatEval H F s p) =
      phiH p.1 * w * phiH (F.subtype p.2) := by
  classical
  have hpOut : xi1115_bruhatEval H F s p ∉ H :=
    xi1115_bruhatEval_not_mem H F s hs p
  let q := xi1115_bruhatCoord H F s hBig
    (xi1115_bruhatEval H F s p) hpOut
  have hqp : q = p := by
    exact ((Classical.choose_spec
      (hBig (xi1115_bruhatEval H F s p) hpOut)).2 p rfl).symm
  simp only [xi1115_bruhatTransport, hpOut, dite_false]
  change phiH q.1 * w * phiH (F.subtype q.2) = _
  rw [hqp]

private theorem xi1115_bruhatTransport_left_H
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (h : H) (x : G) :
    xi1115_bruhatTransport H F s phiH w hBig ((h : G) * x) =
      phiH h * xi1115_bruhatTransport H F s phiH w hBig x := by
  classical
  by_cases hx : x ∈ H
  · have hhx : (h : G) * x ∈ H := H.mul_mem h.property hx
    let xH : H := ⟨x, hx⟩
    have hprod : (⟨(h : G) * x, hhx⟩ : H) = h * xH := by rfl
    simp only [xi1115_bruhatTransport, hx, hhx, dite_true]
    rw [hprod, map_mul]
  · have hhx : (h : G) * x ∉ H := by
      intro hmem
      apply hx
      have hback : (h⁻¹ : G) * ((h : G) * x) ∈ H :=
        H.mul_mem (H.inv_mem h.property) hmem
      simpa using hback
    let p := xi1115_bruhatCoord H F s hBig x hx
    let q := xi1115_bruhatCoord H F s hBig ((h : G) * x) hhx
    have hp : x = xi1115_bruhatEval H F s p :=
      xi1115_bruhatCoord_spec H F s hBig x hx
    have hq : (h : G) * x = xi1115_bruhatEval H F s q :=
      xi1115_bruhatCoord_spec H F s hBig ((h : G) * x) hhx
    let candidate : H × F := (h * p.1, p.2)
    have hcand : (h : G) * x = xi1115_bruhatEval H F s candidate := by
      rw [hp]
      simp only [xi1115_bruhatEval, candidate, Subgroup.coe_mul]
      group
    have hqp : q = candidate :=
      ((Classical.choose_spec (hBig ((h : G) * x) hhx)).2 candidate hcand).symm
    simp only [xi1115_bruhatTransport, hx, hhx, dite_false]
    change phiH q.1 * w * phiH (F.subtype q.2) =
      phiH h * (phiH p.1 * w * phiH (F.subtype p.2))
    rw [hqp]
    simp only [candidate, map_mul]
    group

private theorem xi1115_bruhatTransport_right_F
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (x : G) (f : F) :
    xi1115_bruhatTransport H F s phiH w hBig
        (x * (((f : F) : H) : G)) =
      xi1115_bruhatTransport H F s phiH w hBig x *
        phiH (F.subtype f) := by
  classical
  by_cases hx : x ∈ H
  · have hxf : x * (((f : F) : H) : G) ∈ H :=
      H.mul_mem hx (F.subtype f).property
    let xH : H := ⟨x, hx⟩
    have hprod :
        (⟨x * (((f : F) : H) : G), hxf⟩ : H) =
          xH * F.subtype f := by rfl
    simp only [xi1115_bruhatTransport, hx, hxf, dite_true]
    rw [hprod, map_mul]
  · have hxf : x * (((f : F) : H) : G) ∉ H := by
      intro hmem
      apply hx
      have hback :
          (x * (((f : F) : H) : G)) *
              (((f : F) : H) : G)⁻¹ ∈ H :=
        H.mul_mem hmem (H.inv_mem (F.subtype f).property)
      simpa using hback
    let p := xi1115_bruhatCoord H F s hBig x hx
    let q := xi1115_bruhatCoord H F s hBig
      (x * (((f : F) : H) : G)) hxf
    have hp : x = xi1115_bruhatEval H F s p :=
      xi1115_bruhatCoord_spec H F s hBig x hx
    let candidate : H × F := (p.1, p.2 * f)
    have hcand :
        x * (((f : F) : H) : G) =
          xi1115_bruhatEval H F s candidate := by
      rw [hp]
      simp only [xi1115_bruhatEval, candidate, Subgroup.coe_mul]
      group
    have hqp : q = candidate :=
      ((Classical.choose_spec
        (hBig (x * (((f : F) : H) : G)) hxf)).2 candidate hcand).symm
    simp only [xi1115_bruhatTransport, hx, hxf, dite_false]
    change phiH q.1 * w * phiH (F.subtype q.2) =
      (phiH p.1 * w * phiH (F.subtype p.2)) * phiH (F.subtype f)
    rw [hqp]
    simp only [candidate, map_mul]
    group

private theorem xi1115_bruhatTransport_swap_F
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hss : s * s = 1) (hww : w * w = 1)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (hSwapKernelNotH : ∀ x : F, x ≠ 1 →
      s * (((x : F) : H) : G) * s ∉ H)
    (hSwapCoordTarget : ∀ (x : F) (hx : x ≠ 1),
      let p := xi1115_bruhatCoord H F s hBig
        (s * (((x : F) : H) : G) * s) (hSwapKernelNotH x hx)
      phiH p.1 * w * phiH (F.subtype p.2) =
        w * phiH (F.subtype x) * w) :
    ∀ x : F,
      xi1115_bruhatTransport H F s phiH w hBig
          (s * (((x : F) : H) : G) * s) =
        w * phiH (F.subtype x) * w := by
  classical
  intro x
  by_cases hx : x = 1
  · subst x
    have hone : s * ((((1 : F) : F) : H) : G) * s = 1 := by
      simpa using hss
    rw [hone]
    calc
      xi1115_bruhatTransport H F s phiH w hBig 1 =
          phiH (1 : H) :=
        xi1115_bruhatTransport_on_H H F s phiH w hBig 1
      _ = w * phiH (F.subtype (1 : F)) * w := by
        simp [hww]
  · have hout := hSwapKernelNotH x hx
    let p := xi1115_bruhatCoord H F s hBig
      (s * (((x : F) : H) : G) * s) hout
    simp only [xi1115_bruhatTransport, hout, dite_false]
    change phiH p.1 * w * phiH (F.subtype p.2) = _
    exact hSwapCoordTarget x hx

private theorem xi1115_bruhatTransport_swap_H
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F D : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hSplitRight : ∀ h : H, ∃ d : D, ∃ f : F,
      h = D.subtype d * F.subtype f)
    (hSD : ∀ d : D,
      s * (((d : D) : H) : G) = (((d⁻¹ : D) : H) : G) * s)
    (hWD : ∀ d : D,
      w * phiH (D.subtype d) = phiH (D.subtype d⁻¹) * w)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (hSwapF : ∀ x : F,
      xi1115_bruhatTransport H F s phiH w hBig
          (s * (((x : F) : H) : G) * s) =
        w * phiH (F.subtype x) * w) :
    ∀ h : H,
      xi1115_bruhatTransport H F s phiH w hBig
          (s * (h : G) * s) =
        w * phiH h * w := by
  intro h
  obtain ⟨d, f, hdf⟩ := hSplitRight h
  have hsource :
      s * (h : G) * s =
        (((d⁻¹ : D) : H) : G) *
          (s * (((f : F) : H) : G) * s) := by
    rw [hdf]
    simp only [Subgroup.coe_mul]
    calc
      s * ((((d : D) : H) : G) * (((f : F) : H) : G)) * s =
          (s * (((d : D) : H) : G)) *
            (((f : F) : H) : G) * s := by group
      _ = ((((d⁻¹ : D) : H) : G) * s) *
            (((f : F) : H) : G) * s := by rw [hSD]
      _ = (((d⁻¹ : D) : H) : G) *
            (s * (((f : F) : H) : G) * s) := by group
  rw [hsource]
  rw [xi1115_bruhatTransport_left_H, hSwapF, hdf, map_mul]
  calc
    phiH (D.subtype d⁻¹) *
          (w * phiH (F.subtype f) * w) =
        (phiH (D.subtype d⁻¹) * w) *
          phiH (F.subtype f) * w := by group
    _ = (w * phiH (D.subtype d)) * phiH (F.subtype f) * w := by
      rw [hWD]
    _ = w * (phiH (D.subtype d) * phiH (F.subtype f)) * w := by group

private theorem xi1115_bruhatTransport_left_s
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F D : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hs : s ∉ H)
    (hSplitRight : ∀ h : H, ∃ d : D, ∃ f : F,
      h = D.subtype d * F.subtype f)
    (hSD : ∀ d : D,
      s * (((d : D) : H) : G) = (((d⁻¹ : D) : H) : G) * s)
    (hWD : ∀ d : D,
      w * phiH (D.subtype d) = phiH (D.subtype d⁻¹) * w)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (hSwapH : ∀ h : H,
      xi1115_bruhatTransport H F s phiH w hBig
          (s * (h : G) * s) =
        w * phiH h * w) :
    ∀ x : G,
      xi1115_bruhatTransport H F s phiH w hBig (s * x) =
        w * xi1115_bruhatTransport H F s phiH w hBig x := by
  classical
  intro x
  by_cases hx : x ∈ H
  · let xH : H := ⟨x, hx⟩
    obtain ⟨d, f, hdf⟩ := hSplitRight xH
    let p : H × F := (D.subtype d⁻¹, f)
    have hsource : s * x = xi1115_bruhatEval H F s p := by
      change s * (xH : G) = _
      rw [hdf]
      simp only [xi1115_bruhatEval, p, Subgroup.coe_mul]
      calc
        s * ((((d : D) : H) : G) * (((f : F) : H) : G)) =
            (s * (((d : D) : H) : G)) * (((f : F) : H) : G) := by group
        _ = ((((d⁻¹ : D) : H) : G) * s) *
              (((f : F) : H) : G) := by rw [hSD]
        _ = (((d⁻¹ : D) : H) : G) * s *
              (((f : F) : H) : G) := by group
    rw [hsource, xi1115_bruhatTransport_on_eval H F s phiH w hs hBig p]
    rw [xi1115_bruhatTransport_on_H H F s phiH w hBig xH, hdf, map_mul]
    calc
      phiH (D.subtype d⁻¹) * w * phiH (F.subtype f) =
          (w * phiH (D.subtype d)) * phiH (F.subtype f) := by
            rw [hWD]
      _ = w * (phiH (D.subtype d) * phiH (F.subtype f)) := by group
  · let p := xi1115_bruhatCoord H F s hBig x hx
    have hp : x = xi1115_bruhatEval H F s p :=
      xi1115_bruhatCoord_spec H F s hBig x hx
    calc
      xi1115_bruhatTransport H F s phiH w hBig (s * x) =
          xi1115_bruhatTransport H F s phiH w hBig
            ((s * (p.1 : G) * s) * (((p.2 : F) : H) : G)) := by
              rw [hp]
              simp only [xi1115_bruhatEval]
              congr 1
              group
      _ = xi1115_bruhatTransport H F s phiH w hBig
              (s * (p.1 : G) * s) * phiH (F.subtype p.2) :=
            xi1115_bruhatTransport_right_F H F s phiH w hBig
              (s * (p.1 : G) * s) p.2
      _ = (w * phiH p.1 * w) * phiH (F.subtype p.2) := by
            rw [hSwapH]
      _ = w * (phiH p.1 * w * phiH (F.subtype p.2)) := by group
      _ = w * xi1115_bruhatTransport H F s phiH w hBig
              (xi1115_bruhatEval H F s p) := by
            rw [xi1115_bruhatTransport_on_eval H F s phiH w hs hBig p]
      _ = w * xi1115_bruhatTransport H F s phiH w hBig x := by rw [hp]

private theorem xi1115_target_bruhatEval_not_range
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H)
    (phiH : H →* K) (w : K)
    (hw : w ∉ phiH.range) (p : H × F) :
    phiH p.1 * w * phiH (F.subtype p.2) ∉ phiH.range := by
  intro hp
  apply hw
  have hback :
      (phiH p.1)⁻¹ *
          (phiH p.1 * w * phiH (F.subtype p.2)) *
            (phiH (F.subtype p.2))⁻¹ ∈ phiH.range :=
    phiH.range.mul_mem
      (phiH.range.mul_mem
        (phiH.range.inv_mem ⟨p.1, rfl⟩) hp)
      (phiH.range.inv_mem ⟨F.subtype p.2, rfl⟩)
  have hbackEq :
      (phiH p.1)⁻¹ *
          (phiH p.1 * w * phiH (F.subtype p.2)) *
            (phiH (F.subtype p.2))⁻¹ = w := by group
  rw [hbackEq] at hback
  exact hback

private theorem xi1115_target_bruhatEval_injective
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H)
    (phiH : H →* K) (w : K)
    (hphiH : Function.Injective phiH)
    (hww : w * w = 1)
    (hSwapTargetNotRange : ∀ x : F, x ≠ 1 →
      w * phiH (F.subtype x) * w ∉ phiH.range) :
    Function.Injective (fun p : H × F =>
      phiH p.1 * w * phiH (F.subtype p.2)) := by
  intro p q hpq
  let fdiff : F := p.2 * q.2⁻¹
  have hfdiffMap :
      phiH (F.subtype fdiff) =
        phiH (F.subtype p.2) * (phiH (F.subtype q.2))⁻¹ := by
    simp only [fdiff, map_mul, map_inv]
  change phiH p.1 * w * phiH (F.subtype p.2) =
    phiH q.1 * w * phiH (F.subtype q.2) at hpq
  have hconjEq :
      w * phiH (F.subtype fdiff) * w =
        (phiH p.1)⁻¹ * phiH q.1 := by
    rw [hfdiffMap]
    calc
      w * (phiH (F.subtype p.2) *
            (phiH (F.subtype q.2))⁻¹) * w =
          (phiH p.1)⁻¹ *
            (phiH p.1 * w * phiH (F.subtype p.2)) *
              (phiH (F.subtype q.2))⁻¹ * w := by group
      _ = (phiH p.1)⁻¹ *
            (phiH q.1 * w * phiH (F.subtype q.2)) *
              (phiH (F.subtype q.2))⁻¹ * w := by rw [hpq]
      _ = (phiH p.1)⁻¹ * phiH q.1 * (w * w) := by group
      _ = (phiH p.1)⁻¹ * phiH q.1 := by rw [hww, mul_one]
  have hconjRange :
      w * phiH (F.subtype fdiff) * w ∈ phiH.range := by
    rw [hconjEq]
    exact phiH.range.mul_mem
      (phiH.range.inv_mem ⟨p.1, rfl⟩) ⟨q.1, rfl⟩
  have hfdiffOne : fdiff = 1 := by
    by_contra hne
    exact hSwapTargetNotRange fdiff hne hconjRange
  have hright : p.2 = q.2 := mul_inv_eq_one.mp hfdiffOne
  have hleft : p.1 = q.1 := by
    apply hphiH
    have hpq' := hpq
    rw [hright] at hpq'
    exact mul_right_cancel (mul_right_cancel hpq')
  exact Prod.ext hleft hright


set_option maxHeartbeats 800000 in
/-- After the structure element has coordinates `(1, 1)`, the three special
orbits and the XI.11.11 structure family cover every nonidentity root
element.  The aligned coordinates make the cover explicit, so no class-count
or fixed-field input is needed. -/
private theorem xi1115_aligned_structure_orbit_cover
    {K F D : Type*} [Field K] [CharP K 2] [Finite K]
    [Group F] [Group D] [MulDistribMulAction D F]
    (theta : K ≃+* K) (pair : K → K → F) (eD : D ≃* Kˣ)
    (hone : pair 0 0 = 1)
    (hsurj : ∀ x : F, ∃ a z, x = pair a z)
    (hmul : ∀ a z b w,
      pair a z * pair b w = pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z = pair
        ((eD d : K) * a)
        ((eD d : K) * theta (eD d : K) * z))
    (hnormInjective : Function.Injective (fun x : K => x * theta x))
    (j g : F) (hj : j = pair 0 1) (hg : g = pair 1 1) :
    ∀ x : F, x ≠ 1 →
      (∃ d : D, d⁻¹ • x = j) ∨
      (∃ d : D, d⁻¹ • x = g) ∨
      (∃ d : D, d⁻¹ • x = g⁻¹) ∨
      ∃ d h : D, h ≠ 1 ∧ d⁻¹ • x = g⁻¹ * (h⁻¹ • g) := by
  have hginv : g⁻¹ = pair 1 0 := by
    have hpairInv : pair 1 0 = (pair 1 1)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [hmul, map_one]
      simpa only [zero_add, mul_one, CharTwo.add_self_eq_zero] using hone
    exact (congrArg Inv.inv hg).trans (by simpa using hpairInv.symm)
  have hnormSurjective : Function.Surjective (fun x : K => x * theta x) :=
    Finite.surjective_of_injective hnormInjective
  intro x hx
  obtain ⟨a, z, rfl⟩ := hsurj x
  by_cases ha : a = 0
  · subst a
    have hz : z ≠ 0 := by
      intro hz
      subst z
      exact hx hone
    obtain ⟨c, hc⟩ := hnormSurjective z⁻¹
    have hc0 : c ≠ 0 := by
      intro hc0
      subst c
      simp only [zero_mul, map_zero] at hc
      exact (inv_ne_zero hz) hc.symm
    let cD : D := eD.symm (Units.mk0 c hc0)
    left
    refine ⟨cD⁻¹, ?_⟩
    rw [hj, inv_inv, hactor]
    apply congrArg₂ pair
    · simp [cD]
    · simp only [cD, MulEquiv.apply_symm_apply, Units.val_mk0]
      change c * theta c = z⁻¹ at hc
      rw [hc, inv_mul_cancel₀ hz]
  · let r : K := a⁻¹ * (theta a)⁻¹ * z
    let aD : D := eD.symm (Units.mk0 a ha)
    have haD : (eD aD : K) = a := by simp [aD]
    have hnormalized : aD⁻¹ • pair a z = pair 1 r := by
      rw [hactor]
      apply congrArg₂ pair
      · simp [haD, ha]
      · simp only [map_inv, Units.val_inv_eq_inv_val, haD, map_inv₀]
        rfl
    by_cases hr0 : r = 0
    · right
      right
      left
      refine ⟨aD, ?_⟩
      rw [hnormalized, hr0, hginv]
    by_cases hr1 : r = 1
    · right
      left
      refine ⟨aD, ?_⟩
      rw [hnormalized, hr1, hg]
    · let t : K := theta.symm r
      have htTheta : theta t = r := by simp [t]
      have ht0 : t ≠ 0 := by
        intro ht0
        apply hr0
        calc
          r = theta t := htTheta.symm
          _ = theta 0 := by rw [ht0]
          _ = 0 := map_zero theta
      have ht1 : t ≠ 1 := by
        intro ht1
        apply hr1
        calc
          r = theta t := htTheta.symm
          _ = theta 1 := by rw [ht1]
          _ = 1 := map_one theta
      have hOneAddT : 1 + t ≠ 0 := by
        intro h
        apply ht1
        apply add_left_cancel (a := (1 : K))
        exact h.trans (CharTwo.add_self_eq_zero (1 : K)).symm
      let lambda : K := t * (1 + t)⁻¹
      have hlambda0 : lambda ≠ 0 :=
        mul_ne_zero ht0 (inv_ne_zero hOneAddT)
      have hOneAddLambda : 1 + lambda ≠ 0 := by
        intro h
        have hlambda1 : lambda = 1 := by
          apply add_left_cancel (a := (1 : K))
          exact h.trans (CharTwo.add_self_eq_zero (1 : K)).symm
        have htEq : t = 1 + t := by
          have hdiv : t / (1 + t) = 1 := by
            simpa [lambda, div_eq_mul_inv] using hlambda1
          simpa using (div_eq_one_iff_eq hOneAddT).mp hdiv
        have hzeroOne : (0 : K) = 1 := by
          calc
            0 = t + t := (CharTwo.add_self_eq_zero t).symm
            _ = (1 + t) + t := congrArg (fun y : K => y + t) htEq
            _ = 1 := by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
        exact zero_ne_one hzeroOne
      have hlambda1 : lambda ≠ 1 := by
        intro h
        exact hOneAddLambda (by rw [h, CharTwo.add_self_eq_zero])
      have hlambdaRatio : lambda * (1 + lambda)⁻¹ = t := by
        dsimp [lambda]
        field_simp [hOneAddT]
        ring_nf
        simp only [CharTwo.two_eq_zero, mul_zero, add_zero, inv_one]
      have hrRatio :
          r = theta lambda * (theta (1 + lambda))⁻¹ := by
        calc
          r = theta t := htTheta.symm
          _ = theta (lambda * (1 + lambda)⁻¹) := by rw [hlambdaRatio]
          _ = theta lambda * (theta (1 + lambda))⁻¹ := by
            simp only [map_mul, map_inv₀]
      let h : D := eD.symm (Units.mk0 lambda⁻¹ (inv_ne_zero hlambda0))
      have heh : (eD h : K) = lambda⁻¹ := by simp [h]
      have hh : h ≠ 1 := by
        intro hh
        have hlambdaInv : lambda⁻¹ = 1 := by
          rw [← heh, hh]
          simp
        exact hlambda1 (inv_eq_one.mp hlambdaInv)
      let c : K := (1 + lambda) * a⁻¹
      have hc0 : c ≠ 0 := mul_ne_zero hOneAddLambda (inv_ne_zero ha)
      let cD : D := eD.symm (Units.mk0 c hc0)
      have hecD : (eD cD : K) = c := by simp [cD]
      have hzFormula : z = a * theta a * r := by
        dsimp [r]
        field_simp [ha, (map_ne_zero theta).mpr ha]
      have hcFirst : c * a = 1 + lambda := by
        dsimp [c]
        field_simp [ha]
      have hcSecond :
          c * theta c * z = lambda * theta lambda + theta lambda := by
        rw [hzFormula]
        dsimp [c]
        simp only [map_mul, map_add, map_one, map_inv₀]
        rw [hrRatio]
        have hthetaOneAdd : theta (1 + lambda) = 1 + theta lambda := by
          simp only [map_add, map_one]
        rw [hthetaOneAdd]
        have hthetaOneAdd0 : 1 + theta lambda ≠ 0 := by
          rw [← hthetaOneAdd]
          exact (map_ne_zero theta).mpr hOneAddLambda
        field_simp [ha, (map_ne_zero theta).mpr ha, hthetaOneAdd0]
        ring_nf
      right
      right
      right
      refine ⟨cD⁻¹, h, hh, ?_⟩
      rw [inv_inv, hactor, hginv, hg, hactor, hmul]
      apply congrArg₂ pair
      · simpa only [hecD, heh, map_inv, Units.val_inv_eq_inv_val,
          inv_inv, mul_one] using hcFirst
      · simpa only [hecD, heh, map_inv, Units.val_inv_eq_inv_val,
          inv_inv, one_mul, mul_one, zero_add] using hcSecond


set_option maxHeartbeats 800000 in
private theorem xi1115_kappa_eq_of_structure_norm
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (hthetaSq : ∀ x, theta (theta x) = x ^ 2)
    (hnormInjective : Function.Injective (fun x : K => x * theta x))
    (lambda kappa : K) (hlambda : lambda ≠ 0) (hlambdaOne : lambda ≠ 1)
    (hn : 1 + lambda ^ 2 * theta lambda ≠ 0)
    (hnorm : kappa⁻¹ * theta kappa⁻¹ =
      lambda ^ 2 * (theta lambda) ^ 2 + lambda * theta lambda) :
    kappa = theta lambda * (1 + lambda) *
        (1 + lambda ^ 2 * theta lambda)⁻¹ + lambda⁻¹ := by
  have hthetaLambda : theta lambda ≠ 0 := (map_ne_zero theta).mpr hlambda
  have hnormLambda : lambda * theta lambda ≠ 1 := by
    intro h
    have hnormEq : lambda * theta lambda = 1 * theta 1 := by simpa using h
    exact hlambdaOne (hnormInjective hnormEq)
  have honeNorm : 1 + lambda * theta lambda ≠ 0 := by
    intro h
    exact hnormLambda
      (((eq_neg_of_add_eq_zero_left h).trans
        (CharTwo.neg_eq (lambda * theta lambda))).symm)
  let candidate : K := theta lambda * (1 + lambda) *
      (1 + lambda ^ 2 * theta lambda)⁻¹ + lambda⁻¹
  have hn' : 1 + theta lambda * lambda ^ 2 ≠ 0 := by
    simpa [mul_comm] using hn
  have hcandidateFormula : candidate =
      (1 + lambda * theta lambda) *
        lambda⁻¹ * (1 + lambda ^ 2 * theta lambda)⁻¹ := by
    dsimp [candidate]
    field_simp [hlambda, hn, hn']
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have hcandidate : candidate ≠ 0 := by
    rw [hcandidateFormula]
    exact mul_ne_zero
      (mul_ne_zero honeNorm (inv_ne_zero hlambda)) (inv_ne_zero hn)
  apply inv_injective
  apply hnormInjective
  change kappa⁻¹ * theta kappa⁻¹ = candidate⁻¹ * theta candidate⁻¹
  rw [hnorm]
  rw [hcandidateFormula]
  simp only [map_mul, map_add, map_one, map_inv₀, hthetaSq, map_pow]
  field_simp [hlambda, hthetaLambda, hn, honeNorm]
  ring_nf
  simp only [CharTwo.two_eq_zero, mul_zero, add_zero]

set_option maxHeartbeats 800000 in
private theorem xi1115_char_two_ovoid_norm_translate
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (hthetaSq : ∀ x : K, theta (theta x) = x ^ 2)
    (lambda : K) :
    (1 + lambda) * (lambda * theta lambda + theta lambda) +
          theta (1 + lambda) * (1 + lambda) ^ 2 +
        theta (lambda * theta lambda + theta lambda) =
      1 + lambda ^ 2 * theta lambda := by
  simp only [map_add, map_one, map_mul, hthetaSq]
  ring_nf at ⊢
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hthree : (3 : K) = 1 := by
    calc
      (3 : K) = 2 + 1 := by norm_num
      _ = 0 + 1 := by rw [htwo]
      _ = 1 := zero_add 1
  have hfour : (4 : K) = 0 := by
    calc
      (4 : K) = 2 + 2 := by norm_num
      _ = 0 + 0 := by rw [htwo]
      _ = 0 := add_zero 0
  simp only [htwo, hthree, hfour, mul_zero, mul_one, add_zero]

set_option maxHeartbeats 800000 in
private theorem xi1115_structure_scalar_identities
    {K : Type*} [Field K] [CharP K 2]
    (theta : K ≃+* K)
    (hthetaSq : ∀ x, theta (theta x) = x ^ 2)
    (lambda kappa : K)
    (hlambda : lambda ≠ 0) (_hlambdaOne : lambda ≠ 1)
    (hn : 1 + lambda ^ 2 * theta lambda ≠ 0)
    (hkappa : kappa = theta lambda * (1 + lambda) *
      (1 + lambda ^ 2 * theta lambda)⁻¹ + lambda⁻¹) :
    let n : K := 1 + lambda ^ 2 * theta lambda
    let t : K := kappa * lambda ^ 2
    let c : K := n⁻¹ * (1 + lambda)
    let d : K := n⁻¹ * (1 + lambda) + c * theta c
    let z : K := lambda * theta lambda + theta lambda
    let e : K := n⁻¹ * z
    let f : K := n⁻¹ * (1 + lambda)
    let u : K := theta n * n⁻¹ ^ 2
    t + 1 = c ∧
      theta t * (t + 1) = d ∧
      kappa ^ 2 * lambda ^ 2 = u ∧
      kappa + lambda⁻¹ = e ∧
      lambda⁻¹ * theta (lambda⁻¹) + kappa * theta (lambda⁻¹) = f := by
  let n : K := 1 + lambda ^ 2 * theta lambda
  let t : K := kappa * lambda ^ 2
  let c : K := n⁻¹ * (1 + lambda)
  let d : K := n⁻¹ * (1 + lambda) + c * theta c
  let z : K := lambda * theta lambda + theta lambda
  let e : K := n⁻¹ * z
  let f : K := n⁻¹ * (1 + lambda)
  let u : K := theta n * n⁻¹ ^ 2
  have hthetaLambda : theta lambda ≠ 0 := (map_ne_zero theta).mpr hlambda
  have hkappa' : kappa = theta lambda * (1 + lambda) * n⁻¹ + lambda⁻¹ := by
    simpa [n] using hkappa
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hthetaN : theta n = 1 + (theta lambda) ^ 2 * lambda ^ 2 := by
    dsimp [n]
    simp only [map_add, map_one, map_mul, map_pow]
    rw [hthetaSq]
  have hthetaNne : theta n ≠ 0 := (map_ne_zero theta).mpr hn
  have ht : t + 1 = c := by
    have hn0 : n ≠ 0 := by simpa [n] using hn
    dsimp [t, c]
    rw [hkappa']
    field_simp [hlambda, hn0]
    dsimp [n]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have hthetaT : theta t = 1 + theta c := by
    have h := congrArg theta ht
    simp only [map_add, map_one] at h
    calc
      theta t = theta t + (1 + 1) := by
        rw [CharTwo.add_self_eq_zero, add_zero]
      _ = (theta t + 1) + 1 := by rw [add_assoc]
      _ = theta c + 1 := by rw [h]
      _ = 1 + theta c := by rw [add_comm]
  have htθ : theta t * (t + 1) = d := by
    rw [ht, hthetaT]
    dsimp [d]
    ring
  have hu : kappa ^ 2 * lambda ^ 2 = u := by
    have hn0 : n ≠ 0 := by simpa [n] using hn
    dsimp [u]
    rw [hkappa']
    rw [hthetaN]
    field_simp [hlambda, hn0, hthetaLambda, hthetaNne]
    dsimp [n]
    ring_nf
    have hfour : (4 : K) = 0 := by
      calc
        (4 : K) = 2 + 2 := by norm_num
        _ = 0 + 0 := by rw [htwo]
        _ = 0 := add_zero 0
    simp only [htwo, hfour, mul_zero, add_zero]
  have hke : kappa + lambda⁻¹ = e := by
    have hn0 : n ≠ 0 := by simpa [n] using hn
    dsimp [e, z]
    rw [hkappa']
    field_simp [hlambda, hn0]
    ring_nf
    simp only [htwo, mul_zero, add_zero]
  have hlast : lambda⁻¹ * theta (lambda⁻¹) +
      kappa * theta (lambda⁻¹) = f := by
    simp only [map_inv₀]
    calc
      lambda⁻¹ * (theta lambda)⁻¹ + kappa * (theta lambda)⁻¹ =
          (kappa + lambda⁻¹) * (theta lambda)⁻¹ := by ring
      _ = e * (theta lambda)⁻¹ := by rw [hke]
      _ = f := by
        dsimp [e, z, f, n]
        field_simp [hthetaLambda]
        ring
  exact ⟨ht, htθ, hu, hke, hlast⟩

set_option maxHeartbeats 1600000 in
private theorem xi1115_structure_swap
    {K F D T : Type*} [Field K] [CharP K 2]
    [Group F] [Group D] [Group T]
    [MulDistribMulAction D F] [IsMulCommutative D]
    (theta : K ≃+* K) (pair : K → K → F) (eD : D ≃* Kˣ)
    (hone : pair 0 0 = 1)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w = pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z = pair
        ((eD d : K) * a)
        ((eD d : K) * theta (eD d : K) * z))
    (hthetaSq : ∀ x, theta (theta x) = x ^ 2)
    (hnormInjective : Function.Injective (fun x : K => x * theta x))
    (j g : F) (hj : j = pair 0 1) (hg : g = pair 1 1)
    (phiF : F →* T) (phiD : D →* T) (w : T)
    (hstd : ∀ (a z : K),
      let n := a * z + theta a * a ^ 2 + theta z
      ∀ hn : n ≠ 0,
        let s := a * theta a + z
        let c := n⁻¹ * s
        let d := n⁻¹ * a + c * theta c
        let e := n⁻¹ * z
        let f := n⁻¹ * a
        let uval := theta n * n⁻¹ ^ 2
        let u := Units.mk0 uval
          (mul_ne_zero ((map_ne_zero theta).2 hn)
            (pow_ne_zero _ (inv_ne_zero hn)))
        phiF (pair c d) * phiD (eD.symm u) * w * phiF (pair e f) =
          w * phiF (pair a z) * w)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (h k : D) (hh : h ≠ 1)
    (hprod : g⁻¹ * (h⁻¹ • g) ≠ 1)
    (hcentral : h⁻¹ • ((h⁻¹ • j) * j) = k⁻¹ • j)
    (hcoord :
      let x : {x : F // x ≠ 1} := ⟨g⁻¹ * (h⁻¹ • g), hprod⟩
      let r : D := h * h * k⁻¹
      (coord x).1 = g⁻¹ * (r⁻¹ • g) ∧
        (coord x).2.1 = r⁻¹ * r⁻¹ * (h * h) ∧
          (coord x).2.2 = ((h * h) • (r⁻¹ • g⁻¹)) * (h • g))
    (hnNe :
      let lambda : K := (eD h : K)⁻¹
      1 + lambda ^ 2 * theta lambda ≠ 0) :
    let x : {x : F // x ≠ 1} := ⟨g⁻¹ * (h⁻¹ • g), hprod⟩
    phiF (coord x).1 * phiD (coord x).2.1 * w * phiF (coord x).2.2 =
      w * phiF x.1 * w := by
  let lambda : K := (eD h : K)⁻¹
  let kappa : K := (eD k : K)
  let r : D := h * h * k⁻¹
  let x : {x : F // x ≠ 1} := ⟨g⁻¹ * (h⁻¹ • g), hprod⟩
  have hlambda : lambda ≠ 0 := inv_ne_zero (eD h).ne_zero
  have hnNe' : 1 + lambda ^ 2 * theta lambda ≠ 0 := by
    simpa only [lambda] using hnNe
  have hlambdaOne : lambda ≠ 1 := by
    intro hlambdaEq
    apply hh
    apply eD.injective
    apply Units.ext
    simpa using inv_eq_one.mp hlambdaEq
  have hginv : g⁻¹ = pair 1 0 := by
    have hpairInv : pair 1 0 = (pair 1 1)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [hmul, map_one]
      (convert hone using 1;
        simp only [zero_add, mul_one, CharTwo.add_self_eq_zero])
    exact (congrArg Inv.inv hg).trans (by simpa using hpairInv.symm)
  have hnorm : kappa⁻¹ * theta kappa⁻¹ =
      lambda ^ 2 * (theta lambda) ^ 2 + lambda * theta lambda := by
    rw [hj, hactor, hmul, hactor, hactor] at hcentral
    have hsecond := (hinj _ _ _ _ hcentral).2
    have hraw :
        lambda * theta lambda * (lambda * theta lambda + 1) =
          kappa⁻¹ * theta kappa⁻¹ := by
      simpa [lambda, kappa] using hsecond
    rw [← hraw]
    ring
  have hkappa := xi1115_kappa_eq_of_structure_norm theta hthetaSq
    hnormInjective lambda kappa hlambda hlambdaOne hnNe' hnorm
  let n : K := 1 + lambda ^ 2 * theta lambda
  let t : K := kappa * lambda ^ 2
  let c : K := n⁻¹ * (1 + lambda)
  let d : K := n⁻¹ * (1 + lambda) + c * theta c
  let z : K := lambda * theta lambda + theta lambda
  let e : K := n⁻¹ * z
  let f := n⁻¹ * (1 + lambda)
  let uval : K := theta n * n⁻¹ ^ 2
  have hscalars := xi1115_structure_scalar_identities theta hthetaSq
    lambda kappa hlambda hlambdaOne (by simpa only [n] using hnNe') hkappa
  dsimp only at hscalars
  have herinv : (eD r⁻¹ : K) = t := by
    simp only [r, map_inv, map_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    dsimp only [t, kappa, lambda]
    field_simp
  have hbeta : g⁻¹ * (r⁻¹ • g) = pair c d := by
    rw [hginv, hg, hactor, hmul, herinv]
    apply congrArg₂ pair
    · simpa only [mul_one, add_comm, c, n, t] using hscalars.1
    · calc
        0 + t * theta t * 1 + 1 * theta (t * 1) =
            theta t * (t + 1) := by ring
        _ = d := by simpa only [d, c, n, t] using hscalars.2.1
  have hgamma : r⁻¹ * r⁻¹ * (h * h) =
      eD.symm (Units.mk0 uval
        (mul_ne_zero ((map_ne_zero theta).2 (by simpa only [n] using hnNe'))
          (pow_ne_zero _ (inv_ne_zero (by simpa only [n] using hnNe'))))) := by
    apply eD.injective
    apply Units.ext
    simp only [MulEquiv.apply_symm_apply, Units.val_mk0]
    have hleft : (eD (r⁻¹ * r⁻¹ * (h * h)) : K) =
        kappa ^ 2 * lambda ^ 2 := by
      simp only [map_mul, Units.val_mul]
      rw [herinv]
      have heh : (eD h : K) = lambda⁻¹ := by simp [lambda]
      rw [heh]
      field_simp [hlambda]
      ring
    rw [hleft]
    simpa only [uval, n] using hscalars.2.2.1
  have hkr : h * h * r⁻¹ = k := by
    dsimp only [r]
    rw [mul_inv_rev]
    simp only [inv_inv]
    calc
      h * h * (k * (h * h)⁻¹) = k * ((h * h) * (h * h)⁻¹) := by
        ac_rfl
      _ = k := by simp
  have halphaAction : (h * h) • (r⁻¹ • g⁻¹) = k • g⁻¹ := by
    rw [← mul_smul, hkr]
  have halpha : ((h * h) • (r⁻¹ • g⁻¹)) * (h • g) = pair e f := by
    rw [halphaAction, hginv, hg, hactor, hactor, hmul]
    apply congrArg₂ pair
    · change kappa * 1 + (eD h : K) * 1 = e
      have heh : (eD h : K) = lambda⁻¹ := by simp [lambda]
      rw [heh]
      simpa only [mul_one, e, z, n] using hscalars.2.2.2.1
    · change kappa * theta kappa * 0 +
          (eD h : K) * theta (eD h : K) * 1 +
            kappa * 1 * theta ((eD h : K) * 1) = f
      have heh : (eD h : K) = lambda⁻¹ := by simp [lambda]
      rw [heh]
      calc
        kappa * theta kappa * 0 + lambda⁻¹ * theta lambda⁻¹ * 1 +
              kappa * 1 * theta (lambda⁻¹ * 1) =
            lambda⁻¹ * theta lambda⁻¹ + kappa * theta lambda⁻¹ := by ring
        _ = f := by simpa only [f, n] using hscalars.2.2.2.2
  have hxpair : x.1 = pair (1 + lambda) z := by
    dsimp only [x]
    rw [hginv, hg, hactor, hmul]
    apply congrArg₂ pair
    · simp [lambda]
    · simp [lambda, z]
  have hcoord' := hcoord
  dsimp only [x, r] at hcoord'
  have hcoordEq : coord x =
      (pair c d,
        eD.symm (Units.mk0 uval
          (mul_ne_zero ((map_ne_zero theta).2 (by simpa only [n] using hnNe'))
            (pow_ne_zero _ (inv_ne_zero (by simpa only [n] using hnNe'))))),
        pair e f) := by
    apply Prod.ext
    · exact hcoord'.1.trans hbeta
    apply Prod.ext
    · exact hcoord'.2.1.trans hgamma
    · exact hcoord'.2.2.trans halpha
  change phiF (coord x).1 * phiD (coord x).2.1 * w *
      phiF (coord x).2.2 = w * phiF x.1 * w
  rw [hcoordEq, hxpair]
  have hswap := hstd (1 + lambda) z
  have hnormValue :
      (1 + lambda) * z + theta (1 + lambda) * (1 + lambda) ^ 2 +
          theta z = n := by
    have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have hthree : (3 : K) = 1 := by
      calc
        (3 : K) = 2 + 1 := by norm_num
        _ = 0 + 1 := by rw [htwo]
        _ = 1 := zero_add 1
    have hfour : (4 : K) = 0 := by
      calc
        (4 : K) = 2 + 2 := by norm_num
        _ = 0 + 0 := by rw [htwo]
        _ = 0 := add_zero 0
    dsimp [z, n]
    simp only [map_add, map_one, map_mul, hthetaSq]
    ring_nf
    simp only [htwo, hthree, hfour, mul_zero, mul_one, add_zero]
  have hsValue :
      (1 + lambda) * theta (1 + lambda) + z = 1 + lambda := by
    dsimp [z]
    simp only [map_add, map_one]
    ring_nf
    simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
  have hswap' := hswap (by rw [hnormValue]; simpa only [n] using hnNe')
  simpa only [hnormValue, hsValue, n, z, c, d, e, f, uval] using hswap'

private theorem xi1115_orbit_cover_propagation
    {F D T : Type*} [Group F] [Group D] [Group T]
    [MulDistribMulAction D F]
    (coord : {x : F // x ≠ 1} → F × D × F)
    (phiF : F →* T) (phiD : D →* T) (w : T)
    (j g : F) (hj : j ≠ 1) (hg : g ≠ 1)
    (hcov : ∀ (d : D) (x : {x : F // x ≠ 1}),
      phiF (coord x).1 * phiD (coord x).2.1 * w *
          phiF (coord x).2.2 = w * phiF x.1 * w →
      let dx : {x : F // x ≠ 1} :=
        ⟨d • x.1, by
          intro h
          apply x.2
          calc
            x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
            _ = d⁻¹ • 1 := by rw [h]
            _ = 1 := smul_one _⟩
      phiF (coord dx).1 * phiD (coord dx).2.1 * w *
          phiF (coord dx).2.2 = w * phiF dx.1 * w)
    (hJ : phiF (coord ⟨j, hj⟩).1 * phiD (coord ⟨j, hj⟩).2.1 * w *
      phiF (coord ⟨j, hj⟩).2.2 = w * phiF j * w)
    (hG : phiF (coord ⟨g, hg⟩).1 * phiD (coord ⟨g, hg⟩).2.1 * w *
      phiF (coord ⟨g, hg⟩).2.2 = w * phiF g * w)
    (hGi : phiF (coord ⟨g⁻¹, inv_ne_one.mpr hg⟩).1 *
      phiD (coord ⟨g⁻¹, inv_ne_one.mpr hg⟩).2.1 * w *
      phiF (coord ⟨g⁻¹, inv_ne_one.mpr hg⟩).2.2 =
        w * phiF g⁻¹ * w)
    (hS : ∀ (h : D), h ≠ 1 →
      ∃ hprod : g⁻¹ * (h⁻¹ • g) ≠ 1,
        phiF (coord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).1 *
            phiD (coord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).2.1 * w *
            phiF (coord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).2.2 =
          w * phiF (g⁻¹ * (h⁻¹ • g)) * w)
    :
    ∀ x : {x : F // x ≠ 1},
      ((∃ d : D, d⁻¹ • x.1 = j) ∨
       (∃ d : D, d⁻¹ • x.1 = g) ∨
       (∃ d : D, d⁻¹ • x.1 = g⁻¹) ∨
       (∃ d h : D, h ≠ 1 ∧
          d⁻¹ • x.1 = g⁻¹ * (h⁻¹ • g))) →
      phiF (coord x).1 * phiD (coord x).2.1 * w * phiF (coord x).2.2 =
        w * phiF x.1 * w := by
  intro x hcover
  have hprop (d : D) (y : {x : F // x ≠ 1})
      (hy : phiF (coord y).1 * phiD (coord y).2.1 * w *
          phiF (coord y).2.2 = w * phiF y.1 * w)
      (heq : d • y.1 = x.1) :
      phiF (coord x).1 * phiD (coord x).2.1 * w *
          phiF (coord x).2.2 = w * phiF x.1 * w := by
    let z : {x : F // x ≠ 1} := ⟨d • y.1, by
      intro h
      apply y.2
      calc
        y.1 = d⁻¹ • (d • y.1) := (inv_smul_smul d y.1).symm
        _ = d⁻¹ • 1 := by rw [h]
        _ = 1 := smul_one _⟩
    have hz : z = x := Subtype.ext heq
    rw [← hz]
    exact hcov d y hy
  rcases hcover with hJx | hGx | hGix | hSx
  · rcases hJx with ⟨d, hd⟩
    apply hprop d ⟨j, hj⟩ hJ
    calc
      d • j = d • (d⁻¹ • x.1) := by rw [hd]
      _ = x.1 := smul_inv_smul d x.1
  · rcases hGx with ⟨d, hd⟩
    apply hprop d ⟨g, hg⟩ hG
    calc
      d • g = d • (d⁻¹ • x.1) := by rw [hd]
      _ = x.1 := smul_inv_smul d x.1
  · rcases hGix with ⟨d, hd⟩
    apply hprop d ⟨g⁻¹, inv_ne_one.mpr hg⟩ hGi
    calc
      d • g⁻¹ = d • (d⁻¹ • x.1) := by rw [hd]
      _ = x.1 := smul_inv_smul d x.1
  · rcases hSx with ⟨d, h, hh, hd⟩
    obtain ⟨hprod, hbase⟩ := hS h hh
    apply hprop d ⟨g⁻¹ * (h⁻¹ • g), hprod⟩ hbase
    calc
      d • (g⁻¹ * (h⁻¹ • g)) =
          d • (d⁻¹ • x.1) := by rw [hd]
      _ = x.1 := smul_inv_smul d x.1

set_option maxHeartbeats 1200000 in
private theorem xi1115_structure_family_not_in_orbit_of_beta_covariance
    {F D : Type*} [Group F] [Group D] [MulDistribMulAction D F]
    {n : ℕ}
    (theta : PFAppendixIII.BinaryGaloisField n ≃+*
      PFAppendixIII.BinaryGaloisField n)
    (pair : PFAppendixIII.BinaryGaloisField n →
      PFAppendixIII.BinaryGaloisField n → F)
    (eD : D ≃* (PFAppendixIII.BinaryGaloisField n)ˣ)
    (hone : pair 0 0 = 1)
    (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
    (hmul : ∀ a z b w,
      pair a z * pair b w = pair (a + b) (z + w + a * theta b))
    (hactor : ∀ d : D, ∀ a z,
      d • pair a z = pair
        ((eD d : PFAppendixIII.BinaryGaloisField n) * a)
        ((eD d : PFAppendixIII.BinaryGaloisField n) *
          theta (eD d : PFAppendixIII.BinaryGaloisField n) * z))
    (j g : F) (rho : PFAppendixIII.BinaryGaloisField n)
    (hj : j = pair 0 1)
    (hg : g = pair 1 rho)
    (coord : {x : F // x ≠ 1} → F × D × F)
    (hgne : g ≠ 1)
    (hSpecial : coord ⟨g, hgne⟩ = (j, 1, g))
    (hcov : ∀ (d : D) (x : {x : F // x ≠ 1}),
      let dx : {x : F // x ≠ 1} :=
        ⟨d • x.1, by
          intro h
          apply x.2
          calc
            x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
            _ = d⁻¹ • 1 := by rw [h]
            _ = 1 := smul_one _⟩
      (coord dx).1 = d⁻¹ • (coord x).1)
    (hFamily : ∀ h : D, h ≠ 1 →
      ∃ k : D, ∃ hprod : g⁻¹ * (h⁻¹ • g) ≠ 1,
        h⁻¹ • ((h⁻¹ • j) * j) = k⁻¹ • j ∧
          (coord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).1 =
            g⁻¹ * ((h * h * k⁻¹)⁻¹ • g)) :
    ∀ h : D, h ≠ 1 →
      g⁻¹ * (h⁻¹ • g) ∉ MulAction.orbit D g := by
  intro h hh
  obtain ⟨k, hprod, hcentral, hbetaFamily⟩ := hFamily h hh
  intro horbit
  obtain ⟨d, hd⟩ := MulAction.mem_orbit_iff.mp horbit
  let x : {x : F // x ≠ 1} :=
    ⟨g⁻¹ * (h⁻¹ • g), hprod⟩
  let dx : {x : F // x ≠ 1} :=
    ⟨d⁻¹ • x.1, by
      intro hx
      apply x.2
      calc
        x.1 = d • (d⁻¹ • x.1) := (smul_inv_smul d x.1).symm
        _ = d • 1 := by rw [hx]
        _ = 1 := smul_one _⟩
  have hdxEq : dx = ⟨g, hgne⟩ := by
    apply Subtype.ext
    dsimp [dx, x]
    rw [← hd]
    exact inv_smul_smul d g
  have hcovd := hcov (d⁻¹) x
  change (coord dx).1 = (d⁻¹)⁻¹ • (coord x).1 at hcovd
  have hbetaOrbit : d⁻¹ • j =
      (coord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).1 := by
    have hbetaEq : j = d •
        (coord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).1 := by
      rw [hdxEq, hSpecial] at hcovd
      simpa only [inv_inv] using hcovd
    rw [hbetaEq]
    exact inv_smul_smul d _
  exact xi1115_structure_family_not_orbit theta eD pair hone hinj hmul
    hactor j g rho hj hg h k d hcentral
    (hbetaOrbit.trans hbetaFamily)


private theorem xi1115_bruhatTransport_injective
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (F : Subgroup H) (s : G)
    (phiH : H →* K) (w : K)
    (hphiH : Function.Injective phiH)
    (hBig : ∀ (x : G), x ∉ H →
      ∃! p : H × F, x = xi1115_bruhatEval H F s p)
    (hTargetBigOut : ∀ p : H × F,
      phiH p.1 * w * phiH (F.subtype p.2) ∉ phiH.range)
    (hTargetBigInj : Function.Injective (fun p : H × F =>
      phiH p.1 * w * phiH (F.subtype p.2))) :
    Function.Injective (xi1115_bruhatTransport H F s phiH w hBig) := by
  classical
  intro x y hxy
  by_cases hx : x ∈ H <;> by_cases hy : y ∈ H
  · have hsub : (⟨x, hx⟩ : H) = ⟨y, hy⟩ := by
      apply hphiH
      simpa [xi1115_bruhatTransport, hx, hy] using hxy
    exact congrArg Subtype.val hsub
  · let p := xi1115_bruhatCoord H F s hBig y hy
    have hpRange :
        phiH p.1 * w * phiH (F.subtype p.2) ∈ phiH.range := by
      refine ⟨⟨x, hx⟩, ?_⟩
      simpa [xi1115_bruhatTransport, hx, hy, p] using hxy
    exact (hTargetBigOut p hpRange).elim
  · let p := xi1115_bruhatCoord H F s hBig x hx
    have hpRange :
        phiH p.1 * w * phiH (F.subtype p.2) ∈ phiH.range := by
      refine ⟨⟨y, hy⟩, ?_⟩
      simpa [xi1115_bruhatTransport, hx, hy, p] using hxy.symm
    exact (hTargetBigOut p hpRange).elim
  · let p := xi1115_bruhatCoord H F s hBig x hx
    let q := xi1115_bruhatCoord H F s hBig y hy
    have hpq : p = q := by
      apply hTargetBigInj
      simpa [xi1115_bruhatTransport, hx, hy, p, q] using hxy
    calc
      x = xi1115_bruhatEval H F s p :=
        xi1115_bruhatCoord_spec H F s hBig x hx
      _ = xi1115_bruhatEval H F s q := by rw [hpq]
      _ = y := (xi1115_bruhatCoord_spec H F s hBig y hy).symm

private theorem xi1115_bruhatHom_of_left_equivariance
    {G K : Type*} [Group G] [Group K]
    (H : Subgroup G) (s : G)
    (phiH : H →* K) (w : K)
    (f : G → K)
    (hfH : ∀ h : H, f (h : G) = phiH h)
    (hfLeftH : ∀ (h : H) (x : G),
      f ((h : G) * x) = phiH h * f x)
    (hfLeftS : ∀ x : G, f (s * x) = w * f x)
    (hBruhat : ∀ x : G,
      x ∈ H ∨ ∃ h₁ h₂ : H, x = (h₁ : G) * s * (h₂ : G))
    (hfInjective : Function.Injective f) :
    ∃ Phi : G →* K,
      Function.Injective Phi ∧
      (∀ h : H, Phi (h : G) = phiH h) ∧
      Phi s = w := by
  have hfOne : f 1 = 1 := by
    simpa using hfH (1 : H)
  have hfMul : ∀ x y : G, f (x * y) = f x * f y := by
    intro x y
    rcases hBruhat x with hxH | ⟨h₁, h₂, rfl⟩
    · let h : H := ⟨x, hxH⟩
      calc
        f (x * y) = phiH h * f y := by simpa [h] using hfLeftH h y
        _ = f x * f y := by rw [hfH h]
    · calc
        f (((h₁ : G) * s * (h₂ : G)) * y) =
            phiH h₁ * f (s * ((h₂ : G) * y)) := by
              rw [mul_assoc, mul_assoc]
              exact hfLeftH h₁ (s * ((h₂ : G) * y))
        _ = phiH h₁ * (w * f ((h₂ : G) * y)) := by
              rw [hfLeftS]
        _ = phiH h₁ * (w * (phiH h₂ * f y)) := by
              rw [hfLeftH]
        _ = (phiH h₁ * (w * phiH h₂)) * f y := by group
        _ = f ((h₁ : G) * s * (h₂ : G)) * f y := by
              congr 1
              calc
                phiH h₁ * (w * phiH h₂) =
                    phiH h₁ * f (s * (h₂ : G)) := by
                      rw [hfLeftS, hfH]
                _ = f ((h₁ : G) * (s * (h₂ : G))) :=
                      (hfLeftH h₁ (s * (h₂ : G))).symm
                _ = f ((h₁ : G) * s * (h₂ : G)) := by rw [mul_assoc]
  let Phi : G →* K :=
    { toFun := f
      map_one' := hfOne
      map_mul' := hfMul }
  refine ⟨Phi, hfInjective, ?_, ?_⟩
  · exact hfH
  · calc
      Phi s = f (s * 1) := by simp [Phi]
      _ = w * f 1 := hfLeftS 1
      _ = w := by rw [hfOne, mul_one]

set_option maxHeartbeats 8000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Suzuki XI.11.15, in the form used by Huppert--Blackburn XI.11.16. -/
public theorem huppert_XI_11_15_suzukiRecognition
    {G : Type u} {Omega : Type v}
    [Group G] [Finite G] [MulAction G Omega] [FaithfulSMul G Omega]
    [Fintype Omega]
    (htwo_transitive : MulAction.IsMultiplyPretransitive G Omega 2)
    (hat_most_two_fixed_points :
      ∀ g : G, g ≠ 1 →
        ∀ a b c : Omega,
          a ≠ b → a ≠ c → b ≠ c →
            ¬ (g • a = a ∧ g • b = b ∧ g • c = c))
    (hno_regular_normal :
      ¬ ∃ R : Subgroup G, R.Normal ∧ R ≠ ⊥ ∧
        ∀ a b : Omega, ∃! r : R, (r : G) • a = b)
    (a b : Omega) (hab : a ≠ b)
    (F : Subgroup (MulAction.stabilizer G a))
    (hFrob : IsFrobeniusGroupWithKernelComplement F
      (MulAction.stabilizer (MulAction.stabilizer G a)
        (⟨b, hab.symm⟩ : SubMulAction.ofStabilizer G a)))
    (hFnoncomm : ¬ IsMulCommutative F)
    (hF2 : IsPGroup 2 F) :
    ∃ m : ℕ, 0 < m ∧
      Nonempty (G ≃* SuzukiMatrixGroup m) := by
  obtain ⟨f, hf, hFcard⟩ :=
    xi1115_kernel_card_twoPower F hFrob.kernel_ne_bot hF2
  let b' : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
  let D := MulAction.stabilizer (MulAction.stabilizer G a) b'
  have hFrobD : IsFrobeniusGroupWithKernelComplement F D := by
    simpa [D, b'] using hFrob
  have hDodd : Odd (Nat.card D) :=
    xi1115_complement_card_odd F D hFrobD hFnoncomm
  have hDZ : IsZGroup D :=
    isZGroup_of_frobenius_complement_of_odd (K := F) (R := D) hFrobD hDodd
  have hDdiv : Nat.card D ∣ Nat.card F - 1 :=
    xi1115_complement_card_dvd_kernel_card_sub_one F D hFrobD
  let n := Fintype.card Omega - 1
  have hdegree : Fintype.card Omega = n + 1 := by
    dsimp [n]
    have hcard : 1 < Fintype.card Omega :=
      Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    omega
  have hFcardN : Nat.card F = n :=
    huppert_blackburn_XI_pointStabilizer_frobeniusKernel_card
      n hdegree htwo_transitive a b hab F hFrob
  have hnPower : n = 2 ^ f := hFcardN.symm.trans hFcard
  have hnEven : Even n := by
    rw [hnPower]
    exact Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hdegreeOdd : Odd (Fintype.card Omega) := by
    rw [hdegree]
    exact hnEven.add_one
  have hdegreeF : Fintype.card Omega = Nat.card F + 1 := by
    calc
      Fintype.card Omega = n + 1 := hdegree
      _ = Nat.card F + 1 := by rw [hFcardN]
  let SharpTriple : Prop :=
    ∀ a b c a' b' c' : Omega,
      a ≠ b → a ≠ c → b ≠ c →
      a' ≠ b' → a' ≠ c' → b' ≠ c' →
      ∃! g : G, g • a = a' ∧ g • b = b' ∧ g • c = c'
  have hnotSharp : ¬ SharpTriple := by
    intro hsharp
    apply hFnoncomm
    rcases
        huppert_blackburn_XI_sharpTriple_kernel_elementaryAbelian
          n hdegree htwo_transitive hsharp a b hab F hFrob with
      ⟨p, k, hp, hk, hnk, hFelem⟩
    exact hFelem.toIsMulCommutative
  have hsimple :
      ∀ N : Subgroup G, N.Normal → N ≠ ⊥ → N = ⊤ :=
    xi1115_simple htwo_transitive hat_most_two_fixed_points
      hno_regular_normal a b hab F hFrob hF2
      hdegreeF hdegreeOdd (by simpa [D, b'] using hDodd)
      (by simpa [D, b'] using hDdiv)
  have hDcyclic : IsCyclic D := by
    simpa [D, b'] using
      xi1115_odd_twoPointStabilizer_isCyclic
        htwo_transitive hat_most_two_fixed_points hsimple
        a b hab F hFrob hDodd
  obtain ⟨s, hssq, hsa, hsb⟩ :=
    xi1115_odd_twoPointStabilizer_exists_swap_involution
      htwo_transitive hat_most_two_fixed_points
      a b hab F hFrob hDodd
  have hsInvertsD :
      ∀ x : D,
        s * (((x : MulAction.stabilizer G a) : G)) * s⁻¹ =
          ((((x⁻¹ : D) : MulAction.stabilizer G a) : G)) := by
    simpa [D, b'] using
      xi1115_odd_twoPointStabilizer_swap_inverts
        htwo_transitive hat_most_two_fixed_points hsimple
        a b hab F hFrob hDodd s hsa hsb
  have hsne : s ≠ 1 := by
    intro hs
    apply hab
    simpa [hs] using hsa
  have hsorder : orderOf s = 2 :=
    orderOf_eq_prime hssq hsne
  have hallInvolutionsConj :
      ∀ t : G, orderOf t = 2 → IsConj t s :=
    xi1115_all_involutions_isConj
      htwo_transitive hdegreeOdd hat_most_two_fixed_points
      hno_regular_normal a b hab s hsorder hsa
  letI : F.Normal := hFrob.normal
  letI : MulDistribMulAction D F :=
    Subgroup.conjMulDistribMulActionOfLeNormalizer D F
      (Subgroup.le_normalizer_of_normal (H := F))
  have hActionData :
      PFAppendixIII.IsSuzukiTwoGroup F ∧
        FaithfulSMul D F ∧
        PFAppendixIII.ActionRegularOn D F
          (PFAppendixIII.involutions F) := by
    simpa [D, b'] using
      xi1115_kernel_suzukiActionData
        htwo_transitive a b hab F hFrob hFnoncomm hF2
        (by simpa [D, b'] using hDcyclic) s hallInvolutionsConj
  obtain ⟨hFSuzuki, hDfaithful, hDregular⟩ := hActionData
  letI : FaithfulSMul D F := hDfaithful
  have hDcardCenter :
      Nat.card D = Nat.card (Subgroup.center F) - 1 :=
    xi1115_actor_card_eq_center_card_sub_one hFSuzuki hDregular
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, hl, hZcard⟩ :=
    IsPGroup.card_center_eq_prime_pow hFcard hf
  have hDcard : Nat.card D = 2 ^ l - 1 := by
    calc
      Nat.card D = Nat.card (Subgroup.center F) - 1 := hDcardCenter
      _ = 2 ^ l - 1 := by rw [hZcard]
  obtain ⟨j, g, hjorder, hgne, hstructure⟩ :=
    xi1115_exists_structureEquation
      htwo_transitive hdegreeOdd hat_most_two_fixed_points
      a b hab F hFrob s hsorder hsa hsb
  have hjInv : PFAppendixIII.IsInvolution j :=
    (orderOf_eq_prime_iff.mp hjorder).symm
  have hinvolutions :=
    (Higman.theorem1_involutions_center hFSuzuki).1
  have hjcenter : j ∈ Subgroup.center F := by
    have hj := (Set.ext_iff.mp hinvolutions (j : F)).mp hjInv
    exact hj.1
  have hjgF : j * g = g * j :=
    (Subgroup.mem_center_iff.mp hjcenter g).symm
  have hjgG :
      (((j : F) : MulAction.stabilizer G a) : G) *
          (((g : F) : MulAction.stabilizer G a) : G) =
        (((g : F) : MulAction.stabilizer G a) : G) *
          (((j : F) : MulAction.stabilizer G a) : G) := by
    simpa using congrArg
      (fun x : F => (((x : F) : MulAction.stabilizer G a) : G)) hjgF
  have hjsOdd : Odd (orderOf
      ((((j : F) : MulAction.stabilizer G a) : G) * s)) :=
    xi1115_structureEquation_product_order_odd
      s
      (((j : F) : MulAction.stabilizer G a) : G)
      (((g : F) : MulAction.stabilizer G a) : G)
      hjgG hstructure
  have hjPower : j ∈ Subgroup.zpowers g :=
    xi1115_structureEquation_power
      htwo_transitive a b hab F hFrob hF2
      s hsorder hsa j g hjorder hgne hjcenter hstructure
  let H0 := MulAction.stabilizer G a
  let phiFG : F →* G := H0.subtype.comp F.subtype
  let Icenter : Subgroup G := (Subgroup.center F).map phiFG
  let Dg : Subgroup G := D.map H0.subtype
  let Bcenter : Subgroup G := Icenter ⊔ Dg
  have hthreeRankOne :
      3 ∣ Nat.card D →
        ∃ M : Subgroup G,
          (M : Set G) = xi1115_rankOneSet Bcenter Icenter s := by
    intro hthree
    obtain ⟨i, hiorder, hself⟩ :=
      xi1115_three_dvd_complement_structure_self
        htwo_transitive hdegreeOdd hat_most_two_fixed_points
        a b hab F hFrob hF2 hdegreeF s hsorder hsa hsb
        (by simpa [D, b'] using hsInvertsD)
        hallInvolutionsConj
        (by simpa [D, b'] using hthree)
    have hss : s * s = 1 := by
      simpa [pow_two] using hssq
    have hsInv : s⁻¹ = s :=
      inv_eq_of_mul_eq_one_right hss
    have hInvertsDG :
        ∀ d : D,
          s * (((d : D) : H0) : G) * s =
            (((d⁻¹ : D) : H0) : G) := by
      intro d
      simpa [H0, hsInv] using hsInvertsD d
    have haction :
        ∀ d : D, ∀ x : F,
          (((d • x : F) : H0) : G) =
            (((d : D) : H0) : G) * (((x : F) : H0) : G) *
              (((d : D) : H0) : G)⁻¹ := by
      intro d x
      have hcoe :=
        Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
          D F d x
      exact congrArg
        (fun q : MulAction.stabilizer G a => (q : G)) hcoe
    have hM :=
      xi1115_center_rankOneSubgroup_of_self
        H0 F D haction hFSuzuki hDregular
        s hss hInvertsDG i hiorder hself
    simpa [H0, phiFG, Icenter, Dg, Bcenter] using hM
  have hIcenter_le_H0 : Icenter ≤ H0 := by
    rintro x ⟨z, hz, rfl⟩
    exact (z : H0).property
  have hDg_le_H0 : Dg ≤ H0 := by
    rintro x ⟨d, hd, rfl⟩
    exact (d : H0).property
  have hBcenter_le_H0 : Bcenter ≤ H0 := by
    exact sup_le hIcenter_le_H0 hDg_le_H0
  have hphiFGInj : Function.Injective phiFG := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact hxy
  have hIcenterCard :
      Nat.card Icenter = Nat.card (Subgroup.center F) := by
    simpa [Icenter] using
      (Subgroup.card_map_of_injective
        (K := Subgroup.center F) hphiFGInj)
  have hDgCard : Nat.card Dg = Nat.card D := by
    simpa only [Dg] using
      (Subgroup.card_map_of_injective
        (K := D) (f := H0.subtype) Subtype.coe_injective)
  have hIcenter_le_Fmap :
      Icenter ≤ F.map H0.subtype := by
    rintro x ⟨z, hzcenter, rfl⟩
    exact ⟨(z : H0), z.property, rfl⟩
  have hFmapDgDisjoint :
      Disjoint (F.map H0.subtype) Dg := by
    simpa [Dg] using
      (Subgroup.disjoint_map
        (f := H0.subtype) Subtype.coe_injective
        hFrobD.isComplement'.disjoint)
  have hIcenterDgDisjoint : Disjoint Icenter Dg :=
    Disjoint.mono hIcenter_le_Fmap le_rfl hFmapDgDisjoint
  have hactionMain :
      ∀ d : D, ∀ x : F,
        (((d • x : F) : H0) : G) =
          (((d : D) : H0) : G) * (((x : F) : H0) : G) *
            (((d : D) : H0) : G)⁻¹ := by
    intro d x
    have hcoe :=
      Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
        D F d x
    exact congrArg
      (fun q : MulAction.stabilizer G a => (q : G)) hcoe
  have hDg_conj_Icenter :
      ∀ h : G, h ∈ Dg →
        ∀ i : G, i ∈ Icenter → h * i * h⁻¹ ∈ Icenter := by
    intro h hh i hi
    rcases hh with ⟨hH, hhD, rfl⟩
    rcases hi with ⟨x, hxZ, rfl⟩
    let d : D := ⟨hH, hhD⟩
    have hdxZ : d • x ∈ Subgroup.center F :=
      (MulEquivClass.apply_mem_center_iff
        (MulDistribMulAction.toMulAut D F d)).2 hxZ
    refine ⟨d • x, hdxZ, ?_⟩
    change (((d • x : F) : H0) : G) =
      (((d : D) : H0) : G) * (((x : F) : H0) : G) *
        (((d : D) : H0) : G)⁻¹
    exact hactionMain d x
  have hDg_normalizes_Icenter :
      Dg ≤ Subgroup.normalizer Icenter := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro i
    constructor
    · exact hDg_conj_Icenter h hh i
    · intro hconj
      have hback :=
        hDg_conj_Icenter h⁻¹ (Dg.inv_mem hh)
          (h * i * h⁻¹) hconj
      have heq :
          h⁻¹ * (h * i * h⁻¹) * (h⁻¹)⁻¹ = i := by
        group
      rw [heq] at hback
      exact hback
  have hBcenterCard :
      Nat.card Bcenter =
        Nat.card Icenter * Nat.card Dg := by
    exact
      xi1115_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        Icenter Dg hDg_normalizes_Icenter hIcenterDgDisjoint
  have hsnotBcenter : s ∉ Bcenter := by
    intro hsB
    have hsfixa : s • a = a := hBcenter_le_H0 hsB
    exact hab (hsfixa.symm.trans hsa)
  have hBcenter_conj_Icenter :
      ∀ x : G, x ∈ Bcenter →
        s⁻¹ * x * s ∈ Icenter → x = 1 := by
    intro x hxB hxI
    have hxfixa : x • a = a := hBcenter_le_H0 hxB
    rcases hxI with ⟨z, hzcenter, hzEq⟩
    have hconjFix : (s⁻¹ * x * s) • a = a := by
      rw [← hzEq]
      change (((z : F) : H0) : G) • a = a
      exact (z : H0).property
    have hxfixb : x • b = b := by
      have hsConj := congrArg (fun y : Omega => s • y) hconjFix
      simpa [mul_smul, hsa] using hsConj
    let xH : H0 := ⟨x, hxfixa⟩
    have hxDmem : xH ∈ D := by
      change xH • b' = b'
      apply Subtype.ext
      exact hxfixb
    let xD : D := ⟨xH, hxDmem⟩
    have hxOrderDvd : orderOf x ∣ Nat.card D := by
      calc
        orderOf x = orderOf xH := by
          exact Subgroup.orderOf_coe xH
        _ = orderOf xD := by
          exact Subgroup.orderOf_coe xD
        _ ∣ Nat.card D := orderOf_dvd_natCard xD
    have hxOdd : Odd (orderOf x) :=
      Odd.of_dvd_nat hDodd hxOrderDvd
    have hxOrderEq : orderOf x = orderOf z := by
      calc
        orderOf x = orderOf (s⁻¹ * x * s) := by
          simpa using ((MulAut.conj s⁻¹).orderOf_eq x).symm
        _ = orderOf (phiFG z) := by rw [hzEq]
        _ = orderOf (z : H0) := by
          change orderOf (((z : F) : H0) : G) = orderOf (z : H0)
          exact Subgroup.orderOf_coe (z : H0)
        _ = orderOf z := Subgroup.orderOf_coe z
    have hcop :
        (orderOf z).Coprime (orderOf x) :=
      hF2.orderOf_coprime hxOdd.coprime_two_left z
    have hselfCop :
        (orderOf x).Coprime (orderOf x) := by
      simpa only [hxOrderEq] using hcop
    have hxOrderOne : orderOf x = 1 :=
      (Nat.coprime_self _).mp hselfCop
    exact orderOf_eq_one_iff.mp hxOrderOne
  have hIcenterCardPow : Nat.card Icenter = 2 ^ l :=
    hIcenterCard.trans hZcard
  have hBcenterCardPow :
      Nat.card Bcenter = 2 ^ l * (2 ^ l - 1) := by
    rw [hBcenterCard, hIcenterCardPow, hDgCard, hDcard]
  have hthreeRankOneCard :
      3 ∣ Nat.card D →
        ∃ M : Subgroup G,
          (M : Set G) = xi1115_rankOneSet Bcenter Icenter s ∧
            Nat.card M =
              (2 ^ l + 1) * 2 ^ l * (2 ^ l - 1) := by
    intro hthree
    obtain ⟨M, hM⟩ := hthreeRankOne hthree
    have hMcard :=
      xi1115_rankOneSet_card_of_conj_intersection
        Bcenter Icenter M s hM le_sup_left hsnotBcenter
        hBcenter_conj_Icenter
    refine ⟨M, hM, ?_⟩
    calc
      Nat.card M =
          Nat.card Bcenter +
            Nat.card Bcenter * Nat.card Icenter := hMcard
      _ = (2 ^ l + 1) * 2 ^ l * (2 ^ l - 1) := by
        rw [hBcenterCardPow, hIcenterCardPow]
        exact xi1115_rank_one_card_arithmetic (2 ^ l)
  have hthreeRankOneSharp :
      3 ∣ Nat.card D →
        ∃ M : Subgroup G,
          (M : Set G) = xi1115_rankOneSet Bcenter Icenter s ∧
          Nat.card M = (2 ^ l + 1) * 2 ^ l * (2 ^ l - 1) ∧
          let O := MulAction.orbit M a
          ∀ x y z x' y' z' : O,
            x ≠ y → x ≠ z → y ≠ z →
              x' ≠ y' → x' ≠ z' → y' ≠ z' →
                ∃! g : M,
                  g • x = x' ∧ g • y = y' ∧ g • z = z' := by
    intro hthree
    obtain ⟨M, hM, hMcard⟩ := hthreeRankOneCard hthree
    have hBcenter_le_M : Bcenter ≤ M := by
      intro x hx
      change x ∈ (M : Set G)
      rw [hM]
      exact Or.inl hx
    have hstab :
        MulAction.stabilizer M a = Bcenter.subgroupOf M := by
      ext x
      constructor
      · intro hx
        change (x : G) ∈ Bcenter
        have hxRank :
            (x : G) ∈ xi1115_rankOneSet Bcenter Icenter s := by
          rw [← hM]
          exact x.property
        rcases hxRank with hxB | ⟨b0, hb0, i, hi, hxi⟩
        · exact hxB
        · have hxfix : (x : G) • a = a := hx
          rw [hxi] at hxfix
          have hifix : i • a = a := hIcenter_le_H0 hi
          have hbfix : b0 • a = a := hBcenter_le_H0 hb0
          have hbmaps : b0 • b = a := by
            simpa [mul_smul, hifix, hsa] using hxfix
          exfalso
          apply hab
          exact (MulAction.toPermHom G Omega b0).injective
            (hbfix.trans hbmaps.symm)
      · intro hx
        change (x : G) • a = a
        exact hBcenter_le_H0 hx
    have hq : 2 ≤ 2 ^ l := by
      have hq' : 1 < 2 ^ l := Nat.one_lt_pow hl.ne' (by norm_num)
      omega
    refine ⟨M, hM, hMcard, ?_⟩
    dsimp
    exact xi1115_rankOneOrbit_sharpTriple
      M Bcenter a (2 ^ l) hBcenter_le_M hstab hMcard
      hBcenterCardPow hq hat_most_two_fixed_points
  have hthreePGL :
      3 ∣ Nat.card D →
        ∃ (M : Subgroup G) (K : Type u)
            (_ : Field K) (_ : Finite K),
          (M : Set G) = xi1115_rankOneSet Bcenter Icenter s ∧
          Nat.card K = 2 ^ l ∧
            Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
    intro hthree
    obtain ⟨M, hM, hMcard, hsharp⟩ := hthreeRankOneSharp hthree
    have hBcenter_le_M : Bcenter ≤ M := by
      intro x hx
      change x ∈ (M : Set G)
      rw [hM]
      exact Or.inl hx
    have hIcenter_le_M : Icenter ≤ M :=
      le_sup_left.trans hBcenter_le_M
    have hDg_le_M : Dg ≤ M :=
      le_sup_right.trans hBcenter_le_M
    have hstab :
        MulAction.stabilizer M a = Bcenter.subgroupOf M := by
      ext x
      constructor
      · intro hx
        change (x : G) ∈ Bcenter
        have hxRank :
            (x : G) ∈ xi1115_rankOneSet Bcenter Icenter s := by
          rw [← hM]
          exact x.property
        rcases hxRank with hxB | ⟨b0, hb0, i, hi, hxi⟩
        · exact hxB
        · have hxfix : (x : G) • a = a := hx
          rw [hxi] at hxfix
          have hifix : i • a = a := hIcenter_le_H0 hi
          have hbfix : b0 • a = a := hBcenter_le_H0 hb0
          have hbmaps : b0 • b = a := by
            simpa [mul_smul, hifix, hsa] using hxfix
          exfalso
          apply hab
          exact (MulAction.toPermHom G Omega b0).injective
            (hbfix.trans hbmaps.symm)
      · intro hx
        change (x : G) • a = a
        exact hBcenter_le_H0 hx
    have hsM : s ∈ M := by
      change s ∈ (M : Set G)
      rw [hM]
      right
      exact ⟨1, Bcenter.one_mem, 1, Icenter.one_mem, by simp⟩
    have hbOrbit : b ∈ MulAction.orbit M a := by
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨s, hsM⟩, hsa⟩
    have hDgMem :
        ∀ x : G, x ∈ Dg ↔ x • a = a ∧ x • b = b := by
      intro x
      simpa [H0, D, b', Dg] using
        (xi1115_twoPointStabilizer_map_mem_iff a b hab x)
    have hIcenterNe : Icenter ≠ ⊥ := by
      intro hbot
      have hone : Nat.card Icenter = 1 := by rw [hbot]; simp
      rw [hIcenterCardPow] at hone
      have htwo : 2 ≤ 2 ^ l := by
        have htwo' : 1 < 2 ^ l := Nat.one_lt_pow hl.ne' (by norm_num)
        omega
      omega
    have hDgNe : Dg ≠ ⊥ := by
      intro hbot
      apply hFrobD.complement_ne_bot
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxDg : ((x : H0) : G) ∈ Dg := ⟨x, hx, rfl⟩
      rw [hbot] at hxDg
      exact Subgroup.mem_bot.mpr
        (Subtype.ext (Subgroup.mem_bot.mp hxDg))
    have hIcenterComm : IsMulCommutative Icenter := by
      dsimp [Icenter]
      infer_instance
    obtain ⟨K, fieldK, finiteK, hKcard, eM⟩ :=
      xi1115_rankOneOrbit_charTwo_pgl
        M Icenter Dg a b hab hIcenter_le_M hDg_le_M
        (by simpa [Bcenter] using hstab) hbOrbit hDgMem
        hDg_normalizes_Icenter hIcenterDgDisjoint
        hIcenterNe hDgNe hIcenterComm hl hIcenterCardPow
        (hDgCard.trans hDcard) hMcard hsharp
        hat_most_two_fixed_points
    exact ⟨M, K, fieldK, finiteK, hM, hKcard, eM⟩
  have hxi108GlobalClassCount :
      (∃ (M : Subgroup G) (K : Type u)
          (_ : Field K) (_ : Finite K),
        (M : Set G) = xi1115_rankOneSet Bcenter Icenter s ∧
        Nat.card K = 2 ^ l ∧
        Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) K)) →
      SharpTriple := by
    set_option maxHeartbeats 800000 in
      rintro ⟨M, K, fieldK, finiteK, hM, hKcard, eM0⟩
      obtain ⟨eM⟩ := eM0
      have hDgFusion : ∀ x y : G,
          x ∈ Dg → y ∈ Dg → x ≠ 1 → y ≠ 1 →
            (IsConj x y ↔ y = x ∨ y = x⁻¹) := by
        have hDgCyclic : IsCyclic Dg := by
          let eD : D ≃* Dg :=
            Subgroup.equivMapOfInjective D H0.subtype H0.subtype_injective
          letI : IsCyclic D := hDcyclic
          exact isCyclic_of_surjective eD eD.surjective
        have hDgComm : IsMulCommutative Dg := by
          letI : IsCyclic Dg := hDgCyclic
          infer_instance
        have hDgMem : ∀ x : G,
            x ∈ Dg ↔ x • a = a ∧ x • b = b := by
          intro x
          simpa [H0, D, b', Dg] using
            (xi1115_twoPointStabilizer_map_mem_iff a b hab x)
        have hsInvertsDg : ∀ x : G, x ∈ Dg →
            s * x * s⁻¹ = x⁻¹ := by
          rintro x ⟨d, hd, rfl⟩
          simpa [H0, D, b'] using hsInvertsD ⟨d, hd⟩
        intro x y hxD hyD hxne hyne
        exact xi1115_twoPointSubgroup_fusion_inverse
          hat_most_two_fixed_points a b hab Dg hDgMem hDgComm
          s hsa hsb hsInvertsDg x y hxD hyD hxne hyne
      let SplitClasses : Set (ConjClasses G) :=
        Set.range fun x : {x : Dg // (x : G) ≠ 1} =>
          ConjClasses.mk (x : G)
      have hDgClassRange :
          Nat.card SplitClasses * 2 = 2 ^ l - 2 := by
        have hDgOdd : Odd (Nat.card Dg) := by
          rw [hDgCard]
          exact hDodd
        calc
          Nat.card SplitClasses * 2 = Nat.card Dg - 1 := by
            simpa [SplitClasses] using
              xi1115_conjClass_range_card_of_fusion_inverse
                Dg hDgOdd hDgFusion
          _ = 2 ^ l - 2 := by rw [hDgCard, hDcard]; omega
      let J := {j : F // PFAppendixIII.IsInvolution j}
      let code : Option J → ConjClasses G
        | none => ConjClasses.mk s
        | some j => ConjClasses.mk
            (s * ((((j : J) : F) : H0) : G))
      have hcodeInjective : Function.Injective code := by
        simpa [J, code, H0] using
          xi1115_stronglyReal_classCode_injective
            htwo_transitive hdegreeOdd hat_most_two_fixed_points
            hno_regular_normal a b hab F hFrob hF2 hFSuzuki
            s hsorder hsa hallInvolutionsConj
      have hcodeRangeCard : Nat.card (Set.range code) = 2 ^ l := by
        have hJcard : Nat.card J = 2 ^ l - 1 := by
          calc
            Nat.card J = Nat.card (Subgroup.center F) - 1 :=
              xi1115_kernel_involution_card hFSuzuki
            _ = 2 ^ l - 1 := by rw [hZcard]
        calc
          Nat.card (Set.range code) = Nat.card (Option J) :=
            Nat.card_range_of_injective hcodeInjective
          _ = Nat.card J + 1 := by
            letI : Fintype J := Fintype.ofFinite _
            simp only [Nat.card_eq_fintype_card, Fintype.card_option]
          _ = 2 ^ l := by
            rw [hJcard]
            exact Nat.sub_add_cancel (Nat.one_le_pow l 2 (by norm_num))
      obtain ⟨A, w, hA_le_M, hAcyclic, hAcard, hwM,
          hwNormalizer, hwNotMem, hwsq, hwInv, hdihedralCard⟩ :
          ∃ (A : Subgroup G) (w : G),
            A ≤ M ∧
            IsCyclic A ∧
            Nat.card A = 2 ^ l + 1 ∧
            w ∈ M ∧
            w ∈ Subgroup.normalizer (A : Set G) ∧
            w ∉ A ∧
            w * w = 1 ∧
            (∀ x : G, x ∈ A → w * x * w⁻¹ = x⁻¹) ∧
            Nat.card (A ⊔ Subgroup.zpowers w : Subgroup G) =
              2 * Nat.card A := by
        obtain ⟨S0, w0, hS0cyclic, hS0card, _hw0Normalizer,
            hw0NotMem, hw0sq, hw0Inv, hcandidateCard, _hsubNormalizer⟩ :=
          xi1115_pgl_charTwo_nonsplitTorus hl hKcard
        let phi : Matrix.ProjGenLinGroup (Fin 2) K →* G :=
          M.subtype.comp eM.symm.toMonoidHom
        have hphiInjective : Function.Injective phi := by
          intro x y hxy
          apply eM.symm.injective
          apply Subtype.ext
          exact hxy
        let A : Subgroup G := S0.map phi
        let w : G := phi w0
        have hAleM : A ≤ M := by
          rintro x ⟨t, ht, rfl⟩
          exact (eM.symm t).property
        have hAcyclic' : IsCyclic A := by
          let eA := Subgroup.equivMapOfInjective S0 phi hphiInjective
          letI : IsCyclic S0 := hS0cyclic
          exact isCyclic_of_surjective eA eA.surjective
        have hAcard' : Nat.card A = 2 ^ l + 1 := by
          calc
            Nat.card A = Nat.card S0 := by
              exact Subgroup.card_map_of_injective hphiInjective
            _ = 2 ^ l + 1 := hS0card
        have hwM' : w ∈ M := (eM.symm w0).property
        have hwsq' : w * w = 1 := by
          simpa [w, phi] using congrArg phi hw0sq
        have hwInv' : ∀ x : G, x ∈ A → w * x * w⁻¹ = x⁻¹ := by
          rintro x ⟨t, ht, rfl⟩
          simpa [w, phi] using congrArg phi (hw0Inv t ht)
        have hwNormalizer' : w ∈ Subgroup.normalizer (A : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro x
          constructor
          · intro hx
            rw [hwInv' x hx]
            exact A.inv_mem hx
          · intro hx
            have hxInv : (w * x * w⁻¹)⁻¹ ∈ A := A.inv_mem hx
            have hback := hwInv' (w * x * w⁻¹) hx
            have hwInvEq : w⁻¹ = w :=
              inv_eq_of_mul_eq_one_right hwsq'
            have heq : w * (w * x * w⁻¹) * w⁻¹ = x := by
              rw [hwInvEq]
              calc
                w * (w * x * w) * w = (w * w) * x * (w * w) := by group
                _ = x := by rw [hwsq']; simp
            have hxEq : x = (w * x * w⁻¹)⁻¹ :=
              heq.symm.trans hback
            rwa [hxEq]
        have hwNotMem' : w ∉ A := by
          rintro ⟨t, ht, htw⟩
          apply hw0NotMem
          have htEq : t = w0 := hphiInjective (by simpa [w] using htw)
          simpa [htEq] using ht
        have hmapSup :
            (S0 ⊔ Subgroup.zpowers w0).map phi =
              A ⊔ Subgroup.zpowers w := by
          rw [Subgroup.map_sup, MonoidHom.map_zpowers]
        have hdihedralCard' :
            Nat.card (A ⊔ Subgroup.zpowers w : Subgroup G) =
              2 * Nat.card A := by
          calc
            Nat.card (A ⊔ Subgroup.zpowers w : Subgroup G) =
                Nat.card ((S0 ⊔ Subgroup.zpowers w0).map phi) := by
                  rw [hmapSup]
            _ = Nat.card (S0 ⊔ Subgroup.zpowers w0 :
                Subgroup (Matrix.ProjGenLinGroup (Fin 2) K)) :=
              Subgroup.card_map_of_injective hphiInjective
            _ = 2 * Nat.card S0 := hcandidateCard
            _ = 2 * Nat.card A := by
              change 2 * Nat.card S0 = 2 * Nat.card (S0.map phi)
              rw [Subgroup.card_map_of_injective hphiInjective]
        exact ⟨A, w, hAleM, hAcyclic', hAcard', hwM', hwNormalizer',
          hwNotMem', hwsq', hwInv', hdihedralCard'⟩
      let NonsplitClasses : Set (ConjClasses G) :=
        Set.range fun x : {x : A // (x : G) ≠ 1} =>
          ConjClasses.mk (x : G)
      have hCodeRepresentativesInM : ∀ o : Option J,
          code o = ConjClasses.mk s ∨
            ∃ x : G, x ∈ M ∧ x ^ 2 ≠ 1 ∧
              PFAppendixIII.IsStronglyReal x ∧
              code o = ConjClasses.mk x := by
        intro o
        cases o with
        | none => exact Or.inl rfl
        | some j0 =>
            right
            let jG : G := ((((j0 : J) : F) : H0) : G)
            let x : G := s * jG
            have hss : s * s = 1 := by
              simpa [pow_two] using hssq
            have hjorder : orderOf (j0 : F) = 2 :=
              orderOf_eq_prime j0.property.sq_eq_one j0.property.ne_one
            have hjcenter : (j0 : F) ∈ Subgroup.center F := by
              have hinv := (Higman.theorem1_involutions_center hFSuzuki).1
              exact ((Set.ext_iff.mp hinv (j0 : F)).mp j0.property).1
            have hjI : jG ∈ Icenter := by
              exact ⟨(j0 : F), hjcenter, rfl⟩
            have hxM : x ∈ M := by
              change x ∈ (M : Set G)
              rw [hM]
              right
              exact ⟨1, Bcenter.one_mem, jG, hjI, by simp [x]⟩
            have hxsq : x ^ 2 ≠ 1 := by
              simpa [x, jG] using
                xi1115_swap_mul_kernelInvolution_sq_ne_one
                  htwo_transitive a b hab F hFrob s hsa hss
                  (j0 : F) hjorder
            have hjGInv : PFAppendixIII.IsInvolution jG := by
              refine ⟨?_, ?_⟩
              · intro hjone
                apply j0.property.ne_one
                apply Subtype.ext
                apply Subtype.ext
                exact hjone
              · simpa [jG] using congrArg
                  (fun z : F => (((z : F) : H0) : G))
                  j0.property.sq_eq_one
            have hsInv : PFAppendixIII.IsInvolution s :=
              (orderOf_eq_prime_iff.mp hsorder).symm
            exact ⟨x, hxM, hxsq, ⟨s, jG, hsInv, hjGInv, rfl⟩, rfl⟩
      obtain ⟨P1, U1, S1, hP1, hP1card, hU1cyclic, hU1card,
          hS1cyclic, hS1card, hPartitionM⟩ :
          ∃ P U S : Subgroup M,
            IsPGroup 2 P ∧
            Nat.card P = 2 ^ l ∧
            IsCyclic U ∧ Nat.card U = 2 ^ l - 1 ∧
            IsCyclic S ∧ Nat.card S = 2 ^ l + 1 ∧
            ∀ x : M, x ≠ 1 →
              ∃! T : Subgroup M,
                x ∈ T ∧
                  ((∃ g, T = P.map (MulAut.conj g).toMonoidHom) ∨
                   (∃ g, T = U.map (MulAut.conj g).toMonoidHom) ∨
                   (∃ g, T = S.map (MulAut.conj g).toMonoidHom)) := by
        exact xi1115_pgl_charTwo_threeFamilyPartition hl hKcard eM
      have hSplitFamilyToDg : ∀ x : M, x ≠ 1 →
          (∃ T : Subgroup M, x ∈ T ∧
            ∃ g, T = U1.map (MulAut.conj g).toMonoidHom) →
          ∃ y : Dg, IsConj ((x : M) : G) (y : G) := by
        have hBcenter_le_M : Bcenter ≤ M := by
          intro z hz
          change z ∈ (M : Set G)
          rw [hM]
          exact Or.inl hz
        have hDg_le_M : Dg ≤ M := le_sup_right.trans hBcenter_le_M
        let DM : Subgroup M := Dg.subgroupOf M
        have hDgCyclic : IsCyclic Dg := by
          let eD : D ≃* Dg :=
            Subgroup.equivMapOfInjective D H0.subtype H0.subtype_injective
          letI : IsCyclic D := hDcyclic
          exact isCyclic_of_surjective eD eD.surjective
        have hDMCyclic : IsCyclic DM := by
          let eDM := Subgroup.subgroupOfEquivOfLe hDg_le_M
          letI : IsCyclic Dg := hDgCyclic
          exact isCyclic_of_surjective eDM.symm eDM.symm.surjective
        have hDMcard : Nat.card DM = 2 ^ l - 1 := by
          calc
            Nat.card DM = Nat.card Dg :=
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDg_le_M).toEquiv
            _ = Nat.card D := hDgCard
            _ = 2 ^ l - 1 := hDcard
        have hDMne : DM ≠ ⊥ := by
          rw [← Subgroup.one_lt_card_iff_ne_bot, hDMcard]
          have hDone : 1 < Nat.card D :=
            (Subgroup.one_lt_card_iff_ne_bot D).2 hFrobD.complement_ne_bot
          rwa [hDcard] at hDone
        have hqEven : Even (2 ^ l) :=
          Nat.even_pow.mpr ⟨even_two, hl.ne'⟩
        have hqSubOdd : Odd (2 ^ l - 1) :=
          Nat.Even.sub_odd (pow_pos (by norm_num : 0 < (2 : ℕ)) l)
            hqEven odd_one
        have hPredQ : Nat.Coprime (2 ^ l - 1) (2 ^ l) :=
          ((Nat.coprime_self_sub_right
            (Nat.one_le_pow l 2 (by norm_num))).mpr
              (Nat.coprime_one_right (2 ^ l))).symm
        have hPredSucc : Nat.Coprime (2 ^ l - 1) (2 ^ l + 1) := by
          have hcop : Nat.Coprime (2 ^ l - 1) ((2 ^ l - 1) + 2) :=
            (Nat.coprime_self_add_right).mpr hqSubOdd.coprime_two_right
          have heq : (2 ^ l - 1) + 2 = 2 ^ l + 1 := by
            rw [show 2 = 1 + 1 by norm_num, ← Nat.add_assoc,
              Nat.sub_add_cancel (Nat.one_le_pow l 2 (by norm_num))]
          rwa [heq] at hcop
        obtain ⟨gD, hDalign⟩ :=
          xi1115_cyclic_align_partition_middle P1 U1 S1 DM hPartitionM
            hDMCyclic hDMne (hDMcard.trans hU1card.symm)
            (by rw [hDMcard, hP1card]; exact hPredQ)
            (by rw [hDMcard, hS1card]; exact hPredSucc)
        intro x hx
        rintro ⟨T, hxT, g, rfl⟩
        rcases hxT with ⟨u, hu, hux⟩
        let yM : M := gD * u * gD⁻¹
        have hyDM : yM ∈ DM := by
          rw [hDalign]
          exact ⟨u, hu, rfl⟩
        let y : Dg := ⟨(yM : M), by simpa [DM, Subgroup.mem_subgroupOf] using hyDM⟩
        refine ⟨y, ?_⟩
        rw [isConj_iff]
        refine ⟨((gD * g⁻¹ : M) : G), ?_⟩
        change (((gD * g⁻¹ : M) : G) * (x : G) *
          ((gD * g⁻¹ : M) : G)⁻¹) = (yM : G)
        have hux' : ((g : M) : G) * ((u : M) : G) * ((g : M) : G)⁻¹ =
            (x : G) := by
          simpa using congrArg Subtype.val hux
        rw [← hux']
        dsimp [yM]
        group
      have hNonsplitFamilyToA : ∀ x : M, x ≠ 1 →
          (∃ T : Subgroup M, x ∈ T ∧
            ∃ g, T = S1.map (MulAut.conj g).toMonoidHom) →
          ∃ y : A, IsConj ((x : M) : G) (y : G) := by
        let AM : Subgroup M := A.subgroupOf M
        have hAMCyclic : IsCyclic AM := by
          let eAM := Subgroup.subgroupOfEquivOfLe hA_le_M
          letI : IsCyclic A := hAcyclic
          exact isCyclic_of_surjective eAM.symm eAM.symm.surjective
        have hAMcard : Nat.card AM = 2 ^ l + 1 := by
          calc
            Nat.card AM = Nat.card A :=
              Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA_le_M).toEquiv
            _ = 2 ^ l + 1 := hAcard
        have hAMne : AM ≠ ⊥ := by
          rw [← Subgroup.one_lt_card_iff_ne_bot, hAMcard]
          have hqOne : 1 ≤ 2 ^ l := Nat.one_le_pow l 2 (by norm_num)
          omega
        have hqEven : Even (2 ^ l) :=
          Nat.even_pow.mpr ⟨even_two, hl.ne'⟩
        have hqSubOdd : Odd (2 ^ l - 1) :=
          Nat.Even.sub_odd (pow_pos (by norm_num : 0 < (2 : ℕ)) l)
            hqEven odd_one
        have hSuccQ : Nat.Coprime (2 ^ l + 1) (2 ^ l) :=
          ((Nat.coprime_self_add_right).mpr
            (Nat.coprime_one_right (2 ^ l))).symm
        have hSuccPred : Nat.Coprime (2 ^ l + 1) (2 ^ l - 1) := by
          have hcop : Nat.Coprime (2 ^ l - 1) ((2 ^ l - 1) + 2) :=
            (Nat.coprime_self_add_right).mpr hqSubOdd.coprime_two_right
          have heq : (2 ^ l - 1) + 2 = 2 ^ l + 1 := by
            rw [show 2 = 1 + 1 by norm_num, ← Nat.add_assoc,
              Nat.sub_add_cancel (Nat.one_le_pow l 2 (by norm_num))]
          rw [heq] at hcop
          exact hcop.symm
        obtain ⟨gA, hAalign⟩ :=
          xi1115_cyclic_align_partition_right P1 U1 S1 AM hPartitionM
            hAMCyclic hAMne (hAMcard.trans hS1card.symm)
            (by rw [hAMcard, hP1card]; exact hSuccQ)
            (by rw [hAMcard, hU1card]; exact hSuccPred)
        intro x hx
        rintro ⟨T, hxT, g, rfl⟩
        rcases hxT with ⟨u, hu, hux⟩
        let yM : M := gA * u * gA⁻¹
        have hyAM : yM ∈ AM := by
          rw [hAalign]
          exact ⟨u, hu, rfl⟩
        let y : A := ⟨(yM : M), by simpa [AM, Subgroup.mem_subgroupOf] using hyAM⟩
        refine ⟨y, ?_⟩
        rw [isConj_iff]
        refine ⟨((gA * g⁻¹ : M) : G), ?_⟩
        change (((gA * g⁻¹ : M) : G) * (x : G) *
          ((gA * g⁻¹ : M) : G)⁻¹) = (yM : G)
        have hux' : ((g : M) : G) * ((u : M) : G) * ((g : M) : G)⁻¹ =
            (x : G) := by
          simpa using congrArg Subtype.val hux
        rw [← hux']
        dsimp [yM]
        group
      have hRankOneAlignedPartition : ∀ x : M, x ≠ 1 →
          (∃ P : Subgroup M, IsPGroup 2 P ∧ x ∈ P) ∨
          (∃ y : Dg, IsConj ((x : M) : G) (y : G)) ∨
          (∃ y : A, IsConj ((x : M) : G) (y : G)) := by
        intro x hx
        obtain ⟨T, hxT, hTfamily⟩ := (hPartitionM x hx).exists
        rcases hTfamily with ⟨g, hT⟩ | ⟨g, hT⟩ | ⟨g, hT⟩
        · left
          refine ⟨T, ?_, hxT⟩
          rw [hT]
          exact hP1.map (MulAut.conj g).toMonoidHom
        · right
          left
          exact hSplitFamilyToDg x hx ⟨T, hxT, g, hT⟩
        · right
          right
          exact hNonsplitFamilyToA x hx ⟨T, hxT, g, hT⟩
      have hRankOneStrongPartition : ∀ x : G,
          x ∈ M → x ^ 2 ≠ 1 → PFAppendixIII.IsStronglyReal x →
            ConjClasses.mk x ∈ SplitClasses ∪ NonsplitClasses := by
        intro x hxM hxsq hxStrong
        let xM : M := ⟨x, hxM⟩
        have hxMne : xM ≠ 1 := by
          intro hx
          apply hxsq
          have hxone : x = 1 := congrArg Subtype.val hx
          simp [hxone]
        have hxOdd : Odd (orderOf x) :=
          xi1115_stronglyReal_sq_ne_one_order_odd
            htwo_transitive hdegreeOdd hat_most_two_fixed_points
            hno_regular_normal a b hab F hFrob hFSuzuki x hxStrong hxsq
        rcases hRankOneAlignedPartition xM hxMne with
          ⟨P, hP, hxP⟩ | ⟨y, hxy⟩ | ⟨y, hxy⟩
        · let xP : P := ⟨xM, hxP⟩
          have hxPOdd : Odd (orderOf xP) := by
            simpa [xP, xM, Subgroup.orderOf_coe] using hxOdd
          have hselfCop : (orderOf xP).Coprime (orderOf xP) :=
            hP.orderOf_coprime hxPOdd.coprime_two_left xP
          have hxPone : xP = 1 :=
            orderOf_eq_one_iff.mp ((Nat.coprime_self _).mp hselfCop)
          apply False.elim
          apply hxsq
          have hxone : x = 1 := by
            exact congrArg (fun z : P => (((z : P) : M) : G)) hxPone
          simp [hxone]
        · left
          have hyne : (y : G) ≠ 1 := by
            intro hy
            rw [isConj_iff] at hxy
            rcases hxy with ⟨g, hg⟩
            have hxone : x = 1 := by
              calc
                x = g⁻¹ * (g * x * g⁻¹) * g := by group
                _ = g⁻¹ * (y : G) * g := by rw [hg]
                _ = 1 := by rw [hy]; simp
            exact hxsq (by simp [hxone])
          refine ⟨⟨y, hyne⟩, ?_⟩
          exact (ConjClasses.mk_eq_mk_iff_isConj.mpr hxy).symm
        · right
          have hyne : (y : G) ≠ 1 := by
            intro hy
            rw [isConj_iff] at hxy
            rcases hxy with ⟨g, hg⟩
            have hxone : x = 1 := by
              calc
                x = g⁻¹ * (g * x * g⁻¹) * g := by group
                _ = g⁻¹ * (y : G) * g := by rw [hg]
                _ = 1 := by rw [hy]; simp
            exact hxsq (by simp [hxone])
          refine ⟨⟨y, hyne⟩, ?_⟩
          exact (ConjClasses.mk_eq_mk_iff_isConj.mpr hxy).symm
      have hCodeRangeLeFamilies :
          Set.range code ⊆
            {ConjClasses.mk s} ∪ SplitClasses ∪ NonsplitClasses := by
        rintro c ⟨o, rfl⟩
        rcases hCodeRepresentativesInM o with ho | ⟨x, hxM, hxsq, hxStrong, ho⟩
        · exact Or.inl (Or.inl ho)
        · rw [ho]
          rcases hRankOneStrongPartition x hxM hxsq hxStrong with hxD | hxA
          · exact Or.inl (Or.inr hxD)
          · exact Or.inr hxA
      have hFamiliesLeCodeRange :
          {ConjClasses.mk s} ∪ SplitClasses ∪ NonsplitClasses ⊆
            Set.range code := by
        have hss : s * s = 1 := by
          simpa [pow_two] using hssq
        have hsInv : PFAppendixIII.IsInvolution s :=
          (orderOf_eq_prime_iff.mp hsorder).symm
        have hDgMem : ∀ x : G,
            x ∈ Dg ↔ x • a = a ∧ x • b = b := by
          intro x
          simpa [H0, D, b', Dg] using
            (xi1115_twoPointStabilizer_map_mem_iff a b hab x)
        have hsInvertsDg : ∀ x : G, x ∈ Dg →
            s * x * s⁻¹ = x⁻¹ := by
          rintro x ⟨d, hd, rfl⟩
          simpa [H0, D, b'] using hsInvertsD ⟨d, hd⟩
        rintro c ((hcOne | hcD) | hcA)
        · have hc : c = ConjClasses.mk s := by simpa using hcOne
          rw [hc]
          exact ⟨none, rfl⟩
        · rcases hcD with ⟨x, rfl⟩
          let xG : G := (x : G)
          let v : G := s * xG
          have hsinv : s⁻¹ = s :=
            inv_eq_of_mul_eq_one_right hss
          have hvSq : v ^ 2 = 1 := by
            rw [pow_two]
            dsimp [v]
            calc
              s * xG * (s * xG) = (s * xG * s⁻¹) * xG := by
                rw [hsinv]
                group
              _ = xG⁻¹ * xG := by
                rw [hsInvertsDg xG x.1.property]
              _ = 1 := by simp
          have hvNe : v ≠ 1 := by
            intro hv
            have hsx : s = xG⁻¹ := by
              have := congrArg (fun q : G => q * xG⁻¹) hv
              simpa [v, mul_assoc] using this
            have hsD : s ∈ Dg := by
              rw [hsx]
              exact Dg.inv_mem x.1.property
            exact hab (((hDgMem s).1 hsD).1.symm.trans hsa)
          have hvInv : PFAppendixIII.IsInvolution v := ⟨hvNe, hvSq⟩
          have hxStrong : PFAppendixIII.IsStronglyReal xG := by
            refine ⟨s, v, hsInv, hvInv, ?_⟩
            dsimp [v, xG]
            rw [← mul_assoc, hss, one_mul]
          obtain ⟨o, ho⟩ :=
            xi1115_stronglyReal_class_mem_codeRange
              htwo_transitive hdegreeOdd hat_most_two_fixed_points
              a b hab F hFrob hF2 hFSuzuki s hsorder hsa
              hallInvolutionsConj xG hxStrong x.2
          exact ⟨o, by simpa [J, code, H0, xG] using ho.symm⟩
        · rcases hcA with ⟨x, rfl⟩
          let xG : G := (x : G)
          let v : G := w * xG
          have hwNe : w ≠ 1 := by
            intro hw
            apply hwNotMem
            rw [hw]; exact A.one_mem
          have hwInvElem : PFAppendixIII.IsInvolution w := by
            exact ⟨hwNe, by simpa [pow_two] using hwsq⟩
          have hwinv : w⁻¹ = w :=
            inv_eq_of_mul_eq_one_right hwsq
          have hvSq : v ^ 2 = 1 := by
            rw [pow_two]
            dsimp [v]
            calc
              w * xG * (w * xG) = (w * xG * w⁻¹) * xG := by
                rw [hwinv]
                group
              _ = xG⁻¹ * xG := by rw [hwInv xG x.1.property]
              _ = 1 := by simp
          have hvNe : v ≠ 1 := by
            intro hv
            apply hwNotMem
            have hwEq : w = xG⁻¹ := by
              have := congrArg (fun q : G => q * xG⁻¹) hv
              simpa [v, mul_assoc] using this
            rw [hwEq]
            exact A.inv_mem x.1.property
          have hvInv : PFAppendixIII.IsInvolution v := ⟨hvNe, hvSq⟩
          have hxStrong : PFAppendixIII.IsStronglyReal xG := by
            refine ⟨w, v, hwInvElem, hvInv, ?_⟩
            dsimp [v, xG]
            rw [← mul_assoc, hwsq, one_mul]
          obtain ⟨o, ho⟩ :=
            xi1115_stronglyReal_class_mem_codeRange
              htwo_transitive hdegreeOdd hat_most_two_fixed_points
              a b hab F hFrob hF2 hFSuzuki s hsorder hsa
              hallInvolutionsConj xG hxStrong x.2
          exact ⟨o, by simpa [J, code, H0, xG] using ho.symm⟩
      have hCodeCover :
          Set.range code =
            {ConjClasses.mk s} ∪ SplitClasses ∪ NonsplitClasses := by
        exact Set.Subset.antisymm hCodeRangeLeFamilies hFamiliesLeCodeRange
      have hClassFamiliesDisjoint :
          Disjoint ({ConjClasses.mk s} : Set (ConjClasses G)) SplitClasses ∧
          Disjoint ({ConjClasses.mk s} : Set (ConjClasses G)) NonsplitClasses ∧
          Disjoint SplitClasses NonsplitClasses := by
        have horderConj : ∀ {x y : G}, IsConj x y → orderOf x = orderOf y := by
          intro x y hxy
          rw [isConj_iff] at hxy
          rcases hxy with ⟨g, rfl⟩
          exact ((MulAut.conj g).orderOf_eq x).symm
        have hDgOdd : Odd (Nat.card Dg) := by
          rw [hDgCard]
          exact hDodd
        have hqEven : Even (2 ^ l) :=
          Nat.even_pow.mpr ⟨even_two, hl.ne'⟩
        have hAOdd : Odd (Nat.card A) := by
          rw [hAcard]
          exact hqEven.add_one
        have hDgACoprime : Nat.Coprime (Nat.card Dg) (Nat.card A) := by
          rw [hDgCard, hDcard, hAcard]
          have hqSubOdd : Odd (2 ^ l - 1) :=
            Nat.Even.sub_odd (pow_pos (by norm_num : 0 < (2 : ℕ)) l)
              hqEven odd_one
          have hcop : Nat.Coprime (2 ^ l - 1) ((2 ^ l - 1) + 2) :=
            (Nat.coprime_self_add_right).mpr hqSubOdd.coprime_two_right
          have hqOne : 1 ≤ 2 ^ l := Nat.one_le_pow l 2 (by norm_num)
          have heq : (2 ^ l - 1) + 2 = 2 ^ l + 1 := by
            rw [show 2 = 1 + 1 by norm_num, ← Nat.add_assoc,
              Nat.sub_add_cancel hqOne]
          rwa [heq] at hcop
        refine ⟨?_, ?_, ?_⟩
        · rw [Set.disjoint_left]
          intro c hcOne hcSplit
          have hc : c = ConjClasses.mk s := by simpa using hcOne
          rcases hcSplit with ⟨x, hx⟩
          have hconj : IsConj (x : G) s :=
            ConjClasses.mk_eq_mk_iff_isConj.mp (hx.trans hc)
          have hord : orderOf (x : G) = 2 :=
            (horderConj hconj).trans hsorder
          have hordD : orderOf (x : G) ∣ Nat.card Dg := by
            simpa [Subgroup.orderOf_coe] using orderOf_dvd_natCard x.1
          exact hDgOdd.not_two_dvd_nat (by simpa [hord] using hordD)
        · rw [Set.disjoint_left]
          intro c hcOne hcA
          have hc : c = ConjClasses.mk s := by simpa using hcOne
          rcases hcA with ⟨x, hx⟩
          have hconj : IsConj (x : G) s :=
            ConjClasses.mk_eq_mk_iff_isConj.mp (hx.trans hc)
          have hord : orderOf (x : G) = 2 :=
            (horderConj hconj).trans hsorder
          have hordA : orderOf (x : G) ∣ Nat.card A := by
            simpa [Subgroup.orderOf_coe] using orderOf_dvd_natCard x.1
          exact hAOdd.not_two_dvd_nat (by simpa [hord] using hordA)
        · rw [Set.disjoint_left]
          intro c hcD hcA
          rcases hcD with ⟨x, hx⟩
          rcases hcA with ⟨y, hy⟩
          have hconj : IsConj (x : G) (y : G) :=
            ConjClasses.mk_eq_mk_iff_isConj.mp (hx.trans hy.symm)
          have hordEq : orderOf (x : G) = orderOf (y : G) :=
            horderConj hconj
          have hordD : orderOf (x : G) ∣ Nat.card Dg := by
            simpa [Subgroup.orderOf_coe] using orderOf_dvd_natCard x.1
          have hordA : orderOf (x : G) ∣ Nat.card A := by
            rw [hordEq]
            simpa [Subgroup.orderOf_coe] using orderOf_dvd_natCard y.1
          have hordOne : orderOf (x : G) = 1 :=
            Nat.eq_one_of_dvd_coprimes hDgACoprime hordD hordA
          exact x.2 (orderOf_eq_one_iff.mp hordOne)
      have hAClassRange :
          Nat.card NonsplitClasses * 2 = 2 ^ l := by
        have honeSplit :
            Disjoint ({ConjClasses.mk s} : Set (ConjClasses G)) SplitClasses :=
          hClassFamiliesDisjoint.1
        have honeA :
            Disjoint ({ConjClasses.mk s} : Set (ConjClasses G)) NonsplitClasses :=
          hClassFamiliesDisjoint.2.1
        have hsplitA : Disjoint SplitClasses NonsplitClasses :=
          hClassFamiliesDisjoint.2.2
        have hleftA :
            Disjoint
              (({ConjClasses.mk s} : Set (ConjClasses G)) ∪ SplitClasses)
              NonsplitClasses := by
          rw [Set.disjoint_left]
          intro c hc hA
          rcases hc with hcOne | hcSplit
          · exact (Set.disjoint_left.mp honeA) hcOne hA
          · exact (Set.disjoint_left.mp hsplitA) hcSplit hA
        have hcardFull :
            Set.ncard
                (({ConjClasses.mk s} : Set (ConjClasses G)) ∪ SplitClasses ∪
                  NonsplitClasses) =
              1 + Nat.card SplitClasses + Nat.card NonsplitClasses := by
          rw [Set.ncard_union_eq hleftA, Set.ncard_union_eq honeSplit]
          simp
        rw [Nat.card_coe_set_eq, hCodeCover] at hcodeRangeCard
        rw [hcardFull] at hcodeRangeCard
        have htwoLe : 2 ≤ 2 ^ l := by
          have hqOne : 1 < 2 ^ l :=
            Nat.one_lt_pow hl.ne' (by norm_num : 1 < (2 : ℕ))
          omega
        exact xi1115_nonsplit_count_arithmetic
          (2 ^ l) (Nat.card SplitClasses) (Nat.card NonsplitClasses)
          htwoLe hcodeRangeCard hDgClassRange
      have hAFusion : ∀ x y : G,
          x ∈ A → y ∈ A → x ≠ 1 → y ≠ 1 →
            (IsConj x y ↔ y = x ∨ y = x⁻¹) := by
        have hqEven : Even (2 ^ l) :=
          Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt hl⟩
        have hAOdd : Odd (Nat.card A) := by
          rw [hAcard]
          exact hqEven.add_one
        exact xi1115_fusion_inverse_of_conjClass_range_card
          A hAOdd w hwInv (by
            simpa [NonsplitClasses, hAcard] using hAClassRange)
      have hDgCentralizer : ∀ x : G, x ∈ Dg → x ≠ 1 →
          Subgroup.centralizer ({x} : Set G) = Dg := by
        have hDgCyclic : IsCyclic Dg := by
          let eD : D ≃* Dg :=
            Subgroup.equivMapOfInjective D H0.subtype H0.subtype_injective
          letI : IsCyclic D := hDcyclic
          exact isCyclic_of_surjective eD eD.surjective
        have hDgComm : IsMulCommutative Dg := by
          letI : IsCyclic Dg := hDgCyclic
          infer_instance
        have hDgOdd : Odd (Nat.card Dg) := by
          rw [hDgCard]
          exact hDodd
        have hDgMem : ∀ z : G,
            z ∈ Dg ↔ z • a = a ∧ z • b = b := by
          intro z
          simpa [H0, D, b', Dg] using
            (xi1115_twoPointStabilizer_map_mem_iff a b hab z)
        have hsInvertsDg : ∀ z : G, z ∈ Dg →
            s * z * s⁻¹ = z⁻¹ := by
          rintro z ⟨d, hd, rfl⟩
          simpa [H0, D, b'] using hsInvertsD ⟨d, hd⟩
        intro x hxD hxne
        apply le_antisymm
        · intro g hg
          have hgcomm : g * x = x * g :=
            Subgroup.mem_centralizer_singleton_iff.mp hg
          have hgconj : g * x * g⁻¹ = x := by
            calc
              g * x * g⁻¹ = x * g * g⁻¹ := by rw [hgcomm]
              _ = x := by simp
          have hxfixa : x • a = a := ((hDgMem x).1 hxD).1
          have hxfixb : x • b = b := ((hDgMem x).1 hxD).2
          have hxfix (c : Omega) (hc : x • c = c) : c = a ∨ c = b := by
            by_contra hcnot
            push Not at hcnot
            exact (hat_most_two_fixed_points x hxne a b c
              hab hcnot.1.symm hcnot.2.symm
              ⟨hxfixa, hxfixb, hc⟩)
          have hxfixga : x • (g • a) = g • a := by
            calc
              x • (g • a) = (x * g) • a := by rw [mul_smul]
              _ = (g * x) • a := by rw [hgcomm]
              _ = g • (x • a) := by rw [mul_smul]
              _ = g • a := by rw [hxfixa]
          have hxfixgb : x • (g • b) = g • b := by
            calc
              x • (g • b) = (x * g) • b := by rw [mul_smul]
              _ = (g * x) • b := by rw [hgcomm]
              _ = g • (x • b) := by rw [mul_smul]
              _ = g • b := by rw [hxfixb]
          rcases hxfix (g • a) hxfixga with hga | hga
          · have hgb : g • b = b := by
              rcases hxfix (g • b) hxfixgb with hgba | hgb
              · exact False.elim (hab
                  ((MulAction.toPerm g).injective (hga.trans hgba.symm)))
              · exact hgb
            exact (hDgMem g).2 ⟨hga, hgb⟩
          · have hgb : g • b = a := by
              rcases hxfix (g • b) hxfixgb with hgb | hgbb
              · exact hgb
              · exact False.elim (hab
                  ((MulAction.toPerm g).injective (hga.trans hgbb.symm)))
            let d : G := s⁻¹ * g
            have hda : d • a = a := by
              dsimp [d]
              rw [mul_smul, hga, ← hsa, inv_smul_smul]
            have hdb : d • b = b := by
              dsimp [d]
              rw [mul_smul, hgb, ← hsb, inv_smul_smul]
            have hdD : d ∈ Dg := (hDgMem d).2 ⟨hda, hdb⟩
            letI : IsMulCommutative Dg := hDgComm
            have hdx : d * x = x * d := by
              exact congrArg Subtype.val
                (mul_comm (⟨d, hdD⟩ : Dg) (⟨x, hxD⟩ : Dg))
            have hgform : g = s * d := by
              dsimp [d]
              group
            have hgInv : g * x * g⁻¹ = x⁻¹ := by
              calc
                g * x * g⁻¹ = s * (d * x * d⁻¹) * s⁻¹ := by
                  rw [hgform]
                  group
                _ = s * x * s⁻¹ := by rw [hdx]; simp
                _ = x⁻¹ := hsInvertsDg x hxD
            have hxinv : x = x⁻¹ := hgconj.symm.trans hgInv
            have hxsq : x ^ 2 = 1 := by
              simpa [pow_two] using (eq_inv_iff_mul_eq_one.mp hxinv)
            let xD : Dg := ⟨x, hxD⟩
            have hxDsq : xD ^ 2 = 1 := by
              apply Subtype.ext
              exact hxsq
            have hxDone : xD = 1 :=
              xi1115_eq_one_of_sq_eq_one_of_odd_card hDgOdd xD hxDsq
            exact False.elim (hxne (congrArg Subtype.val hxDone))
        · intro z hzD
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          exact congrArg Subtype.val
            ((@IsMulCommutative.is_comm Dg _ hDgComm).comm
              (⟨z, hzD⟩ : Dg) (⟨x, hxD⟩ : Dg))
      have hACentralizer : ∀ x : G, x ∈ A → x ≠ 1 →
          Subgroup.centralizer ({x} : Set G) = A := by
        letI : IsCyclic A := hAcyclic
        letI : IsMulCommutative A := hAcyclic.isMulCommutative
        obtain ⟨agen, hagengen⟩ := IsCyclic.exists_generator (α := A)
        let x0 : G := (agen : G)
        have hx0order : orderOf agen = Nat.card A :=
          orderOf_eq_card_of_forall_mem_zpowers hagengen
        have hx0ne : x0 ≠ 1 := by
          intro hx0one
          have hagenone : agen = 1 := Subtype.ext hx0one
          rw [hagenone, orderOf_one, hAcard] at hx0order
          have hqpos : 0 < 2 ^ l := pow_pos (by norm_num) l
          omega
        have hqEven : Even (2 ^ l) :=
          Nat.even_pow.mpr ⟨even_two, Nat.ne_of_gt hl⟩
        have hAOdd : Odd (Nat.card A) := by
          rw [hAcard]
          exact hqEven.add_one
        have hx0sq : x0 ^ 2 ≠ 1 := by
          intro hsq
          have hsqA : agen ^ 2 = 1 := by
            apply Subtype.ext
            exact hsq
          have hagenone : agen = 1 :=
            xi1115_eq_one_of_sq_eq_one_of_odd_card hAOdd agen hsqA
          exact hx0ne (congrArg Subtype.val hagenone)
        have hwNe : w ≠ 1 := by
          intro hwone
          apply hwNotMem
          rw [hwone]; exact A.one_mem
        have hwInvElem : PFAppendixIII.IsInvolution w :=
          ⟨hwNe, by simpa [pow_two] using hwsq⟩
        let v : G := w * x0
        have hvSq : v ^ 2 = 1 := by
          rw [pow_two]
          dsimp [v]
          calc
            w * x0 * (w * x0) = (w * x0 * w⁻¹) * x0 := by
              rw [inv_eq_of_mul_eq_one_right hwsq]
              group
            _ = x0⁻¹ * x0 := by rw [hwInv x0 agen.property]
            _ = 1 := by simp
        have hvNe : v ≠ 1 := by
          intro hvone
          apply hwNotMem
          have hwEq : w = x0⁻¹ := by
            have h := congrArg (fun z : G => z * x0⁻¹) hvone
            simpa [v, mul_assoc] using h
          rw [hwEq]
          exact A.inv_mem agen.property
        have hvInv : PFAppendixIII.IsInvolution v := ⟨hvNe, hvSq⟩
        have hx0Strong : PFAppendixIII.IsStronglyReal x0 := by
          refine ⟨w, v, hwInvElem, hvInv, ?_⟩
          dsimp [v]
          rw [← mul_assoc, hwsq, one_mul]
        let C := Subgroup.centralizer ({x0} : Set G)
        have hA_le_C : A ≤ C := by
          intro z hzA
          change z ∈ Subgroup.centralizer ({x0} : Set G)
          apply Subgroup.mem_centralizer_singleton_iff.mpr
          exact congrArg Subtype.val
            (mul_comm (⟨z, hzA⟩ : A) agen)
        have hCodd : Odd (Nat.card C) := by
          simpa [C] using
            xi1115_stronglyReal_centralizer_card_odd
              htwo_transitive hdegreeOdd hat_most_two_fixed_points
              hno_regular_normal a b hab F hFrob hF2 hFSuzuki
              s hallInvolutionsConj x0 hx0Strong hx0sq
        obtain ⟨hCcomm, t, htInv, htInverts⟩ :=
          xi1115_stronglyReal_centralizer_structure
            htwo_transitive hdegreeOdd hat_most_two_fixed_points
            hno_regular_normal a b hab F hFrob hF2 hFSuzuki
            s hallInvolutionsConj x0 hx0Strong hx0sq
        have hCnontrivial : ∀ z : G, z ∈ C → z ≠ 1 →
            PFAppendixIII.IsStronglyReal z ∧
              Subgroup.centralizer ({z} : Set G) = C := by
          intro z hzC hzne
          simpa [C] using
            xi1115_stronglyReal_centralizer_nontrivial
              htwo_transitive hdegreeOdd hat_most_two_fixed_points
              hno_regular_normal a b hab F hFrob hF2 hFSuzuki
              s hallInvolutionsConj x0 hx0Strong hx0sq z hzC hzne
        have hC_le_normalizer_A : C ≤ Subgroup.normalizer (A : Set G) := by
          intro c hcC
          rw [Subgroup.mem_normalizer_iff]
          intro z
          constructor
          · intro hzA
            have hcz : c * z = z * c := by
              exact congrArg Subtype.val
                ((@IsMulCommutative.is_comm C _ hCcomm).comm
                  (⟨c, hcC⟩ : C) (⟨z, hA_le_C hzA⟩ : C))
            have heq : c * z * c⁻¹ = z := by rw [hcz]; simp
            rw [heq]
            exact hzA
          · intro hconjA
            let y : G := c * z * c⁻¹
            have hyC : y ∈ C := hA_le_C hconjA
            have hcy : c * y = y * c := by
              exact congrArg Subtype.val
                ((@IsMulCommutative.is_comm C _ hCcomm).comm
                  (⟨c, hcC⟩ : C) (⟨y, hyC⟩ : C))
            have hzy : z = y := by
              dsimp [y]
              calc
                z = c⁻¹ * (c * z * c⁻¹) * c := by group
                _ = c⁻¹ * y * c := rfl
                _ = c⁻¹ * (y * c) := by group
                _ = c⁻¹ * (c * y) := by rw [hcy]
                _ = y := by group
            rwa [hzy]
        have htNormalizerA : t ∈ Subgroup.normalizer (A : Set G) := by
          rw [Subgroup.mem_normalizer_iff]
          intro z
          constructor
          · intro hzA
            rw [htInverts z (hA_le_C hzA)]
            exact A.inv_mem hzA
          · intro hzA
            let y : G := t * z * t⁻¹
            have hyA : y ∈ A := hzA
            have hback : t * y * t⁻¹ = z := by
              dsimp [y]
              rw [htInv.inv_eq_self]
              calc
                t * (t * z * t) * t = (t * t) * z * (t * t) := by group
                _ = z := by
                  rw [show t * t = 1 by
                    simpa [pow_two] using htInv.sq_eq_one]
                  simp
            have hyInv := htInverts y (hA_le_C hyA)
            have hzEq : z = y⁻¹ := hback.symm.trans hyInv
            rw [hzEq]
            exact A.inv_mem hyA
        have hApreTI : ∀ k : G,
            k ∉ Subgroup.normalizer (A : Set G) →
              Disjoint A (A.map (MulAut.conj k).toMonoidHom) := by
          intro k hk
          rw [Subgroup.disjoint_def]
          intro z hzA hzAk
          by_contra hzne
          rcases hzAk with ⟨u, huA, huz⟩
          have hune : u ≠ 1 := by
            intro huone
            apply hzne
            simpa [huone] using huz.symm
          have hconj : IsConj u z := by
            rw [isConj_iff]
            exact ⟨k, by simpa using huz⟩
          rcases (hAFusion u z huA hzA hune hzne).mp hconj with hzu | hzu
          · have hkcomm : k * u = u * k := by
              have h := congrArg (fun q : G => q * k) huz
              simpa [hzu, mul_assoc] using h
            have hkCu : k ∈ Subgroup.centralizer ({u} : Set G) :=
              Subgroup.mem_centralizer_singleton_iff.mpr hkcomm
            have hCu : Subgroup.centralizer ({u} : Set G) = C :=
              (hCnontrivial u (hA_le_C huA) hune).2
            apply hk
            apply hC_le_normalizer_A
            rwa [← hCu]
          · let c : G := t⁻¹ * k
            have htBack : t⁻¹ * u⁻¹ * t = u := by
              calc
                t⁻¹ * u⁻¹ * t = t * u⁻¹ * t⁻¹ := by
                  rw [htInv.inv_eq_self]
                _ = (t * u * t⁻¹)⁻¹ := by group
                _ = (u⁻¹)⁻¹ := congrArg Inv.inv
                  (htInverts u (hA_le_C huA))
                _ = u := inv_inv u
            have hcconj : c * u * c⁻¹ = u := by
              dsimp [c]
              calc
                (t⁻¹ * k) * u * (t⁻¹ * k)⁻¹ =
                    t⁻¹ * (k * u * k⁻¹) * t := by group
                _ = t⁻¹ * z * t := by rw [show k * u * k⁻¹ = z by simpa using huz]
                _ = t⁻¹ * u⁻¹ * t := by rw [hzu]
                _ = u := htBack
            have hccomm : c * u = u * c := by
              have h := congrArg (fun q : G => q * c) hcconj
              simpa [mul_assoc] using h
            have hcCu : c ∈ Subgroup.centralizer ({u} : Set G) :=
              Subgroup.mem_centralizer_singleton_iff.mpr hccomm
            have hCu : Subgroup.centralizer ({u} : Set G) = C :=
              (hCnontrivial u (hA_le_C huA) hune).2
            have hcNorm : c ∈ Subgroup.normalizer (A : Set G) :=
              hC_le_normalizer_A (by rwa [← hCu])
            have hkform : k = t * c := by
              dsimp [c]
              group
            apply hk
            rw [hkform]
            exact (Subgroup.normalizer (A : Set G)).mul_mem htNormalizerA hcNorm
        have hCConjA : ∀ z : G, z ∈ C → z ≠ 1 →
            ∃ y : G, y ∈ A ∧ IsConj z y := by
          intro z hzC hzne
          obtain ⟨hzStrong, hCz⟩ := hCnontrivial z hzC hzne
          have hzsq : z ^ 2 ≠ 1 := by
            intro hzsq
            let zC : C := ⟨z, hzC⟩
            have hzCsq : zC ^ 2 = 1 := by
              apply Subtype.ext
              exact hzsq
            have zCone : zC = 1 :=
              xi1115_eq_one_of_sq_eq_one_of_odd_card hCodd zC hzCsq
            exact hzne (congrArg Subtype.val zCone)
          obtain ⟨o, ho⟩ :=
            xi1115_stronglyReal_class_mem_codeRange
              htwo_transitive hdegreeOdd hat_most_two_fixed_points
              a b hab F hFrob hF2 hFSuzuki s hsorder hsa
              hallInvolutionsConj z hzStrong hzne
          have hzFamily : ConjClasses.mk z ∈
              {ConjClasses.mk s} ∪ SplitClasses ∪ NonsplitClasses := by
            rw [← hCodeCover]
            exact ⟨o, by simpa [J, code, H0] using ho.symm⟩
          rcases hzFamily with (hzOne | hzSplit) | hzNonsplit
          · have hzmk : ConjClasses.mk z = ConjClasses.mk s := by
              simpa using hzOne
            have hconj : IsConj z s :=
              ConjClasses.mk_eq_mk_iff_isConj.mp hzmk
            rw [isConj_iff] at hconj
            rcases hconj with ⟨g, hg⟩
            have hzorder : orderOf z = 2 := by
              calc
                orderOf z = orderOf (g * z * g⁻¹) := by
                  simpa [MulAut.conj_apply] using
                    ((MulAut.conj g).orderOf_eq z).symm
                _ = orderOf s := by rw [hg]
                _ = 2 := hsorder
            apply False.elim
            apply hzsq
            rw [← hzorder]
            exact pow_orderOf_eq_one z
          · rcases hzSplit with ⟨y, hy⟩
            have hconj : IsConj (y : G) z :=
              ConjClasses.mk_eq_mk_iff_isConj.mp hy
            have hCy : Subgroup.centralizer ({(y : G)} : Set G) = Dg :=
              hDgCentralizer (y : G) y.1.property y.2
            have hcardEq : Nat.card C = Nat.card Dg := by
              calc
                Nat.card C =
                    Nat.card (Subgroup.centralizer ({z} : Set G)) :=
                  by rw [hCz]
                _ = Nat.card (Subgroup.centralizer ({(y : G)} : Set G)) :=
                  (xi1115_centralizer_card_eq_of_isConj (y : G) z hconj).symm
                _ = Nat.card Dg := by rw [hCy]
            have hcardLe : Nat.card A ≤ Nat.card C :=
              Subgroup.card_le_of_le hA_le_C
            rw [hAcard, hcardEq, hDgCard, hDcard] at hcardLe
            exact False.elim (xi1115_not_succ_le_pred (2 ^ l) hcardLe)
          · rcases hzNonsplit with ⟨y, hy⟩
            have hconj : IsConj (y : G) z :=
              ConjClasses.mk_eq_mk_iff_isConj.mp hy
            exact ⟨y, y.1.property, hconj.symm⟩
        have hCeqA : C = A := by
          exact xi1115_nonsplit_centralizer_eq
            htwo_transitive hdegreeOdd hat_most_two_fixed_points
            hno_regular_normal a b hab F hFrob hF2 hFSuzuki
            s hallInvolutionsConj l hl D hFrobD hDcard
            A C agen rfl hAcard hx0order NonsplitClasses rfl hAClassRange
            hx0Strong hx0sq hA_le_C hCodd hCcomm t htInv htInverts
            hCnontrivial hApreTI hCConjA
        intro x hxA hxne
        exact (hCnontrivial x (hA_le_C hxA) hxne).2.trans hCeqA

      have hANormalizerCard :
          Nat.card (Subgroup.normalizer (A : Set G)) =
            2 * (2 ^ l + 1) := by
        letI : IsCyclic A := hAcyclic
        obtain ⟨a0, ha0gen⟩ := IsCyclic.exists_generator (α := A)
        have ha0order : orderOf a0 = Nat.card A :=
          orderOf_eq_card_of_forall_mem_zpowers ha0gen
        have ha0ne : (a0 : G) ≠ 1 := by
          intro ha0one
          have ha0oneA : a0 = 1 := Subtype.ext ha0one
          rw [ha0oneA, orderOf_one, hAcard] at ha0order
          have hqpos : 0 < 2 ^ l := pow_pos (by norm_num) l
          omega
        let N0 : Subgroup G := A ⊔ Subgroup.zpowers w
        have hnormEq : Subgroup.normalizer (A : Set G) = N0 := by
          apply le_antisymm
          · intro g hg
            let y : G := g * (a0 : G) * g⁻¹
            have hyA : y ∈ A := by
              exact (Subgroup.mem_normalizer_iff.mp hg (a0 : G)).mp a0.property
            have hyne : y ≠ 1 := by
              intro hyone
              apply ha0ne
              calc
                (a0 : G) = g⁻¹ * y * g := by dsimp [y]; group
                _ = 1 := by rw [hyone]; simp
            have hconj : IsConj (a0 : G) y := by
              rw [isConj_iff]
              exact ⟨g, rfl⟩
            rcases (hAFusion (a0 : G) y a0.property hyA ha0ne hyne).mp hconj with
              hy | hy
            · have hgcomm : g * (a0 : G) = (a0 : G) * g := by
                have h := congrArg (fun z : G => z * g) hy
                simpa [y, mul_assoc] using h
              have hgA : g ∈ A := by
                rw [← hACentralizer (a0 : G) a0.property ha0ne]
                exact Subgroup.mem_centralizer_singleton_iff.mpr hgcomm
              exact (show A ≤ N0 from le_sup_left) hgA
            · let c : G := w⁻¹ * g
              have hwBack : w⁻¹ * (a0 : G)⁻¹ * w = (a0 : G) := by
                have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hwsq
                calc
                  w⁻¹ * (a0 : G)⁻¹ * w =
                      w * (a0 : G)⁻¹ * w⁻¹ := by rw [hwinv]
                  _ = (w * (a0 : G) * w⁻¹)⁻¹ := by group
                  _ = ((a0 : G)⁻¹)⁻¹ := congrArg Inv.inv
                    (hwInv (a0 : G) a0.property)
                  _ = (a0 : G) := inv_inv _
              have hcconj : c * (a0 : G) * c⁻¹ = (a0 : G) := by
                dsimp [c]
                calc
                  (w⁻¹ * g) * (a0 : G) * (w⁻¹ * g)⁻¹ =
                      w⁻¹ * (g * (a0 : G) * g⁻¹) * w := by group
                  _ = w⁻¹ * y * w := rfl
                  _ = w⁻¹ * (a0 : G)⁻¹ * w := by rw [hy]
                  _ = (a0 : G) := hwBack
              have hccomm : c * (a0 : G) = (a0 : G) * c := by
                have h := congrArg (fun z : G => z * c) hcconj
                simpa [mul_assoc] using h
              have hcA : c ∈ A := by
                rw [← hACentralizer (a0 : G) a0.property ha0ne]
                exact Subgroup.mem_centralizer_singleton_iff.mpr hccomm
              have hwN0 : w ∈ N0 :=
                (show Subgroup.zpowers w ≤ N0 from le_sup_right)
                  (Subgroup.mem_zpowers w)
              have hcN0 : c ∈ N0 := (show A ≤ N0 from le_sup_left) hcA
              have hgform : g = w * c := by
                dsimp [c]
                group
              rw [hgform]
              exact N0.mul_mem hwN0 hcN0
          · exact sup_le A.le_normalizer
              (Subgroup.zpowers_le.mpr hwNormalizer)
        calc
          Nat.card (Subgroup.normalizer (A : Set G)) = Nat.card N0 := by
            rw [hnormEq]
          _ = 2 * Nat.card A := by simpa [N0] using hdihedralCard
          _ = 2 * (2 ^ l + 1) := by rw [hAcard]

      have hATI : ∀ k : G,
          k ∉ Subgroup.normalizer (A : Set G) →
            Disjoint A (A.map (MulAut.conj k).toMonoidHom) := by
        have hAne : A ≠ ⊥ := by
          rw [← Subgroup.one_lt_card_iff_ne_bot, hAcard]
          have hqpos : 0 < 2 ^ l := pow_pos (by norm_num) l
          omega
        obtain ⟨x, hxA, hxne⟩ : ∃ x : G, x ∈ A ∧ x ≠ 1 := by
          by_contra hnone
          apply hAne
          apply le_antisymm
          · intro z hzA
            have hzone : z = 1 := by
              by_contra hzne
              exact hnone ⟨z, hzA, hzne⟩
            simp [hzone]
          · exact bot_le
        have hCx : Subgroup.centralizer ({x} : Set G) = A :=
          hACentralizer x hxA hxne
        intro k hk
        rw [disjoint_iff, ← hCx]
        apply xi1115_centralizer_TI_core x
        · intro z hz hzNe
          have hzA : z ∈ A := by rw [← hCx]; exact hz
          exact (hACentralizer z hzA hzNe).trans hCx.symm
        · simpa [hCx] using hk

      have hDgNormalizerRelIndex :
          Dg.relIndex (Subgroup.normalizer (Dg : Set G)) = 2 := by
        simpa [Subgroup.relIndex, H0, D, Dg, b'] using
          (xi1115_twoPointStabilizer_normalizer_index_two
            htwo_transitive hat_most_two_fixed_points
            a b hab F hFrob)
      simpa [SharpTriple] using
        (xi1115_global_class_count_tail
          htwo_transitive hat_most_two_fixed_points a b hab F hFrob
          f hf n hdegree hFcardN hnPower hnEven hDodd hDdiv
          l hl hDcard Dg hDgCard hDgNormalizerRelIndex
          hDgCentralizer A hAcard hANormalizerCard hATI)
  have hnotThree : ¬ 3 ∣ Nat.card D := by
    intro hthree
    exact hnotSharp (hxi108GlobalClassCount (hthreePGL hthree))
  have hnotThreePow : ¬ 3 ∣ 2 ^ l - 1 := by
    simpa [hDcard] using hnotThree
  have hlOdd : Odd l :=
    xi1115_odd_of_not_three_dvd_two_pow_sub_one l hnotThreePow
  have hjgRankOne : j = g →
      ∃ M : Subgroup G,
        (M : Set G) = xi1115_rankOneSet Bcenter Icenter s := by
    intro hjg
    have hss : s * s = 1 := by
      simpa [pow_two] using hssq
    have hsInv : s⁻¹ = s :=
      inv_eq_of_mul_eq_one_right hss
    have hInvertsDG :
        ∀ d : D,
          s * (((d : D) : H0) : G) * s =
            (((d⁻¹ : D) : H0) : G) := by
      intro d
      simpa [H0, hsInv] using hsInvertsD d
    have hM := xi1115_center_rankOneSubgroup_of_structure_eq_self
      H0 F D hactionMain hFSuzuki hDregular
      s hss hInvertsDG j g hjorder hjg hstructure
    simpa only [Bcenter, Icenter, Dg, phiFG] using hM
  have hjgRankOneCard : j = g →
      ∃ M : Subgroup G,
        (M : Set G) = xi1115_rankOneSet Bcenter Icenter s ∧
        Nat.card M = (2 ^ l + 1) * 2 ^ l * (2 ^ l - 1) := by
    intro hjg
    obtain ⟨M, hM⟩ := hjgRankOne hjg
    have hMcard :=
      xi1115_rankOneSet_card_of_conj_intersection
        Bcenter Icenter M s hM le_sup_left hsnotBcenter
        hBcenter_conj_Icenter
    refine ⟨M, hM, ?_⟩
    calc
      Nat.card M =
          Nat.card Bcenter +
            Nat.card Bcenter * Nat.card Icenter := hMcard
      _ = (2 ^ l + 1) * 2 ^ l * (2 ^ l - 1) := by
        rw [hBcenterCardPow, hIcenterCardPow]
        exact xi1115_rank_one_card_arithmetic (2 ^ l)
  have hjgRankOneSharp : j = g →
      ∃ M : Subgroup G,
        (M : Set G) = xi1115_rankOneSet Bcenter Icenter s ∧
        Nat.card M = (2 ^ l + 1) * 2 ^ l * (2 ^ l - 1) ∧
        let O := MulAction.orbit M a
        ∀ x y z x' y' z' : O,
          x ≠ y → x ≠ z → y ≠ z →
          x' ≠ y' → x' ≠ z' → y' ≠ z' →
            ∃! q : M,
              q • x = x' ∧ q • y = y' ∧ q • z = z' := by
    intro hjg
    obtain ⟨M, hM, hMcard⟩ := hjgRankOneCard hjg
    have hBcenter_le_M : Bcenter ≤ M := by
      intro x hx
      change x ∈ (M : Set G)
      rw [hM]
      exact Or.inl hx
    have hstab :
        MulAction.stabilizer M a = Bcenter.subgroupOf M := by
      ext x
      constructor
      · intro hx
        change (x : G) ∈ Bcenter
        have hxRank :
            (x : G) ∈ xi1115_rankOneSet Bcenter Icenter s := by
          rw [← hM]
          exact x.property
        rcases hxRank with hxB | ⟨b0, hb0, i, hi, hxi⟩
        · exact hxB
        · have hxfix : (x : G) • a = a := hx
          rw [hxi] at hxfix
          have hifix : i • a = a := hIcenter_le_H0 hi
          have hbfix : b0 • a = a := hBcenter_le_H0 hb0
          have hbmaps : b0 • b = a := by
            simpa [mul_smul, hifix, hsa] using hxfix
          exfalso
          apply hab
          exact (MulAction.toPermHom G Omega b0).injective
            (hbfix.trans hbmaps.symm)
      · intro hx
        change (x : G) • a = a
        exact hBcenter_le_H0 hx
    have hq : 2 ≤ 2 ^ l := by
      have hq' : 1 < 2 ^ l := Nat.one_lt_pow hl.ne' (by norm_num)
      omega
    refine ⟨M, hM, hMcard, ?_⟩
    dsimp
    exact xi1115_rankOneOrbit_sharpTriple
      M Bcenter a (2 ^ l) hBcenter_le_M hstab hMcard
      hBcenterCardPow hq hat_most_two_fixed_points
  have hjgRankOnePGL : j = g →
      ∃ (M : Subgroup G) (K : Type u)
          (_ : Field K) (_ : Finite K),
        (M : Set G) = xi1115_rankOneSet Bcenter Icenter s ∧
        Nat.card K = 2 ^ l ∧
        Nonempty (M ≃* Matrix.ProjGenLinGroup (Fin 2) K) := by
    intro hjg
    obtain ⟨M, hM, hMcard, hsharp⟩ := hjgRankOneSharp hjg
    have hBcenter_le_M : Bcenter ≤ M := by
      intro x hx
      change x ∈ (M : Set G)
      rw [hM]
      exact Or.inl hx
    have hIcenter_le_M : Icenter ≤ M :=
      le_sup_left.trans hBcenter_le_M
    have hDg_le_M : Dg ≤ M :=
      le_sup_right.trans hBcenter_le_M
    have hstab :
        MulAction.stabilizer M a = Bcenter.subgroupOf M := by
      ext x
      constructor
      · intro hx
        change (x : G) ∈ Bcenter
        have hxRank :
            (x : G) ∈ xi1115_rankOneSet Bcenter Icenter s := by
          rw [← hM]
          exact x.property
        rcases hxRank with hxB | ⟨b0, hb0, i, hi, hxi⟩
        · exact hxB
        · have hxfix : (x : G) • a = a := hx
          rw [hxi] at hxfix
          have hifix : i • a = a := hIcenter_le_H0 hi
          have hbfix : b0 • a = a := hBcenter_le_H0 hb0
          have hbmaps : b0 • b = a := by
            simpa [mul_smul, hifix, hsa] using hxfix
          exfalso
          apply hab
          exact (MulAction.toPermHom G Omega b0).injective
            (hbfix.trans hbmaps.symm)
      · intro hx
        change (x : G) • a = a
        exact hBcenter_le_H0 hx
    have hsM : s ∈ M := by
      change s ∈ (M : Set G)
      rw [hM]
      right
      exact ⟨1, Bcenter.one_mem, 1, Icenter.one_mem, by simp⟩
    have hbOrbit : b ∈ MulAction.orbit M a := by
      rw [MulAction.mem_orbit_iff]
      exact ⟨⟨s, hsM⟩, hsa⟩
    have hDgMem :
        ∀ x : G, x ∈ Dg ↔ x • a = a ∧ x • b = b := by
      intro x
      simpa [H0, D, b', Dg] using
        (xi1115_twoPointStabilizer_map_mem_iff a b hab x)
    have hIcenterNe : Icenter ≠ ⊥ := by
      intro hbot
      have hone : Nat.card Icenter = 1 := by rw [hbot]; simp
      rw [hIcenterCardPow] at hone
      have htwo : 2 ≤ 2 ^ l := by
        have htwo' : 1 < 2 ^ l := Nat.one_lt_pow hl.ne' (by norm_num)
        omega
      omega
    have hDgNe : Dg ≠ ⊥ := by
      intro hbot
      apply hFrobD.complement_ne_bot
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have hxDg : ((x : H0) : G) ∈ Dg := ⟨x, hx, rfl⟩
      rw [hbot] at hxDg
      exact Subgroup.mem_bot.mpr
        (Subtype.ext (Subgroup.mem_bot.mp hxDg))
    have hIcenterComm : IsMulCommutative Icenter := by
      dsimp [Icenter]
      infer_instance
    obtain ⟨K, fieldK, finiteK, hKcard, eM⟩ :=
      xi1115_rankOneOrbit_charTwo_pgl
        M Icenter Dg a b hab hIcenter_le_M hDg_le_M
        (by simpa [Bcenter] using hstab) hbOrbit hDgMem
        hDg_normalizes_Icenter hIcenterDgDisjoint
        hIcenterNe hDgNe hIcenterComm hl hIcenterCardPow
        (hDgCard.trans hDcard) hMcard hsharp
        hat_most_two_fixed_points
    exact ⟨M, K, fieldK, finiteK, hM, hKcard, eM⟩
  have hjNeG : j ≠ g := by
    intro hjg
    exact hnotSharp (hxi108GlobalClassCount (hjgRankOnePGL hjg))
  have hss : s * s = 1 := by
    simpa [pow_two] using hssq
  have hsjNe : s * phiFG j ≠ 1 := by
    intro hsj
    have hfix : (s * phiFG j) • a = a := by
      rw [hsj]
      simp
    have hjfix : phiFG j • a = a := by
      change (((j : F) : H0) : G) • a = a
      exact (j : H0).property
    have hsfix : s • a = a := by
      simpa [mul_smul, hjfix] using hfix
    exact hab (hsfix.symm.trans hsa)
  have hstructureMain :
      s * phiFG j * s = phiFG g * s * (phiFG g)⁻¹ := by
    simpa [phiFG, H0] using hstructure
  have hGcardMain :
      Nat.card G =
        (Nat.card F + 1) * Nat.card F * (2 ^ l - 1) := by
    rcases
        xi1115_action_parameters_core
          htwo_transitive a b hab F hFrob with
      ⟨_, _, hGcard, _⟩
    calc
      Nat.card G =
          Fintype.card Omega * Nat.card F * Nat.card D := hGcard
      _ = (Nat.card F + 1) * Nat.card F * (2 ^ l - 1) := by
        rw [hdegreeF, hDcard]
  have hFcardCenterSq :
      Nat.card F = Nat.card (Subgroup.center F) ^ 2 := by
    exact xi1115_kernel_card_eq_center_sq_of_structureEquation
      hFSuzuki l hZcard hlOdd phiFG s j g hss hjorder hgne
      hjPower hjNeG hsjNe hstructureMain hGcardMain
  have hcoordinates :=
    Higman.theorem1_order_center_sq_typeA_coordinates
      hFSuzuki hDcyclic
      (inferInstance : FaithfulSMul D F) hDregular hFcardCenterSq
  have hSuzukiParameter :
      ∃ m : ℕ, 0 < m ∧ l = 2 * m + 1 := by
    rcases hlOdd with ⟨m, hlm⟩
    refine ⟨m, ?_, hlm⟩
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    subst m
    simp at hlm
    subst l
    norm_num at hDcard
    exact hFrobD.complement_ne_bot hDcard
  obtain ⟨m, hm, hlm⟩ := hSuzukiParameter
  obtain ⟨r, hr, theta, pairLift, cocycle, eK, eQ, eZ,
      hCoordinateProps⟩ := hcoordinates
  have hrl : r = l := by
    have hCenterCoord : Nat.card (Subgroup.center F) = 2 ^ r := by
      rcases hCoordinateProps with
        ⟨_period, _nonfixed, _addLeft, _addRight, _diagonal,
          _pairTop, _pairOne, _pairSurj, _pairInj, _pairMul,
          hCenterCoord, _quotientAction, _centerAction,
          _pairQuotient, _pairCenter⟩
      exact hCenterCoord
    rw [hZcard] at hCenterCoord
    exact (Nat.pow_right_injective
      (by norm_num : 1 < (2 : ℕ)) hCenterCoord).symm
  subst r
  subst l
  have hTwistedNormInjective :
      Function.Injective (fun x : PFAppendixIII.BinaryGaloisField (2 * m + 1) =>
        x * theta x) := by
    rcases hCoordinateProps with
      ⟨_hThetaPeriod, _hThetaNonfixed, _hCocycleLeft, _hCocycleRight,
        _hCocycleDiag, _hPairTop, _hPairOne, _hPairSurj, _hPairInj,
        _hPairMul, _hCenterCoord, _hQuotientAction, hCenterAction,
        _hPairQuotient, _hPairCenter⟩
    intro x y hxy
    by_cases hx : x = 0
    · subst x
      have hyProd : y * theta y = 0 := by simpa using hxy.symm
      rcases mul_eq_zero.mp hyProd with hy | hthetaY
      · exact hy.symm
      · have hy : y = 0 := by
          apply theta.injective
          simpa using hthetaY
        exact hy.symm
    have hy : y ≠ 0 := by
      intro hy
      subst y
      have hxProd : x * theta x ≠ 0 :=
        mul_ne_zero hx ((map_ne_zero theta).mpr hx)
      exact hxProd (by simpa using hxy)
    let dx : D := eK.symm (Units.mk0 x hx)
    let dy : D := eK.symm (Units.mk0 y hy)
    let z0C : Subgroup.center F :=
      eZ.symm (Multiplicative.ofAdd
        (1 : PFAppendixIII.BinaryGaloisField (2 * m + 1)))
    let z0 : F := z0C
    have hz0Cne : z0C ≠ 1 := by
      intro hz
      have hzCoord := congrArg
        (fun z : Subgroup.center F => (eZ z).toAdd) hz
      simp [z0C] at hzCoord
    have hz0ne : z0 ≠ 1 := by
      intro hz
      apply hz0Cne
      exact Subtype.ext hz
    have hz0Inv : z0 ∈ PFAppendixIII.involutions F := by
      rw [hinvolutions]
      exact ⟨z0C.property, hz0ne⟩
    have hact : dx • z0 = dy • z0 := by
      dsimp [z0, z0C]
      rw [hCenterAction dx 1, hCenterAction dy 1]
      apply Subtype.ext
      simpa [dx, dy] using hxy
    obtain ⟨k, _hk, huniq⟩ :=
      hDregular.2 z0 hz0Inv (dx • z0)
        (hDregular.1 z0 hz0Inv dx)
    have hdxk : dx = k := huniq dx rfl
    have hdyk : dy = k := huniq dy hact
    have hdxy : dx = dy := hdxk.trans hdyk.symm
    have hvals := congrArg
      (fun d : D => (eK d : PFAppendixIII.BinaryGaloisField (2 * m + 1))) hdxy
    simpa [dx, dy] using hvals
  have hCocycleZeroLeft :
      ∀ b : PFAppendixIII.BinaryGaloisField (2 * m + 1),
        cocycle 0 b = 0 := by
    rcases hCoordinateProps with
      ⟨_hThetaPeriod, _hThetaNonfixed, hCocycleLeft, _hCocycleRight,
        _hCocycleDiag, _hPairTop, _hPairOne, _hPairSurj, _hPairInj,
        _hPairMul, _hCenterCoord, _hQuotientAction, _hCenterAction,
        _hPairQuotient, _hPairCenter⟩
    intro b
    have h := hCocycleLeft 0 0 b
    rw [zero_add] at h
    exact xi1115_eq_zero_of_eq_add_self (cocycle 0 b) h
  have hCocycleZeroRight :
      ∀ a : PFAppendixIII.BinaryGaloisField (2 * m + 1),
        cocycle a 0 = 0 := by
    rcases hCoordinateProps with
      ⟨_hThetaPeriod, _hThetaNonfixed, _hCocycleLeft, hCocycleRight,
        _hCocycleDiag, _hPairTop, _hPairOne, _hPairSurj, _hPairInj,
        _hPairMul, _hCenterCoord, _hQuotientAction, _hCenterAction,
        _hPairQuotient, _hPairCenter⟩
    intro a
    have h := hCocycleRight a 0 0
    rw [zero_add] at h
    exact xi1115_eq_zero_of_eq_add_self (cocycle a 0) h
  let pairFun :
      PFAppendixIII.BinaryGaloisField (2 * m + 1) ×
          PFAppendixIII.BinaryGaloisField (2 * m + 1) → F :=
    fun az => pairLift az.1 az.2
  have hPairFunBijective : Function.Bijective pairFun := by
    rcases hCoordinateProps with
      ⟨_hThetaPeriod, _hThetaNonfixed, _hCocycleLeft, _hCocycleRight,
        _hCocycleDiag, _hPairTop, _hPairOne, hPairSurj, hPairInj,
        _hPairMul, _hCenterCoord, _hQuotientAction, _hCenterAction,
        _hPairQuotient, _hPairCenter⟩
    constructor
    · intro az bw hab
      rcases hPairInj az.1 az.2 bw.1 bw.2 hab with ⟨ha, hz⟩
      exact Prod.ext ha hz
    · intro x
      rcases hPairSurj x with ⟨a, z, hx⟩
      exact ⟨(a, z), hx.symm⟩
  let centerMap :
      PFAppendixIII.BinaryGaloisField (2 * m + 1) →
        Subgroup.center F := fun z =>
    ⟨pairLift 0 z, by
      rcases hCoordinateProps with
        ⟨_hThetaPeriod, _hThetaNonfixed, _hCocycleLeft, _hCocycleRight,
          _hCocycleDiag, _hPairTop, _hPairOne, hPairSurj, _hPairInj,
          hPairMul, _hCenterCoord, _hQuotientAction, _hCenterAction,
          _hPairQuotient, _hPairCenter⟩
      rw [Subgroup.mem_center_iff]
      intro x
      rcases hPairSurj x with ⟨a, w, hx⟩
      change x * pairLift 0 z = pairLift 0 z * x
      rw [hx, hPairMul, hPairMul, hCocycleZeroLeft,
        hCocycleZeroRight]
      simp [add_comm]⟩
  have hCenterMapInjective : Function.Injective centerMap := by
    rcases hCoordinateProps with
      ⟨_hThetaPeriod, _hThetaNonfixed, _hCocycleLeft, _hCocycleRight,
        _hCocycleDiag, _hPairTop, _hPairOne, _hPairSurj, hPairInj,
        _hPairMul, _hCenterCoord, _hQuotientAction, _hCenterAction,
        _hPairQuotient, _hPairCenter⟩
    intro z w hzw
    have hval := congrArg
      (fun x : Subgroup.center F => (x : F)) hzw
    exact (hPairInj 0 z 0 w hval).2
  have hCenterMapSurjective : Function.Surjective centerMap := by
    rcases hCoordinateProps with
      ⟨_hThetaPeriod, hThetaNonfixed, hCocycleLeft, hCocycleRight,
        hCocycleDiag, _hPairTop, _hPairOne, hPairSurj, hPairInj,
        hPairMul, _hCenterCoord, _hQuotientAction, _hCenterAction,
        _hPairQuotient, _hPairCenter⟩
    intro x
    rcases hPairSurj (x : F) with ⟨a, z, hx⟩
    have hCocycleSymm : ∀ b, cocycle a b = cocycle b a := by
      intro b
      have hcomm := Subgroup.mem_center_iff.mp x.property (pairLift b 0)
      have hcommEq :
          pairLift a z * pairLift b 0 =
            pairLift b 0 * pairLift a z := by
        simpa [hx] using hcomm.symm
      rw [hPairMul, hPairMul] at hcommEq
      have hcoord := (hPairInj _ _ _ _ hcommEq).2
      have hcoord' :
          z + 0 + cocycle a b = z + 0 + cocycle b a := by
        calc
          z + 0 + cocycle a b = 0 + z + cocycle b a := hcoord
          _ = z + 0 + cocycle b a := by abel
      exact add_left_cancel hcoord'
    have hpolar : ∀ b, a * theta b + b * theta a = 0 := by
      intro b
      calc
        a * theta b + b * theta a =
            (a + b) * theta (a + b) +
              a * theta a + b * theta b := by
                rw [map_add]
                ring_nf
                simp only [CharTwo.two_eq_zero, mul_zero, add_zero]
        _ = cocycle (a + b) (a + b) +
              cocycle a a + cocycle b b := by
                rw [hCocycleDiag, hCocycleDiag, hCocycleDiag]
        _ = (cocycle a a + cocycle a b +
              (cocycle b a + cocycle b b)) +
              cocycle a a + cocycle b b := by
                rw [hCocycleLeft, hCocycleRight, hCocycleRight]
        _ = 0 := by
          rw [hCocycleSymm b]
          calc
            (cocycle a a + cocycle b a +
                (cocycle b a + cocycle b b)) +
                cocycle a a + cocycle b b =
              (cocycle a a + cocycle a a) +
                (cocycle b a + cocycle b a) +
                (cocycle b b + cocycle b b) := by abel
            _ = 0 := by
              simp only [CharTwo.add_self_eq_zero]
    have ha : a = 0 := by
      by_contra ha
      have hThetaFixed : ∀ y, theta y = y := by
        intro y
        have hfactor : a * theta a * (theta y + y) = 0 := by
          calc
            a * theta a * (theta y + y) =
                a * theta (a * y) + (a * y) * theta a := by
                  rw [map_mul]
                  ring
            _ = 0 := hpolar (a * y)
        have hsum : theta y + y = 0 :=
          (mul_eq_zero.mp hfactor).resolve_left
            (mul_ne_zero ha ((map_ne_zero theta).mpr ha))
        exact (eq_neg_of_add_eq_zero_left hsum).trans (CharTwo.neg_eq y)
      rcases hThetaNonfixed with ⟨y, hy⟩
      exact hy (hThetaFixed y)
    subst a
    refine ⟨z, ?_⟩
    apply Subtype.ext
    exact hx.symm
  have hStandardTypeACoordinates :
      ∃ pairA :
          PFAppendixIII.BinaryGaloisField (2 * m + 1) →
          PFAppendixIII.BinaryGaloisField (2 * m + 1) → F,
        pairA 0 0 = 1 ∧
        (∀ x : F, ∃ a z, x = pairA a z) ∧
        (∀ a z b w, pairA a z = pairA b w → a = b ∧ z = w) ∧
        (∀ a z b w,
          pairA a z * pairA b w =
            pairA (a + b) (z + w + a * theta b)) ∧
        (∀ a z,
          (eQ (QuotientGroup.mk' (Subgroup.center F) (pairA a z))).toAdd = a) ∧
        ∀ z, pairA 0 z =
          ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center F) : F) := by
    rcases hCoordinateProps with
      ⟨_hThetaPeriod, _hThetaNonfixed, hCocycleLeft, hCocycleRight,
        hCocycleDiag, _hPairTop, hPairOne, hPairSurj, hPairInj,
        hPairMul, _hCenterCoord, _hQuotientAction, _hCenterAction,
        hPairQuotient, hPairCenter⟩
    exact xi1115_normalize_typeA_coordinates theta pairLift cocycle
      hCocycleLeft hCocycleRight hCocycleDiag hPairOne hPairSurj
      hPairInj hPairMul
      (fun x =>
        (eQ (QuotientGroup.mk' (Subgroup.center F) x)).toAdd)
      (fun z =>
        ((eZ.symm (Multiplicative.ofAdd z) : Subgroup.center F) : F))
      hPairQuotient hPairCenter
  have hActorEquivariantTypeACoordinates :
      ∃ pairB :
          PFAppendixIII.BinaryGaloisField (2 * m + 1) →
          PFAppendixIII.BinaryGaloisField (2 * m + 1) → F,
        pairB 0 0 = 1 ∧
        (∀ x : F, ∃ a z, x = pairB a z) ∧
        (∀ a z b w, pairB a z = pairB b w → a = b ∧ z = w) ∧
        (∀ a z b w,
          pairB a z * pairB b w =
            pairB (a + b) (z + w + a * theta b)) ∧
        ∀ d : D, ∀ a z,
          d • pairB a z =
            pairB ((eK d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) * a)
              ((eK d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) *
                theta (eK d : PFAppendixIII.BinaryGaloisField (2 * m + 1)) * z) := by
    rcases hStandardTypeACoordinates with
      ⟨pairA, hPairOne, hPairSurj, hPairInj, hPairMul,
        hPairQuotient, hPairCenter⟩
    rcases hCoordinateProps with
      ⟨_hThetaPeriod, _hThetaNonfixed, _hCocycleLeft, _hCocycleRight,
        _hCocycleDiag, _hPairTop, _hPairOne, _hPairSurj, _hPairInj,
        _hPairMul, _hCenterCoord, hQuotientAction, hCenterAction,
        _hPairQuotient, _hPairCenter⟩
    exact xi1115_exists_actor_equivariant_coordinates
      (2 * m + 1) theta pairA eK eQ eZ hDodd hPairOne hPairSurj
      hPairInj hPairMul hPairQuotient hPairCenter hQuotientAction
      hCenterAction
  have hActorEquivariantTypeACoordinatesForBruhat :=
    hActorEquivariantTypeACoordinates
  rcases hActorEquivariantTypeACoordinatesForBruhat with
    ⟨pairN, hPairNOne, hPairNSurj, hPairNInj, hPairNMul,
      hPairNAction⟩

  obtain ⟨pairJ, hPairJOne, hPairJSurj, hPairJInj, hPairJMul,
      hPairJAction, hPairJj⟩ :=
    xi1115_normalize_typeA_central_involution theta eK pairN
      hPairNOne hPairNSurj hPairNInj hPairNMul hPairNAction
      hDregular j hjInv
  have hg4 : g ^ 4 = 1 :=
    (Higman.theorem1_center_quotient_orders_and_exponent hFSuzuki).2.2.2.2 g
  have hjEqGSq : j = g ^ 2 :=
    (xi1115_cyclic_power_order_four j g hjorder hgne hg4 hjPower hjNeG).2
  obtain ⟨ga, gz, hgPair⟩ := hPairJSurj g
  have hNormGa : ga * theta ga = 1 := by
    have hcoord : pairJ 0 1 = pairJ 0 (ga * theta ga) := by
      calc
        pairJ 0 1 = j := hPairJj
        _ = g ^ 2 := hjEqGSq
        _ = pairJ ga gz * pairJ ga gz := by rw [pow_two, hgPair]
        _ = pairJ (ga + ga) (gz + gz + ga * theta ga) :=
          hPairJMul ga gz ga gz
        _ = pairJ 0 (ga * theta ga) := by
          simp only [CharTwo.add_self_eq_zero, zero_add]
    exact (hPairJInj 0 1 0 (ga * theta ga) hcoord).2.symm
  have hga : ga = 1 := by
    apply hTwistedNormInjective
    simpa using hNormGa
  subst ga
  have hgPairJ : g = pairJ 1 gz := hgPair
  have hAmbientBruhat :
      ∀ x : G,
        x ∈ H0 ∨
          ∃ h₁ h₂ : H0, x = (h₁ : G) * s * (h₂ : G) := by
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo_transitive
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hstabPretrans :
        MulAction.IsPretransitive H0 (SubMulAction.ofStabilizer G a) := by
      exact (MulAction.is_one_pretransitive_iff
        (G := H0) (α := SubMulAction.ofStabilizer G a)).mp
          ((SubMulAction.ofStabilizer.isMultiplyPretransitive
            (G := G) (a := a)).mp htwo_transitive)
    intro x
    by_cases hxa : x • a = a
    · left
      exact hxa
    · right
      let xa : SubMulAction.ofStabilizer G a := ⟨x • a, hxa⟩
      let ba : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
      obtain ⟨h₁, hh₁⟩ := hstabPretrans.exists_smul_eq ba xa
      have hh₁G : (h₁ : G) • b = x • a := by
        exact congrArg Subtype.val hh₁
      let h₂G : G := s⁻¹ * (h₁ : G)⁻¹ * x
      have hh₂fix : h₂G • a = a := by
        calc
          h₂G • a = s⁻¹ • ((h₁ : G)⁻¹ • (x • a)) := by
            simp only [h₂G, mul_smul]
          _ = s⁻¹ • b := by rw [← hh₁G, inv_smul_smul]
          _ = a := by rw [← hsa, inv_smul_smul]
      let h₂ : H0 := ⟨h₂G, hh₂fix⟩
      refine ⟨h₁, h₂, ?_⟩
      dsimp [h₂, h₂G]
      group
  let bruhatEval : F × D × F → G := fun p =>
    (((p.1 : F) : H0) : G) * (((p.2.1 : D) : H0) : G) * s *
      (((p.2.2 : F) : H0) : G)
  have hswapKernelNotH :
      ∀ x : F, x ≠ 1 →
        s * (((x : F) : H0) : G) * s ∉ H0 := by
    intro x hx hxH
    have hgfix :
        (s * (((x : F) : H0) : G) * s) • a = a := hxH
    have hxb : (((x : F) : H0) : G) • b = b := by
      apply smul_left_cancel s
      calc
        s • ((((x : F) : H0) : G) • b) =
            (s * (((x : F) : H0) : G) * s) • a := by
              simp [mul_smul, hsa]
        _ = a := hgfix
        _ = s • b := hsb.symm
    have hxD : (x : H0) ∈ D := by
      apply MulAction.mem_stabilizer_iff.mpr
      exact Subtype.ext hxb
    have hxbot : (x : H0) ∈ (⊥ : Subgroup H0) :=
      hFrobD.isComplement'.disjoint.le_bot ⟨x.property, hxD⟩
    apply hx
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
  have hKernelBruhatExists :
      ∀ x : F, x ≠ 1 →
        ∃ p : F × D × F,
          s * (((x : F) : H0) : G) * s = bruhatEval p := by
    intro x hx
    obtain ⟨h₁, h₂, hg⟩ :=
      (hAmbientBruhat (s * (((x : F) : H0) : G) * s)).resolve_left
        (hswapKernelNotH x hx)
    let eFD : H0 ≃ F × D := hFrobD.isComplement'.equiv
    let p₁ : F × D := eFD h₁
    let p₂ : F × D := eFD h₂
    have hh₁ :
        (((p₁.1 : F) : H0) : G) * (((p₁.2 : D) : H0) : G) =
          (h₁ : G) := by
      exact congrArg Subtype.val
        (hFrobD.isComplement'.equiv_fst_mul_equiv_snd h₁)
    have hh₂ :
        (((p₂.1 : F) : H0) : G) * (((p₂.2 : D) : H0) : G) =
          (h₂ : G) := by
      exact congrArg Subtype.val
        (hFrobD.isComplement'.equiv_fst_mul_equiv_snd h₂)
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hd₂InvConj :
        ((((p₂.2 : D)⁻¹ : D) : H0) : G) =
          s * (((p₂.2 : D) : H0) : G) * s := by
      have hconj := hsInvertsD p₂.2
      have hconj' :
          s * (((p₂.2 : D) : H0) : G) * s =
            ((((p₂.2 : D)⁻¹ : D) : H0) : G) := by
        simpa [hsinv] using hconj
      exact hconj'.symm
    have hd₂Inv :
        ((((p₂.2 : D)⁻¹ : D) : H0) : G) =
          (((p₂.2 : D) : H0) : G)⁻¹ := by
      rfl
    have hmove :
        (((p₂.2 : D) : H0) : G)⁻¹ * s =
          s * (((p₂.2 : D) : H0) : G) := by
      rw [← hd₂Inv, hd₂InvConj]
      simp [mul_assoc, hss]
    have halpha :
        (((((p₂.2 : D)⁻¹ : D) • p₂.1 : F) : H0) : G) =
          ((((p₂.2 : D)⁻¹ : D) : H0) : G) *
            (((p₂.1 : F) : H0) : G) *
              (((p₂.2 : D) : H0) : G) := by
      calc
        (((((p₂.2 : D)⁻¹ : D) • p₂.1 : F) : H0) : G)
            = ((((p₂.2 : D)⁻¹ : D) : H0) : G) * (((p₂.1 : F) : H0) : G) *
                ((((p₂.2 : D)⁻¹ : D) : H0) : G)⁻¹ :=
          hactionMain (p₂.2 : D)⁻¹ p₂.1
        _ = ((((p₂.2 : D)⁻¹ : D) : H0) : G) * (((p₂.1 : F) : H0) : G) *
            (((p₂.2 : D) : H0) : G) := by
          simp
    have hgamma :
        ((((p₁.2 * p₂.2⁻¹ : D) : D) : H0) : G) =
          (((p₁.2 : D) : H0) : G) *
            ((((p₂.2 : D)⁻¹ : D) : H0) : G) := by
      rfl
    refine ⟨(p₁.1, p₁.2 * p₂.2⁻¹, p₂.2⁻¹ • p₂.1), ?_⟩
    change s * (((x : F) : H0) : G) * s =
      (((p₁.1 : F) : H0) : G) *
        ((((p₁.2 * p₂.2⁻¹ : D) : D) : H0) : G) * s *
          ((((p₂.2⁻¹ • p₂.1 : F) : F) : H0) : G)
    calc
      s * (((x : F) : H0) : G) * s = (h₁ : G) * s * (h₂ : G) := hg
      _ = ((((p₁.1 : F) : H0) : G) * (((p₁.2 : D) : H0) : G)) * s *
          ((((p₂.1 : F) : H0) : G) * (((p₂.2 : D) : H0) : G)) := by
            rw [hh₁, hh₂]
      _ = (((p₁.1 : F) : H0) : G) *
          ((((p₁.2 * p₂.2⁻¹ : D) : D) : H0) : G) * s *
            ((((p₂.2⁻¹ • p₂.1 : F) : F) : H0) : G) := by
              rw [halpha, hgamma, hd₂Inv]
              calc
                (((p₁.1 : F) : H0) : G) * (((p₁.2 : D) : H0) : G) * s *
                    ((((p₂.1 : F) : H0) : G) * (((p₂.2 : D) : H0) : G)) =
                  (((p₁.1 : F) : H0) : G) * (((p₁.2 : D) : H0) : G) *
                    (((((p₂.2 : D) : H0) : G)⁻¹ * s) *
                      ((((p₂.2 : D) : H0) : G)⁻¹ *
                        (((p₂.1 : F) : H0) : G) *
                          (((p₂.2 : D) : H0) : G))) := by
                            rw [hmove]
                            group
                _ = (((p₁.1 : F) : H0) : G) *
                    ((((p₁.2 : D) : H0) : G) *
                      (((p₂.2 : D) : H0) : G)⁻¹) * s *
                        ((((p₂.2 : D) : H0) : G)⁻¹ *
                          (((p₂.1 : F) : H0) : G) *
                            (((p₂.2 : D) : H0) : G)) := by group
  have hstabPretransMain :
      MulAction.IsPretransitive H0 (SubMulAction.ofStabilizer G a) := by
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo_transitive
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    exact (MulAction.is_one_pretransitive_iff
      (G := H0) (α := SubMulAction.ofStabilizer G a)).mp
        ((SubMulAction.ofStabilizer.isMultiplyPretransitive
          (G := G) (a := a)).mp htwo_transitive)
  have hFRegular :
      ∀ x y : SubMulAction.ofStabilizer G a,
        ∃! k : F, (k : H0) • x = y :=
    huppert_blackburn_XI_regular_of_isComplement_stabilizer
      hFrobD.isComplement' hstabPretransMain
  have hBruhatEvalAction (p : F × D × F) :
      bruhatEval p • a = (((p.1 : F) : H0) : G) • b := by
    have hAlphaFix : (((p.2.2 : F) : H0) : G) • a = a :=
      ((p.2.2 : F) : H0).property
    have hGammaFix : (((p.2.1 : D) : H0) : G) • b = b :=
      congrArg Subtype.val
        (MulAction.mem_stabilizer_iff.mp (p.2.1 : D).property)
    dsimp [bruhatEval]
    simp only [mul_smul, hAlphaFix, hsa, hGammaFix]
  have hKernelBruhatUnique :
      ∀ (x : F) (hx : x ≠ 1) (p q : F × D × F),
        s * (((x : F) : H0) : G) * s = bruhatEval p →
        s * (((x : F) : H0) : G) * s = bruhatEval q →
          p = q := by
    intro x _hx p q hp hq
    have hevalEq : bruhatEval p = bruhatEval q := hp.symm.trans hq
    have hBetaActionG :
        (((p.1 : F) : H0) : G) • b =
          (((q.1 : F) : H0) : G) • b := by
      calc
        (((p.1 : F) : H0) : G) • b = bruhatEval p • a :=
          (hBruhatEvalAction p).symm
        _ = bruhatEval q • a := congrArg (fun z : G => z • a) hevalEq
        _ = (((q.1 : F) : H0) : G) • b := hBruhatEvalAction q
    have hBetaAction :
        (p.1 : F) • b' = (q.1 : F) • b' := by
      apply Subtype.ext
      exact hBetaActionG
    obtain ⟨k, hk, hkUnique⟩ := hFRegular b' ((p.1 : F) • b')
    have hpBeta : p.1 = k := hkUnique p.1 rfl
    have hqBeta : q.1 = k := hkUnique q.1 hBetaAction.symm
    have hbeta : p.1 = q.1 := hpBeta.trans hqBeta.symm
    have hrest :
        (((p.2.1 : D) : H0) : G) * s * (((p.2.2 : F) : H0) : G) =
          (((q.2.1 : D) : H0) : G) * s * (((q.2.2 : F) : H0) : G) := by
      calc
        (((p.2.1 : D) : H0) : G) * s * (((p.2.2 : F) : H0) : G) =
            (((p.1 : F) : H0) : G)⁻¹ * bruhatEval p := by
              dsimp [bruhatEval]
              group
        _ = (((q.1 : F) : H0) : G)⁻¹ * bruhatEval q := by
          rw [hbeta, hevalEq]
        _ = (((q.2.1 : D) : H0) : G) * s *
            (((q.2.2 : F) : H0) : G) := by
              dsimp [bruhatEval]
              group
    let fdiff : F := p.2.2 * q.2.2⁻¹
    have hfdiffVal : (((fdiff : F) : H0) : G) =
        (((p.2.2 : F) : H0) : G) * (((q.2.2 : F) : H0) : G)⁻¹ := by
      rfl
    have hconjEq :
        s * (((fdiff : F) : H0) : G) * s =
          (((p.2.1 : D) : H0) : G)⁻¹ *
            (((q.2.1 : D) : H0) : G) := by
      rw [hfdiffVal]
      calc
        s * ((((p.2.2 : F) : H0) : G) *
              (((q.2.2 : F) : H0) : G)⁻¹) * s =
            (((p.2.1 : D) : H0) : G)⁻¹ *
              ((((p.2.1 : D) : H0) : G) * s *
                (((p.2.2 : F) : H0) : G)) *
                  (((q.2.2 : F) : H0) : G)⁻¹ * s := by group
        _ = (((p.2.1 : D) : H0) : G)⁻¹ *
              ((((q.2.1 : D) : H0) : G) * s *
                (((q.2.2 : F) : H0) : G)) *
                  (((q.2.2 : F) : H0) : G)⁻¹ * s := by rw [hrest]
        _ = ((((p.2.1 : D) : H0) : G)⁻¹ *
              (((q.2.1 : D) : H0) : G)) * (s * s) := by group
        _ = (((p.2.1 : D) : H0) : G)⁻¹ *
              (((q.2.1 : D) : H0) : G) := by rw [hss, mul_one]
    have hconjH : s * (((fdiff : F) : H0) : G) * s ∈ H0 := by
      rw [hconjEq]
      exact (((p.2.1 : D) : H0)⁻¹ * ((q.2.1 : D) : H0)).property
    have hfdiffOne : fdiff = 1 := by
      by_contra hne
      exact hswapKernelNotH fdiff hne hconjH
    have halpha : p.2.2 = q.2.2 := by
      apply mul_inv_eq_one.mp
      exact hfdiffOne
    have hrest' := hrest
    rw [halpha] at hrest'
    have hgammaG :
        (((p.2.1 : D) : H0) : G) = (((q.2.1 : D) : H0) : G) :=
      mul_right_cancel (mul_right_cancel hrest')
    have hgamma : p.2.1 = q.2.1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hgammaG
    exact Prod.ext hbeta (Prod.ext hgamma halpha)
  have hKernelBruhatExistsUnique :
      ∀ x : F, x ≠ 1 →
        ∃! p : F × D × F,
          s * (((x : F) : H0) : G) * s = bruhatEval p := by
    intro x hx
    obtain ⟨p, hp⟩ := hKernelBruhatExists x hx
    exact ⟨p, hp, fun q hq => hKernelBruhatUnique x hx q p hq hp⟩
  let FneOne := {x : F // x ≠ 1}
  choose bruhatCoord hBruhatCoord hBruhatCoordUnique using
    fun x : FneOne => hKernelBruhatExistsUnique x.1 x.2
  let betaRaw : FneOne → F := fun x => (bruhatCoord x).1
  let gamma : FneOne → D := fun x => (bruhatCoord x).2.1
  let alphaRaw : FneOne → F := fun x => (bruhatCoord x).2.2
  have hBruhatFormula (x : FneOne) :
      s * (((x.1 : F) : H0) : G) * s =
        (((betaRaw x : F) : H0) : G) *
          (((gamma x : D) : H0) : G) * s *
            (((alphaRaw x : F) : H0) : G) := by
    simpa [bruhatEval, betaRaw, gamma, alphaRaw] using hBruhatCoord x
  have hAlphaNe (x : FneOne) : alphaRaw x ≠ 1 := by
    intro hAlpha
    have hsxEq :
        s * (((x.1 : F) : H0) : G) =
          (((betaRaw x : F) : H0) : G) *
            (((gamma x : D) : H0) : G) := by
      calc
        s * (((x.1 : F) : H0) : G) =
            (s * (((x.1 : F) : H0) : G) * s) * s := by
              rw [mul_assoc, hss, mul_one]
        _ = ((((betaRaw x : F) : H0) : G) *
              (((gamma x : D) : H0) : G) * s *
                (((alphaRaw x : F) : H0) : G)) * s := by
                  rw [hBruhatFormula]
        _ = (((betaRaw x : F) : H0) : G) *
              (((gamma x : D) : H0) : G) := by
                rw [hAlpha]
                simp [hss, mul_assoc]
    have hsxH : s * (((x.1 : F) : H0) : G) ∈ H0 := by
      rw [hsxEq]
      exact (((betaRaw x : F) : H0) * ((gamma x : D) : H0)).property
    have hsxFix : (s * (((x.1 : F) : H0) : G)) • a = a := hsxH
    have hxFix : (((x.1 : F) : H0) : G) • a = a :=
      ((x.1 : F) : H0).property
    have hba : b = a := by simpa [mul_smul, hxFix, hsa] using hsxFix
    exact hab hba.symm
  have hBetaNe (x : FneOne) : betaRaw x ≠ 1 := by
    intro hBeta
    have hBetaG : (((betaRaw x : F) : H0) : G) = 1 := by
      rw [hBeta]
      rfl
    have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    have hGammaConj :
        s * (((gamma x : D) : H0) : G) * s =
          ((((gamma x : D)⁻¹ : D) : H0) : G) := by
      simpa [hsinv] using hsInvertsD (gamma x)
    have hxsEq :
        (((x.1 : F) : H0) : G) * s =
          ((((gamma x : D)⁻¹ : D) : H0) : G) *
            (((alphaRaw x : F) : H0) : G) := by
      calc
        (((x.1 : F) : H0) : G) * s =
            (s * s) * (((x.1 : F) : H0) : G) * s := by
              rw [hss, one_mul]
        _ = s * (s * (((x.1 : F) : H0) : G) * s) := by group
        _ = s * ((((betaRaw x : F) : H0) : G) *
              (((gamma x : D) : H0) : G) * s *
                (((alphaRaw x : F) : H0) : G)) := by rw [hBruhatFormula]
        _ = ((((gamma x : D)⁻¹ : D) : H0) : G) *
              (((alphaRaw x : F) : H0) : G) := by
                rw [hBetaG, one_mul]
                calc
                  s * ((((gamma x : D) : H0) : G) * s *
                      (((alphaRaw x : F) : H0) : G)) =
                    (s * (((gamma x : D) : H0) : G) * s) *
                      (((alphaRaw x : F) : H0) : G) := by group
                  _ = ((((gamma x : D)⁻¹ : D) : H0) : G) *
                      (((alphaRaw x : F) : H0) : G) := by rw [hGammaConj]
    have hxsH : (((x.1 : F) : H0) : G) * s ∈ H0 := by
      rw [hxsEq]
      exact ((((gamma x : D)⁻¹ : D) : H0) *
        ((alphaRaw x : F) : H0)).property
    have hxsFix : ((((x.1 : F) : H0) : G) * s) • a = a := hxsH
    have hxb : (((x.1 : F) : H0) : G) • b = a := by
      simpa [mul_smul, hsa] using hxsFix
    have hxa : (((x.1 : F) : H0) : G) • a = a :=
      ((x.1 : F) : H0).property
    have hba : b = a :=
      (MulAction.toPerm (((x.1 : F) : H0) : G)).injective (hxb.trans hxa.symm)
    exact hab hba.symm
  let alpha : FneOne → FneOne := fun x => ⟨alphaRaw x, hAlphaNe x⟩
  let beta : FneOne → FneOne := fun x => ⟨betaRaw x, hBetaNe x⟩
  have hAlphaInvolutive (x : FneOne) : alpha (alpha x) = x := by
    apply Subtype.ext
    simpa [alpha, alphaRaw] using
      (xi1115_alpha_bruhat_coordinates H0 F D s hss hactionMain
        bruhatCoord
        (fun y => by simpa [bruhatEval] using hBruhatCoord y)
        (fun y p hp => hBruhatCoordUnique y p (by
          simpa [bruhatEval] using hp))
        (fun y => by simpa [alphaRaw] using hAlphaNe y)
        x).2.2
  have hjne : j ≠ 1 := (orderOf_eq_prime_iff.mp hjorder).2
  have hSpecialCoordinates :
      bruhatCoord ⟨j, hjne⟩ = (g, 1, g⁻¹) ∧
        bruhatCoord ⟨g, hgne⟩ = (j, 1, g) :=
    xi1115_structure_special_bruhat_coordinates H0 F D s hss
      bruhatCoord
      (fun x p hp => hBruhatCoordUnique x p (by
        simpa [bruhatEval] using hp))
      j g hjne hgne hstructureMain
  have hjInvEq : j⁻¹ = j := inv_eq_self_of_orderOf_eq_two hjorder
  have hInverseSpecialCoordinate :
      bruhatCoord ⟨g⁻¹, inv_ne_one.mpr hgne⟩ = (g⁻¹, 1, j) :=
    xi1115_structure_inverse_bruhat_coordinate H0 F D s hss
      (by simpa [H0] using hsInvertsD) bruhatCoord
      (fun x => by simpa [bruhatEval] using hBruhatCoord x)
      (fun x p hp => hBruhatCoordUnique x p (by
        simpa [bruhatEval] using hp))
      j g hjInvEq hgne hSpecialCoordinates.2
  have hActionH : ∀ d : D, ∀ x : F,
      ((d • x : F) : H0) =
        (d : H0) * (x : H0) * (d : H0)⁻¹ := by
    intro d x
    exact Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe
      D F d x
  have hcoordUnique : ∀ (x : FneOne) (p : F × D × F),
      s * (((x.1 : F) : H0) : G) * s =
        (((p.1 : F) : H0) : G) *
          (((p.2.1 : D) : H0) : G) * s *
            (((p.2.2 : F) : H0) : G) →
      p = bruhatCoord x := by
    intro x p hp
    exact hBruhatCoordUnique x p (by
      simpa [bruhatEval] using hp)
  have hbetaCov : ∀ (d : D) (x : FneOne),
      let dx : FneOne := ⟨d • x.1, by
        intro h
        apply x.2
        calc
          x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
          _ = d⁻¹ • 1 := by rw [h]
          _ = 1 := smul_one _⟩
      (bruhatCoord dx).1 = d⁻¹ • (bruhatCoord x).1 := by
    intro d x
    let dx : FneOne := ⟨d • x.1, by
      intro h
      apply x.2
      calc
        x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
        _ = d⁻¹ • 1 := by rw [h]
        _ = 1 := smul_one _⟩
    have hcc := xi1115_conjugate_bruhat_coordinates H0 F D s hss
      (by simpa [H0] using hsInvertsD) hactionMain bruhatCoord
      (fun y => by simpa [bruhatEval] using hBruhatFormula y)
      hcoordUnique d x
    dsimp only [dx] at hcc ⊢
    exact hcc.1
  have hcoordCov : ∀ (d : D) (x : FneOne),
      let dx : FneOne := ⟨d • x.1, by
        intro h
        apply x.2
        calc
          x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
          _ = d⁻¹ • 1 := by rw [h]
          _ = 1 := smul_one _⟩
      bruhatCoord dx =
        (d⁻¹ • (bruhatCoord x).1,
          d⁻¹ * d⁻¹ * (bruhatCoord x).2.1,
          d⁻¹ • (bruhatCoord x).2.2) := by
    intro d x
    let dx : FneOne := ⟨d • x.1, by
      intro h
      apply x.2
      calc
        x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
        _ = d⁻¹ • 1 := by rw [h]
        _ = 1 := smul_one _⟩
    have hcc := xi1115_conjugate_bruhat_coordinates H0 F D s hss
      (by simpa [H0] using hsInvertsD) hactionMain bruhatCoord
      (fun y => by simpa [bruhatEval] using hBruhatFormula y)
      hcoordUnique d x
    dsimp only [dx] at hcc ⊢
    exact Prod.ext hcc.1 (Prod.ext hcc.2.1 hcc.2.2)
  have hproductAlpha :
      ∀ (x₁ x₂ : FneOne)
        (hprod : x₁.1 * x₂.1 ≠ 1)
        (hmiddle : (bruhatCoord x₁).2.2 * (bruhatCoord x₂).1 ≠ 1),
        let x₁₂ : FneOne := ⟨x₁.1 * x₂.1, hprod⟩
        let middle : FneOne :=
          ⟨(bruhatCoord x₁).2.2 * (bruhatCoord x₂).1, hmiddle⟩
        (bruhatCoord x₁₂).2.2 =
          (bruhatCoord x₂).2.1 • (bruhatCoord middle).2.2 *
            (bruhatCoord x₂).2.2 := by
    intro x₁ x₂ hprod hmiddle
    have hproduct := xi1115_product_bruhat_coordinates H0 F D s hss
      (by simpa [H0] using hsInvertsD) hactionMain bruhatCoord
      (fun y => by simpa [bruhatEval] using hBruhatFormula y)
      hcoordUnique x₁ x₂ hprod hmiddle
    dsimp only at hproduct ⊢
    exact hproduct.2.2
  classical
  let alphaTotal : F → F := fun x =>
    if hx : x ≠ 1 then (bruhatCoord ⟨x, hx⟩).2.2 else 1
  let betaTotal : F → F := fun x =>
    if hx : x ≠ 1 then (bruhatCoord ⟨x, hx⟩).1 else 1
  let gammaTotal : F → D := fun x =>
    if hx : x ≠ 1 then (bruhatCoord ⟨x, hx⟩).2.1 else 1
  have halphaCov : ∀ (d : D) (x : F), x ≠ 1 →
      alphaTotal (d • x) = d⁻¹ • alphaTotal x := by
    intro d x hx
    have hdx : d • x ≠ 1 := xi1115_smul_ne_one d hx
    have hcc := hcoordCov d (⟨x, hx⟩ : FneOne)
    dsimp only at hcc
    have halpha := congrArg (fun p : F × D × F => p.2.2) hcc
    simpa only [alphaTotal, dif_pos hx, dif_pos hdx] using halpha
  have halphaGInv : alphaTotal g⁻¹ = j := by
    simp only [alphaTotal, dif_pos (inv_ne_one.mpr hgne),
      hInverseSpecialCoordinate]
  have hbetaJ : betaTotal j = g := by
    simp only [betaTotal, dif_pos hjne, hSpecialCoordinates.1]
  have hgammaJ : gammaTotal j = 1 := by
    simp only [gammaTotal, dif_pos hjne, hSpecialCoordinates.1]
  have halphaJ : alphaTotal j = g⁻¹ := by
    simp only [alphaTotal, dif_pos hjne, hSpecialCoordinates.1]
  have hproductLaw : ∀ x₁ x₂ : F,
      x₁ ≠ 1 → x₂ ≠ 1 → x₁ * x₂ ≠ 1 →
      alphaTotal x₁ * betaTotal x₂ ≠ 1 →
      alphaTotal (x₁ * x₂) =
        gammaTotal x₂ • alphaTotal (alphaTotal x₁ * betaTotal x₂) *
          alphaTotal x₂ := by
    intro x₁ x₂ hx₁ hx₂ hprod hmiddle
    let sx₁ : FneOne := ⟨x₁, hx₁⟩
    let sx₂ : FneOne := ⟨x₂, hx₂⟩
    have hmiddleRaw :
        (bruhatCoord sx₁).2.2 * (bruhatCoord sx₂).1 ≠ 1 := by
      simpa only [alphaTotal, betaTotal, dif_pos hx₁, dif_pos hx₂,
        sx₁, sx₂] using hmiddle
    have hpa := hproductAlpha sx₁ sx₂ hprod hmiddleRaw
    dsimp only at hpa
    simpa only [alphaTotal, betaTotal, gammaTotal, dif_pos hx₁,
      dif_pos hx₂, dif_pos hprod, dif_pos hmiddleRaw, sx₁, sx₂] using hpa
  have hFamily : ∀ h : D, h ≠ 1 →
      ∃ k : D, ∃ hprod : g⁻¹ * (h⁻¹ • g) ≠ 1,
        h⁻¹ • ((h⁻¹ • j) * j) = k⁻¹ • j ∧
          (bruhatCoord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).1 =
            g⁻¹ * ((h * h * k⁻¹)⁻¹ • g) := by
    intro h hh
    obtain ⟨k, hprod, hcentral, hcoordData⟩ :=
      xi1115_structure_conjugate_family_coordinates
        H0 F D hFrobD hDregular hinvolutions hActionH
        s hss (by simpa [H0] using hsInvertsD) hactionMain
        bruhatCoord (fun y => by simpa [bruhatEval] using hBruhatFormula y)
        hcoordUnique hAlphaNe j g hjInv hjcenter hgne
        hSpecialCoordinates.1 hSpecialCoordinates.2
        hInverseSpecialCoordinate h hh
    refine ⟨k, hprod, hcentral, ?_⟩
    simpa only using hcoordData.1
  have hFamilyAlpha : ∀ h : D, h ≠ 1 →
      ∃ k : D,
        h⁻¹ • ((h⁻¹ • j) * j) = k⁻¹ • j ∧
          alphaTotal (g⁻¹ * (h⁻¹ • g)) = (k • g⁻¹) * (h • g) := by
    intro h hh
    obtain ⟨k, hprod, hcentral, hcoordData⟩ :=
      xi1115_structure_conjugate_family_coordinates
        H0 F D hFrobD hDregular hinvolutions hActionH
        s hss (by simpa [H0] using hsInvertsD) hactionMain
        bruhatCoord (fun y => by simpa [bruhatEval] using hBruhatFormula y)
        hcoordUnique hAlphaNe j g hjInv hjcenter hgne
        hSpecialCoordinates.1 hSpecialCoordinates.2
        hInverseSpecialCoordinate h hh
    refine ⟨k, hcentral, ?_⟩
    let r : D := h * h * k⁻¹
    have hkr : h * h * r⁻¹ = k := by
      dsimp only [r]
      rw [mul_inv_rev]
      simp only [inv_inv]
      calc
        h * h * (k * (h * h)⁻¹) = k * ((h * h) * (h * h)⁻¹) := by
          ac_rfl
        _ = k := by simp
    have haction : (h * h) • (r⁻¹ • g⁻¹) = k • g⁻¹ := by
      rw [← mul_smul, hkr]
    rw [show alphaTotal (g⁻¹ * (h⁻¹ • g)) =
        (bruhatCoord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).2.2 by
      simp only [alphaTotal, dif_pos hprod]]
    calc
      (bruhatCoord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).2.2 =
          (h * h) • (r⁻¹ • g⁻¹) * (h • g) := by
            simpa only [r] using hcoordData.2.2
      _ = (k • g⁻¹) * (h • g) := by rw [haction]
  have hnotOrbitJ : ∀ h : D, h ≠ 1 →
      g⁻¹ * (h⁻¹ • g) ∉ MulAction.orbit D g :=
    xi1115_structure_family_not_in_orbit_of_beta_covariance
      theta pairJ eK hPairJOne hPairJInj hPairJMul hPairJAction
      j g gz hPairJj.symm hgPairJ bruhatCoord hgne
      hSpecialCoordinates.2 hbetaCov hFamily

  have hThetaFixed :
      ∀ x : PFAppendixIII.BinaryGaloisField (2 * m + 1),
        theta x = x → x = 0 ∨ x = 1 :=
    xi1115_theta_fixed_points_of_bruhat_product
      theta pairJ eK hPairJOne hPairJInj hPairJMul hPairJAction
      j g gz hPairJj.symm hgPairJ hjne hgne bruhatCoord
      hSpecialCoordinates.1 hSpecialCoordinates.2 hInverseSpecialCoordinate
      hcoordCov hproductAlpha
  have hGz : gz = 0 ∨ gz = 1 :=
    xi1115_rho_zero_or_one_of_orbit_exclusion
      theta pairJ eK hPairJOne hPairJMul hPairJAction hThetaFixed
      g gz hgPairJ hnotOrbitJ

  let K := PFAppendixIII.BinaryGaloisField (2 * m + 1)
  have hBinaryGenerator :
      ∃ a : K,
        Algebra.adjoin (ZMod 2) ({a} : Set K) = ⊤ ∧ a ≠ 0 ∧ a ≠ 1 := by
    simpa only [K] using
      xi1115_exists_binary_generator_ne_zero_one (2 * m + 1) (by omega)
  have hThetaRelationOfAlignedCoordinates
      (pi : K ≃+* K) (pair : K → K → F) (eD : D ≃* Kˣ)
      (hone : pair 0 0 = 1)
      (hsurj : ∀ x : F, ∃ a z, x = pair a z)
      (hinj : ∀ a z b w, pair a z = pair b w → a = b ∧ z = w)
      (hmul : ∀ a z b w,
        pair a z * pair b w = pair (a + b) (z + w + a * pi b))
      (hactor : ∀ d : D, ∀ a z,
        d • pair a z = pair ((eD d : K) * a)
          ((eD d : K) * pi (eD d : K) * z))
      (hj : j = pair 0 1) (hg : g = pair 1 1)
      (hnormInjective : Function.Injective (fun x : K => x * pi x)) :
      ∀ x : K, pi (pi x) = x ^ 2 := by
    have hcover : ∀ x : F, x ≠ 1 →
        (∃ d : D, d⁻¹ • x = j) ∨
        (∃ d : D, d⁻¹ • x = g) ∨
        (∃ d : D, d⁻¹ • x = g⁻¹) ∨
        ∃ d h : D, h ≠ 1 ∧ d⁻¹ • x = g⁻¹ * (h⁻¹ • g) :=
      xi1115_aligned_structure_orbit_cover pi pair eD hone hsurj hmul
        hactor hnormInjective j g hj hg
    have hgeneric : ∀ A Z : K, A ≠ 0 → Z ≠ 0 →
        Z + A * pi A ≠ 0 →
        AlignedGenericAlphaData pi pair alphaTotal A Z := by
      intro A Z hA hZ hB
      exact aligned_generic_alpha_data_of_family pi pair eD hone hinj hmul
        hactor j g hj hg alphaTotal halphaCov hcover hFamilyAlpha
          A Z hA hZ hB
    have buildData (b : K) (hb : b ≠ 0) (hbOne : b ≠ 1) :
        AlignedThetaCoordinateData pi b := by
      obtain ⟨hdataEta, hdataEpsilon⟩ :=
        aligned_xi1114_two_generic_inputs pi hnormInjective pair alphaTotal
          b hb hbOne hgeneric
      let d : D := eD.symm
        (Units.mk0 (pi.symm b) ((map_ne_zero pi.symm).mpr hb))
      have hd : (eD d : K) = pi.symm b := by simp [d]
      have hproduct := aligned_generic_product_identity_of_alpha_laws
        pi pair eD hone hinj hmul hactor j g hj hg alphaTotal betaTotal
        gammaTotal halphaCov halphaGInv hbetaJ hgammaJ halphaJ hproductLaw
        b hb d hd
      exact aligned_theta_coordinate_data_of_generic_product pi
        hnormInjective pair eD hinj hmul hactor alphaTotal b hb hdataEta
        hdataEpsilon d hd hproduct
    obtain ⟨agen, hgenerate, hagen, hagenOne⟩ := hBinaryGenerator
    have hagenPlusZero : agen + 1 ≠ 0 := by
      intro h
      apply hagenOne
      exact (eq_neg_of_add_eq_zero_left h).trans (CharTwo.neg_eq (1 : K))
    have hagenPlusOne : agen + 1 ≠ 1 := by
      intro h
      apply hagen
      have h' := congrArg (fun x : K => x + 1) h
      simpa only [add_assoc, CharTwo.add_self_eq_zero, add_zero] using h'
    exact xi1115_theta_relation_from_generator_and_translate
      (2 * m + 1) (by omega) pi hnormInjective agen hgenerate hagen
      hagenOne (buildData agen hagen hagenOne)
      (buildData (agen + 1) hagenPlusZero hagenPlusOne)
  have hThetaRelationEither :
      ((∀ x : K, theta (theta x) = x ^ 2) ∧ gz = 1) ∨
      ((∀ x : K, theta.symm (theta.symm x) = x ^ 2) ∧ gz = 0) := by
    rcases hGz with hgzZero | hgzOne
    · rcases xi1115_inverse_actor_coordinates
        (2 * m + 1) theta pairJ eK hPairJOne hPairJSurj hPairJInj
          hPairJMul hPairJAction with
        ⟨pairB, eKTheta, hpairOneB, hpairSurjB, hpairInjB,
          hpairMulB, hActorB, hpairBSpec, _heKThetaSpec⟩
      have hjPairB : j = pairB 0 1 := by
        rw [hPairJj.symm, hpairBSpec]
        simp
      have hgPairB : g = pairB 1 1 := by
        calc
          g = pairJ 1 0 := by simpa only [hgzZero] using hgPairJ
          _ = pairB 1 1 := by
            rw [hpairBSpec]
            simp only [map_one, mul_one, CharTwo.add_self_eq_zero]
      right
      refine ⟨?_, hgzZero⟩
      exact hThetaRelationOfAlignedCoordinates theta.symm pairB eKTheta
        hpairOneB hpairSurjB hpairInjB hpairMulB hActorB hjPairB hgPairB
        (twisted_norm_symm_injective theta hTwistedNormInjective)
    · have hgPairJOne : g = pairJ 1 1 := by
        simpa only [hgzOne] using hgPairJ
      left
      refine ⟨?_, hgzOne⟩
      exact hThetaRelationOfAlignedCoordinates theta pairJ eK hPairJOne
        hPairJSurj hPairJInj hPairJMul hPairJAction hPairJj.symm hgPairJOne
        hTwistedNormInjective
  have hCompatibleRootTorusEmbedding :
      ∃ (pi : K ≃+* K) (pair : K → K → F) (eD : D ≃* Kˣ),
        (∀ x, pi (pi x) = x ^ 2) ∧
          Function.Injective (fun x : K => x * pi x) ∧
          pair 0 0 = 1 ∧
          (∀ x : F, ∃ a z, x = pair a z) ∧
          (∀ a z b w, pair a z = pair b w → a = b ∧ z = w) ∧
          (∀ a z b w,
            pair a z * pair b w =
              pair (a + b) (z + w + a * pi b)) ∧
          (∀ d : D, ∀ a z,
            d • pair a z = pair ((eD d : K) * a)
              ((eD d : K) * pi (eD d : K) * z)) ∧
          j = pair 0 1 ∧
          g = pair 1 1 ∧
          ∃ phiF : F →* SuzukiMatrixGroup m,
            Function.Injective phiF ∧
              (∀ a z,
                ((phiF (pair a z) : SuzukiMatrixGroup m) :
                  GL (Fin 4) K) = SuzukiRootGL m a z) ∧
              ∃ phiD : D →* SuzukiMatrixGroup m,
                Function.Injective phiD ∧
                  (∀ d,
                    ((phiD d : SuzukiMatrixGroup m) : GL (Fin 4) K) =
                      SuzukiTorusGL m (eD d)) ∧
                  (∀ d : D, ∀ x : F,
                    phiF (d • x) = phiD d * phiF x * (phiD d)⁻¹) ∧
                  ∃ wstd : SuzukiMatrixGroup m,
                    ((wstd : SuzukiMatrixGroup m) : GL (Fin 4) K) =
                        SuzukiWeylGL m ∧
                      wstd * wstd = 1 ∧
                      (∀ x : SuzukiMatrixGroup m,
                        x ∈ phiF.range ⊔ phiD.range ∨
                          ∃ h₁ h₂ : ↥(phiF.range ⊔ phiD.range),
                            x = (h₁ : SuzukiMatrixGroup m) * wstd *
                              (h₂ : SuzukiMatrixGroup m)) ∧
                      (∀ a z : K,
                        let n := a * z + pi a * a ^ 2 + pi z
                        ∀ hn : n ≠ 0,
                          let s := a * pi a + z
                          let c := n⁻¹ * s
                          let d := n⁻¹ * a + c * pi c
                          let e := n⁻¹ * z
                          let f := n⁻¹ * a
                          let uval := pi n * n⁻¹ ^ 2
                          let u := Units.mk0 uval
                            (mul_ne_zero ((map_ne_zero pi).2 hn)
                              (pow_ne_zero _ (inv_ne_zero hn)))
                          phiF (pair c d) * phiD (eD.symm u) * wstd *
                              phiF (pair e f) =
                            wstd * phiF (pair a z) * wstd) ∧
                      (∀ d : D, wstd * phiD d = phiD d⁻¹ * wstd) ∧
                      wstd ∉ phiF.range ⊔ phiD.range := by
    rcases hThetaRelationEither with
        ⟨hThetaSq, hgzOne⟩ | ⟨hThetaInvSq, hgzZero⟩
    · rcases xi1115_aligned_suzuki_embedding_package
        m hm theta hThetaSq pairJ eK hPairJOne hPairJSurj hPairJInj
          hPairJMul hPairJAction with
        ⟨phiF, hphiF, hphiFSpec, phiD, hphiD, hphiDSpec,
          hcompat, wstd, hwstd, hwstdSq, hBruhat, hSwap⟩
      have hgPairJOne : g = pairJ 1 1 := by
        simpa only [hgzOne] using hgPairJ
      refine ⟨theta, pairJ, eK, hThetaSq, hTwistedNormInjective,
        hPairJOne, hPairJSurj,
        hPairJInj, hPairJMul, hPairJAction, hPairJj.symm,
        hgPairJOne, phiF, hphiF, hphiFSpec,
        phiD, hphiD, hphiDSpec, hcompat, wstd, hwstd, hwstdSq,
        hBruhat, hSwap, ?_, ?_⟩
      · exact xi1115_standard_weyl_torus_relation m eK phiD hphiDSpec
          wstd hwstd
      · exact xi1115_standard_weyl_not_in_borel m pairJ hPairJSurj eK
          phiF phiD hcompat hphiFSpec hphiDSpec wstd hwstd
    · rcases xi1115_inverse_actor_coordinates
        (2 * m + 1) theta pairJ eK hPairJOne hPairJSurj hPairJInj
          hPairJMul hPairJAction with
        ⟨pairB, eKTheta, hpairOneB, hpairSurjB, hpairInjB,
          hpairMulB, hActorB, hpairBSpec, _heKThetaSpec⟩
      have hjPairB : j = pairB 0 1 := by
        rw [hPairJj.symm, hpairBSpec]
        simp
      have hgPairB : g = pairB 1 1 := by
        calc
          g = pairJ 1 0 := by simpa only [hgzZero] using hgPairJ
          _ = pairB 1 1 := by
            rw [hpairBSpec]
            simp only [map_one, mul_one, CharTwo.add_self_eq_zero]
      rcases xi1115_aligned_suzuki_embedding_package
        m hm theta.symm hThetaInvSq pairB eKTheta hpairOneB hpairSurjB
          hpairInjB hpairMulB hActorB with
        ⟨phiF, hphiF, hphiFSpec, phiD, hphiD, hphiDSpec,
          hcompat, wstd, hwstd, hwstdSq, hBruhat, hSwap⟩
      refine ⟨theta.symm, pairB, eKTheta, hThetaInvSq,
        twisted_norm_symm_injective theta hTwistedNormInjective, hpairOneB,
        hpairSurjB, hpairInjB, hpairMulB, hActorB, hjPairB,
        hgPairB, phiF, hphiF, hphiFSpec,
        phiD, hphiD, hphiDSpec, hcompat, wstd, hwstd, hwstdSq,
        hBruhat, hSwap, ?_, ?_⟩
      · exact xi1115_standard_weyl_torus_relation m eKTheta phiD
          hphiDSpec wstd hwstd
      · exact xi1115_standard_weyl_not_in_borel m pairB hpairSurjB
          eKTheta phiF phiD hcompat hphiFSpec hphiDSpec wstd hwstd
  obtain ⟨piAligned, pairAligned, eDAligned, hpiAlignedSq,
      hTwistedNormInjectiveAligned,
      hpairAlignedOne, hpairAlignedSurj, hpairAlignedInj,
      hpairAlignedMul, hpairAlignedAction, hjPairAligned,
      hgPairAligned, phiF, hphiF, hphiFSpecAligned,
      phiD, hphiD, hphiDSpecAligned, hRootTorusCompatibility,
      wstdAligned, hwstdAligned, hwstdAlignedSq, hStandardBruhatFD,
      hStandardSwapAligned, hTargetWeylInvertsD,
      hwstdAlignedNotB⟩ := hCompatibleRootTorusEmbedding
  let rho : D →* MulAut F :=
    (F.normalizerMonoidHom).comp (Subgroup.inclusion (F.normalizer_eq_top ▸ le_top))
  let eH : F ⋊[rho] D ≃* H0 := by
    simpa [rho, H0] using
      (SemidirectProduct.mulEquivSubgroup hFrobD.isComplement')
  have hPointStabilizerEmbedding :
      ∃ phiH : H0 →* SuzukiMatrixGroup m,
        Function.Injective phiH ∧
          (∀ x : F,
            phiH (eH (SemidirectProduct.inl x)) = phiF x) ∧
          ∀ d : D,
            phiH (eH (SemidirectProduct.inr d)) = phiD d := by
    exact xi1115_pointStabilizer_embedding_of_compatible
      eH hF2 hDodd phiF phiD hphiF hphiD
      hRootTorusCompatibility
  obtain ⟨phiH, hphiH, hphiHOnF, hphiHOnD⟩ :=
    hPointStabilizerEmbedding
  have hphiHRange : phiH.range = phiF.range ⊔ phiD.range := by
    apply le_antisymm
    · intro y hy
      rcases hy with ⟨h, rfl⟩
      obtain ⟨z, rfl⟩ := eH.surjective h
      have hvalue :
          phiH (eH z) = phiF z.left * phiD z.right := by
        calc
          phiH (eH z) =
              phiH (eH
                (SemidirectProduct.inl z.left *
                  SemidirectProduct.inr z.right)) := by
                rw [SemidirectProduct.inl_left_mul_inr_right]
          _ = phiH
                (eH (SemidirectProduct.inl z.left) *
                  eH (SemidirectProduct.inr z.right)) := by
                rw [map_mul]
          _ = phiH (eH (SemidirectProduct.inl z.left)) *
                phiH (eH (SemidirectProduct.inr z.right)) := by
                rw [map_mul]
          _ = phiF z.left * phiD z.right := by
                rw [hphiHOnF, hphiHOnD]
      rw [hvalue]
      exact (phiF.range ⊔ phiD.range).mul_mem
        ((show phiF.range ≤ phiF.range ⊔ phiD.range from le_sup_left)
          ⟨z.left, rfl⟩)
        ((show phiD.range ≤ phiF.range ⊔ phiD.range from le_sup_right)
          ⟨z.right, rfl⟩)
    · refine sup_le ?_ ?_
      · rintro y ⟨x, rfl⟩
        exact ⟨eH (SemidirectProduct.inl x), hphiHOnF x⟩
      · rintro y ⟨d, rfl⟩
        exact ⟨eH (SemidirectProduct.inr d), hphiHOnD d⟩
  have hpointStabilizerStandard :
      ∃ Bstd : Subgroup (SuzukiMatrixGroup m),
        Nonempty (H0 ≃* Bstd) := by
    let Bstd : Subgroup (SuzukiMatrixGroup m) := phiH.range
    refine ⟨Bstd, ⟨MulEquiv.ofBijective phiH.rangeRestrict ?_⟩⟩
    exact ⟨fun _ _ h => hphiH (congrArg Subtype.val h),
      phiH.rangeRestrict_surjective⟩
  have hAmbientBruhat :
      ∀ x : G,
        x ∈ H0 ∨
          ∃ h₁ h₂ : H0, x = (h₁ : G) * s * (h₂ : G) := by
    letI : MulAction.IsMultiplyPretransitive G Omega 2 := htwo_transitive
    letI : MulAction.IsPretransitive G Omega :=
      MulAction.isPretransitive_of_is_two_pretransitive
    have hstabPretrans :
        MulAction.IsPretransitive H0 (SubMulAction.ofStabilizer G a) := by
      exact (MulAction.is_one_pretransitive_iff
        (G := H0) (α := SubMulAction.ofStabilizer G a)).mp
          ((SubMulAction.ofStabilizer.isMultiplyPretransitive
            (G := G) (a := a)).mp htwo_transitive)
    intro x
    by_cases hxa : x • a = a
    · left
      exact hxa
    · right
      let xa : SubMulAction.ofStabilizer G a := ⟨x • a, hxa⟩
      let ba : SubMulAction.ofStabilizer G a := ⟨b, hab.symm⟩
      obtain ⟨h₁, hh₁⟩ := hstabPretrans.exists_smul_eq ba xa
      have hh₁G : (h₁ : G) • b = x • a := by
        exact congrArg Subtype.val hh₁
      let h₂G : G := s⁻¹ * (h₁ : G)⁻¹ * x
      have hh₂fix : h₂G • a = a := by
        calc
          h₂G • a = s⁻¹ • ((h₁ : G)⁻¹ • (x • a)) := by
            simp only [h₂G, mul_smul]
          _ = s⁻¹ • b := by rw [← hh₁G, inv_smul_smul]
          _ = a := by rw [← hsa, inv_smul_smul]
      let h₂ : H0 := ⟨h₂G, hh₂fix⟩
      refine ⟨h₁, h₂, ?_⟩
      dsimp [h₂, h₂G]
      group
  have heHInl (x : F) :
      eH (SemidirectProduct.inl x) = F.subtype x := by
    simp only [eH, rho, H0, id_eq]
    calc
      (SemidirectProduct.mulEquivSubgroup hFrobD.isComplement')
          (SemidirectProduct.inl x) =
          (x : H0) * (1 : D) :=
        SemidirectProduct.mulEquivSubgroup_apply
          hFrobD.isComplement' (SemidirectProduct.inl x)
      _ = F.subtype x := by simp
  have heHInr (d : D) :
      eH (SemidirectProduct.inr d) = D.subtype d := by
    simp only [eH, rho, H0, id_eq]
    calc
      (SemidirectProduct.mulEquivSubgroup hFrobD.isComplement')
          (SemidirectProduct.inr d) =
          (1 : F) * (d : H0) :=
        SemidirectProduct.mulEquivSubgroup_apply
          hFrobD.isComplement' (SemidirectProduct.inr d)
      _ = D.subtype d := by simp
  have hphiHOnF' (x : F) : phiH (F.subtype x) = phiF x := by
    rw [← heHInl]
    exact hphiHOnF x
  have hphiHOnD' (d : D) : phiH (D.subtype d) = phiD d := by
    rw [← heHInr]
    exact hphiHOnD d
  have hSplitRight : ∀ h : H0, ∃ d : D, ∃ f : F,
      h = D.subtype d * F.subtype f := by
    intro h
    obtain ⟨z, rfl⟩ := eH.surjective h
    let d : D := z.right
    let f : F := d⁻¹ • z.left
    refine ⟨d, f, ?_⟩
    calc
      eH z = (z.left : H0) * (z.right : H0) := by
        simp only [eH, rho, H0, id_eq]
        exact SemidirectProduct.mulEquivSubgroup_apply
          hFrobD.isComplement' _
      _ = (d : H0) * (f : H0) := by
        dsimp only [d, f]
        rw [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe]
        simp only [Subgroup.coe_inv]
        group
  have hSD : ∀ d : D,
      s * (((d : D) : H0) : G) = (((d⁻¹ : D) : H0) : G) * s := by
    intro d
    have hsInv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
    calc
      s * (((d : D) : H0) : G) =
          (s * (((d : D) : H0) : G) * s⁻¹) * s := by
        rw [hsInv]
        nth_rw 1 [← mul_one (s * (((d : D) : H0) : G))]
        rw [← hss]
        group
      _ = (((d⁻¹ : D) : H0) : G) * s := by
        simpa [H0] using congrArg (fun z : G => z * s) (hsInvertsD d)
  have hsNotH : s ∉ H0 := by
    intro hsH
    have hsfix : s • a = a := hsH
    exact hab (hsfix.symm.trans hsa)
  have hBig : ∀ (x : G), x ∉ H0 →
      ∃! p : H0 × F, x = xi1115_bruhatEval H0 F s p :=
    xi1115_existsUnique_bruhatEval H0 F D s hss hAmbientBruhat
      hSplitRight hSD hswapKernelNotH
  have hAligned : ∀ x : FneOne,
      phiF (bruhatCoord x).1 * phiD (bruhatCoord x).2.1 *
          wstdAligned * phiF (bruhatCoord x).2.2 =
        wstdAligned * phiF x.1 * wstdAligned := by
    classical
    have hcov : ∀ (d : D) (x : FneOne),
        phiF (bruhatCoord x).1 * phiD (bruhatCoord x).2.1 *
            wstdAligned * phiF (bruhatCoord x).2.2 =
          wstdAligned * phiF x.1 * wstdAligned →
        let dx : FneOne := ⟨d • x.1, by
          intro h
          apply x.2
          calc
            x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
            _ = d⁻¹ • 1 := by rw [h]
            _ = 1 := smul_one _⟩
        phiF (bruhatCoord dx).1 * phiD (bruhatCoord dx).2.1 *
            wstdAligned * phiF (bruhatCoord dx).2.2 =
          wstdAligned * phiF dx.1 * wstdAligned := by
      intro d x hx
      let dx : FneOne := ⟨d • x.1, by
        intro h
        apply x.2
        calc
          x.1 = d⁻¹ • (d • x.1) := (inv_smul_smul d x.1).symm
          _ = d⁻¹ • 1 := by rw [h]
          _ = 1 := smul_one _⟩
      have hccRaw : (bruhatCoord dx).1 = d⁻¹ • (bruhatCoord x).1 ∧
          (bruhatCoord dx).2.1 = d⁻¹ * d⁻¹ * (bruhatCoord x).2.1 ∧
          (bruhatCoord dx).2.2 = d⁻¹ • (bruhatCoord x).2.2 :=
        xi1115_conjugate_bruhat_coordinates H0 F D s hss
          (by simpa [H0] using hsInvertsD) hactionMain bruhatCoord
          (fun y => by simpa [bruhatEval] using hBruhatFormula y)
          hcoordUnique d x
      have hcc : bruhatCoord dx =
          (d⁻¹ • (bruhatCoord x).1,
            d⁻¹ * d⁻¹ * (bruhatCoord x).2.1,
            d⁻¹ • (bruhatCoord x).2.2) := by
        exact Prod.ext hccRaw.1 (Prod.ext hccRaw.2.1 hccRaw.2.2)
      dsimp only [dx] at hcc ⊢
      exact xi1115_swap_formula_smul bruhatCoord phiF phiD wstdAligned
        hRootTorusCompatibility hTargetWeylInvertsD d x dx rfl hcc hx
    have hpairAlignedInv :
        pairAligned 1 0 = (pairAligned 1 1)⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      calc
        pairAligned 1 0 * pairAligned 1 1 =
            pairAligned (1 + 1) (0 + 1 + 1 * piAligned 1) := hpairAlignedMul 1 0 1 1
        _ = pairAligned 0 0 := by
          simp [map_one, CharTwo.add_self_eq_zero]
        _ = 1 := hpairAlignedOne
    have hphiPairAlignedInv :
        phiF (pairAligned 1 0) = (phiF (pairAligned 1 1))⁻¹ := by
      set_option synthInstance.maxHeartbeats 0 in
      calc
        phiF (pairAligned 1 0) = phiF ((pairAligned 1 1)⁻¹) := by rw [hpairAlignedInv]
        _ = (phiF (pairAligned 1 1))⁻¹ := map_inv _ _
    have hJswap :
        phiF (bruhatCoord ⟨j, hjne⟩).1 *
            phiD (bruhatCoord ⟨j, hjne⟩).2.1 * wstdAligned *
            phiF (bruhatCoord ⟨j, hjne⟩).2.2 =
          wstdAligned * phiF j * wstdAligned := by
      rw [hSpecialCoordinates.1, hjPairAligned, hgPairAligned]
      simpa [map_zero, map_one, CharTwo.add_self_eq_zero,
        hphiPairAlignedInv] using
        (hStandardSwapAligned 0 1 (by simp))
    have hGswap :
        phiF (bruhatCoord ⟨g, hgne⟩).1 *
            phiD (bruhatCoord ⟨g, hgne⟩).2.1 * wstdAligned *
            phiF (bruhatCoord ⟨g, hgne⟩).2.2 =
          wstdAligned * phiF g * wstdAligned := by
      rw [hSpecialCoordinates.2, hjPairAligned, hgPairAligned]
      simpa [map_zero, map_one, CharTwo.add_self_eq_zero] using
        (hStandardSwapAligned 1 1 (by simp [CharTwo.add_self_eq_zero]))
    have hGiswap :
        phiF (bruhatCoord ⟨g⁻¹, inv_ne_one.mpr hgne⟩).1 *
            phiD (bruhatCoord ⟨g⁻¹, inv_ne_one.mpr hgne⟩).2.1 * wstdAligned *
            phiF (bruhatCoord ⟨g⁻¹, inv_ne_one.mpr hgne⟩).2.2 =
          wstdAligned * phiF g⁻¹ * wstdAligned := by
      rw [hInverseSpecialCoordinate, hjPairAligned, hgPairAligned]
      simpa [map_zero, map_one, CharTwo.add_self_eq_zero,
        hphiPairAlignedInv] using
        (hStandardSwapAligned 1 0 (by simp))
    have hS : ∀ h : D, h ≠ 1 →
        ∃ hprod : g⁻¹ * (h⁻¹ • g) ≠ 1,
          phiF (bruhatCoord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).1 *
              phiD (bruhatCoord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).2.1 *
                wstdAligned *
              phiF (bruhatCoord ⟨g⁻¹ * (h⁻¹ • g), hprod⟩).2.2 =
            wstdAligned * phiF (g⁻¹ * (h⁻¹ • g)) * wstdAligned := by
      intro h hh
      obtain ⟨k, hprod, hcentral, hcoordData⟩ :=
        xi1115_structure_conjugate_family_coordinates
          H0 F D hFrobD hDregular hinvolutions hActionH
          s hss (by simpa [H0] using hsInvertsD) hactionMain
          bruhatCoord (fun y => by simpa [bruhatEval] using hBruhatFormula y)
          hcoordUnique hAlphaNe j g hjInv hjcenter hgne
          hSpecialCoordinates.1 hSpecialCoordinates.2
          hInverseSpecialCoordinate h hh
      have hnNe :
          let lambda : K := (eDAligned h : K)⁻¹
          1 + lambda ^ 2 * piAligned lambda ≠ 0 := by
        dsimp only
        let lambda : K := (eDAligned h : K)⁻¹
        change 1 + lambda ^ 2 * piAligned lambda ≠ 0
        have hlambda : lambda ≠ 0 := by
          dsimp [lambda]
          exact inv_ne_zero (eDAligned h).ne_zero
        have hlambdaOne : lambda ≠ 1 := by
          intro hlambdaEq
          apply hh
          apply eDAligned.injective
          apply Units.ext
          have heh : (eDAligned h : K) = 1 :=
            inv_eq_one.mp hlambdaEq
          simpa [lambda] using heh
        intro hn
        let z : K := lambda * piAligned lambda + piAligned lambda
        have hzNorm :
            (1 + lambda) * z + piAligned (1 + lambda) *
                (1 + lambda) ^ 2 + piAligned z = 0 := by
          calc
            (1 + lambda) * z + piAligned (1 + lambda) *
                  (1 + lambda) ^ 2 + piAligned z =
                1 + lambda ^ 2 * piAligned lambda := by
              simpa only [z] using
                (xi1115_char_two_ovoid_norm_translate
                  piAligned hpiAlignedSq lambda)
            _ = 0 := hn
        have hzeroPair : (1 + lambda) = 0 ∧ z = 0 :=
          (suzukiOvoidNorm_eq_zero m piAligned hpiAlignedSq
            (1 + lambda) z).mp hzNorm
        have honeLambda : lambda = 1 := by
          exact ((eq_neg_of_add_eq_zero_left hzeroPair.1).trans
            (CharTwo.neg_eq lambda)).symm
        exact hlambdaOne honeLambda
      refine ⟨hprod, ?_⟩
      exact xi1115_structure_swap piAligned pairAligned eDAligned
        hpairAlignedOne hpairAlignedInj hpairAlignedMul hpairAlignedAction
        hpiAlignedSq hTwistedNormInjectiveAligned j g hjPairAligned
        hgPairAligned
        phiF phiD wstdAligned hStandardSwapAligned bruhatCoord h k hh hprod
        hcentral hcoordData hnNe
    intro x
    apply xi1115_orbit_cover_propagation bruhatCoord phiF phiD wstdAligned
      j g hjne hgne hcov hJswap hGswap hGiswap hS x
    exact xi1115_aligned_structure_orbit_cover piAligned pairAligned
      eDAligned hpairAlignedOne hpairAlignedSurj hpairAlignedMul
      hpairAlignedAction hTwistedNormInjectiveAligned j g hjPairAligned
      hgPairAligned x.1 x.2
  have hSwapCoordTarget : ∀ (x : F) (hx : x ≠ 1),
      let p := xi1115_bruhatCoord H0 F s hBig
        (s * (((x : F) : H0) : G) * s) (hswapKernelNotH x hx)
      phiH p.1 * wstdAligned * phiH (F.subtype p.2) =
        wstdAligned * phiH (F.subtype x) * wstdAligned := by
    intro x hx
    let x0 : FneOne := ⟨x, hx⟩
    let q : H0 × F :=
      (F.subtype (bruhatCoord x0).1 *
          D.subtype (bruhatCoord x0).2.1,
        (bruhatCoord x0).2.2)
    have hq :
        s * (((x : F) : H0) : G) * s =
          xi1115_bruhatEval H0 F s q := by
      simpa [x0, xi1115_bruhatEval, q, Subgroup.coe_mul,
        Prod.fst, Prod.snd, Subtype.coe_mk] using hBruhatCoord x0
    let p := xi1115_bruhatCoord H0 F s hBig
      (s * (((x : F) : H0) : G) * s) (hswapKernelNotH x hx)
    have hpq : p = q :=
      ((Classical.choose_spec
        (hBig (s * (((x : F) : H0) : G) * s)
          (hswapKernelNotH x hx))).2 q hq).symm
    change phiH p.1 * wstdAligned * phiH (F.subtype p.2) = _
    rw [hpq]
    simp only [q, map_mul]
    rw [hphiHOnF', hphiHOnD', hphiHOnF', hphiHOnF']
    exact hAligned x0
  have hWD : ∀ d : D,
      wstdAligned * phiH (D.subtype d) =
        phiH (D.subtype d⁻¹) * wstdAligned := by
    intro d
    rw [hphiHOnD', hphiHOnD']
    exact hTargetWeylInvertsD d
  have hwstdNotRange : wstdAligned ∉ phiH.range := by
    rw [hphiHRange]
    exact hwstdAlignedNotB
  have hTargetBigOut : ∀ p : H0 × F,
      phiH p.1 * wstdAligned * phiH (F.subtype p.2) ∉
        phiH.range :=
    xi1115_target_bruhatEval_not_range H0 F phiH wstdAligned
      hwstdNotRange
  have hSwapTargetNotRange : ∀ (x : F), x ≠ 1 →
      wstdAligned * phiH (F.subtype x) * wstdAligned ∉
        phiH.range := by
    intro x hx hmem
    let p := xi1115_bruhatCoord H0 F s hBig
      (s * (((x : F) : H0) : G) * s) (hswapKernelNotH x hx)
    have hp := hSwapCoordTarget x hx
    change phiH p.1 * wstdAligned * phiH (F.subtype p.2) = _ at hp
    apply hTargetBigOut p
    rw [hp]
    exact hmem
  have hTargetBigInj : Function.Injective (fun p : H0 × F =>
      phiH p.1 * wstdAligned * phiH (F.subtype p.2)) :=
    xi1115_target_bruhatEval_injective H0 F phiH wstdAligned
      hphiH hwstdAlignedSq hSwapTargetNotRange
  let transport : G → SuzukiMatrixGroup m :=
    xi1115_bruhatTransport H0 F s phiH wstdAligned hBig
  have hSwapF : ∀ x : F,
      transport (s * (((x : F) : H0) : G) * s) =
        wstdAligned * phiH (F.subtype x) * wstdAligned := by
    exact xi1115_bruhatTransport_swap_F H0 F s phiH wstdAligned
      hss hwstdAlignedSq hBig hswapKernelNotH hSwapCoordTarget
  have hSwapH : ∀ h : H0,
      transport (s * (h : G) * s) =
        wstdAligned * phiH h * wstdAligned := by
    exact xi1115_bruhatTransport_swap_H H0 F D s phiH wstdAligned
      hSplitRight hSD hWD hBig hSwapF
  have hLeftS : ∀ x : G,
      transport (s * x) = wstdAligned * transport x := by
    exact xi1115_bruhatTransport_left_s H0 F D s phiH wstdAligned
      hsNotH hSplitRight hSD hWD hBig hSwapH
  have hTransportInjective : Function.Injective transport := by
    exact xi1115_bruhatTransport_injective H0 F s phiH wstdAligned
      hphiH hBig hTargetBigOut hTargetBigInj
  have hStandardBruhat : ∀ x : SuzukiMatrixGroup m,
      x ∈ phiH.range ∨
        ∃ h₁ h₂ : phiH.range,
          x = (h₁ : SuzukiMatrixGroup m) * wstdAligned *
            (h₂ : SuzukiMatrixGroup m) := by
    rw [hphiHRange]
    exact hStandardBruhatFD
  have hBruhatHom :
      ∃ Phi : G →* SuzukiMatrixGroup m,
        Function.Injective Phi ∧
        (∀ h : H0, Phi (h : G) = phiH h) ∧
        Phi s = wstdAligned := by
    exact xi1115_bruhatHom_of_left_equivariance H0 s phiH
      wstdAligned transport
      (xi1115_bruhatTransport_on_H H0 F s phiH wstdAligned hBig)
      (xi1115_bruhatTransport_left_H H0 F s phiH wstdAligned hBig)
      hLeftS hAmbientBruhat hTransportInjective
  obtain ⟨Phi, hPhiInjective, hPhiH, hPhiS⟩ := hBruhatHom
  have hSuzukiCard :
      Nat.card G = Nat.card (SuzukiMatrixGroup m) := by
    have hFcard : Nat.card F = (2 ^ (2 * m + 1)) ^ 2 := by
      calc
        Nat.card F = Nat.card (Subgroup.center F) ^ 2 := hFcardCenterSq
        _ = (2 ^ (2 * m + 1)) ^ 2 := by rw [hZcard]
    calc
      Nat.card G = ((2 ^ (2 * m + 1)) ^ 2 + 1) * (2 ^ (2 * m + 1)) ^ 2 * (2 ^ (2 * m + 1) - 1) := by
        rw [hGcardMain, hFcard]
      _ = Nat.card (SuzukiMatrixGroup m) := by
        rw [xi1115_suzukiMatrixGroup_card_formula m hm]
  have hPhiBijective : Function.Bijective Phi := by
    exact (Nat.bijective_iff_injective_and_card Phi).2
      ⟨hPhiInjective, hSuzukiCard⟩
  have hbruhatExtension :
      (∃ Bstd : Subgroup (SuzukiMatrixGroup m),
          Nonempty (H0 ≃* Bstd)) →
        Nonempty (G ≃* SuzukiMatrixGroup m) := by
    intro _
    exact ⟨MulEquiv.ofBijective Phi hPhiBijective⟩
  exact ⟨m, hm, hbruhatExtension hpointStabilizerStandard⟩

end External
end CFSG.BenderSuzuki
