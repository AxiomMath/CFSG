module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Higman.lemma_4
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.Algebra.Polynomial.Module.AEval
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.Finite.Trace
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.TensorProduct.Maps

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped TensorProduct
open scoped commutatorElement
open scoped IsMulCommutative

/-!
# Higman Lemma 5
-/

namespace CFSG.BenderSuzuki
namespace External
namespace Higman

open PFAppendixIII

universe u

local notation "F2" => ZMod 2

set_option backward.isDefEq.respectTransparency false in
private theorem lemma5_irreducible_AEval_isSimple
    {V : Type u} [AddCommGroup V] [Module F2 V] [Nontrivial V]
    (T : V ≃ₗ[F2] V)
    (hT_irreducible :
      ∀ W : Submodule F2 V,
        (∀ v : V, v ∈ W → T v ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    IsSimpleModule (Polynomial F2) (Module.AEval' (R := F2) T.toLinearMap) := by
  letI : Nontrivial (Module.AEval' (R := F2) T.toLinearMap) := ‹Nontrivial V›
  rw [isSimpleModule_iff]
  refine
    { toNontrivial := inferInstance
      eq_bot_or_eq_top := ?_ }
  intro W
  let eSub := Module.AEval.mapSubmodule F2 V T.toLinearMap
  let W0 := eSub.symm W
  have hW0_invariant :
      ∀ v : V, v ∈ (W0 : Submodule F2 V) →
        T v ∈ (W0 : Submodule F2 V) := by
    intro v hv
    exact W0.property hv
  rcases hT_irreducible (W0 : Submodule F2 V) hW0_invariant with hW0 | hW0
  · left
    apply eSub.symm.injective
    have hW0' : W0 = (⊥ : (Algebra.lsmul F2 F2 V T.toLinearMap).invtSubmodule) := by
      apply Subtype.ext
      exact hW0
    simpa [W0] using hW0'
  · right
    apply eSub.symm.injective
    have hW0' : W0 = (⊤ : (Algebra.lsmul F2 F2 V T.toLinearMap).invtSubmodule) := by
      apply Subtype.ext
      exact hW0
    simpa [W0] using hW0'


set_option backward.isDefEq.respectTransparency false in
private theorem lemma5_irreducible_field_coordinates
    {V : Type u} [AddCommGroup V] [Module F2 V] [Nontrivial V]
    [Finite V] [Module.Finite F2 V]
    (T : V ≃ₗ[F2] V)
    (hT_irreducible :
      ∀ W : Submodule F2 V,
        (∀ v : V, v ∈ W → T v ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    ∃ (m : ℕ) (_hm : 0 < m)
      (lambda : BinaryGaloisField m)
      (coordinates : BinaryGaloisField m ≃ₗ[F2] V),
      Nat.card V = 2 ^ m ∧
      lambda ≠ 0 ∧
      ∀ alpha : BinaryGaloisField m,
        T (coordinates alpha) = coordinates (lambda * alpha) := by
  let m := Module.finrank F2 V
  have hm : 0 < m := Module.finrank_pos
  have hVcard : Nat.card V = 2 ^ m := by
    simpa [m, Nat.card_zmod] using
      (Module.natCard_eq_pow_finrank (K := F2) (V := V))
  have hsimple := lemma5_irreducible_AEval_isSimple T hT_irreducible
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
  letI : I.IsMaximal := hI
  letI : Field (Polynomial F2 ⧸ I) := Ideal.Quotient.field I
  let eF2 : V ≃ₗ[F2] Polynomial F2 ⧸ I :=
    (Module.AEval'.of T.toLinearMap).trans (e.restrictScalars F2)
  have hQcard : Nat.card (Polynomial F2 ⧸ I) = 2 ^ m := by
    calc
      Nat.card (Polynomial F2 ⧸ I) = Nat.card V :=
        Nat.card_congr eF2.symm.toEquiv
      _ = 2 ^ m := hVcard
  let qToK : (Polynomial F2 ⧸ I) ≃ₐ[F2] BinaryGaloisField m :=
    GaloisField.algEquivGaloisField 2 m hQcard
  let coordinates : BinaryGaloisField m ≃ₗ[F2] V :=
    qToK.toLinearEquiv.symm.trans eF2.symm
  let lambda : BinaryGaloisField m :=
    qToK (Ideal.Quotient.mk I Polynomial.X)
  have hcoordinates :
      ∀ alpha : BinaryGaloisField m,
        T (coordinates alpha) = coordinates (lambda * alpha) := by
    intro alpha
    apply eF2.injective
    change e (Module.AEval'.of T.toLinearMap
        (T.toLinearMap (coordinates alpha))) =
      e (Module.AEval'.of T.toLinearMap (coordinates (lambda * alpha)))
    rw [← Module.AEval'.X_smul_of, e.map_smul]
    simp [coordinates, lambda, eF2, qToK, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq]
  have hlambda : lambda ≠ 0 := by
    intro hlambda
    have hTzero : T (coordinates (1 : BinaryGaloisField m)) = 0 := by
      simpa [hlambda] using hcoordinates (1 : BinaryGaloisField m)
    have hcoordzero : coordinates (1 : BinaryGaloisField m) = 0 := by
      apply T.injective
      exact hTzero.trans T.map_zero.symm
    exact one_ne_zero (coordinates.injective (hcoordzero.trans coordinates.map_zero.symm))
  exact ⟨m, hm, lambda, coordinates, hVcard, hlambda, hcoordinates⟩

set_option backward.isDefEq.respectTransparency false in
/-- If an irreducible binary linear automorphism has order dividing `2 ^ n - 1`,
then the dimension of its module divides `n`. -/
public theorem lemma5_irreducible_finrank_dvd_of_order_dvd
    {V : Type u} [AddCommGroup V] [Module F2 V] [Nontrivial V]
    [Finite V] [Module.Finite F2 V]
    (T : V ≃ₗ[F2] V)
    (hT_irreducible :
      ∀ W : Submodule F2 V,
        (∀ v : V, v ∈ W → T v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (n : ℕ) (hT_order : orderOf T ∣ 2 ^ n - 1) :
    Module.finrank F2 V ∣ n := by
  obtain ⟨m, hm, lambda, coordinates, _hV_card, hlambda,
      hcoordinates⟩ :=
    lemma5_irreducible_field_coordinates T hT_irreducible
  let K := BinaryGaloisField m
  let lambdaUnit : Kˣ := Units.mk0 lambda hlambda
  have hT_pow_apply : ∀ k : ℕ, ∀ alpha : K,
      (T ^ k) (coordinates alpha) =
        coordinates ((lambdaUnit ^ k : Kˣ) * alpha) := by
    intro k
    induction k with
    | zero =>
        intro alpha
        simp
    | succ k ih =>
        intro alpha
        simpa only [pow_succ, LinearEquiv.mul_apply, Units.val_mul] using
          (calc
            (T ^ k) (T (coordinates alpha)) =
                (T ^ k) (coordinates (lambda * alpha)) := by
                  rw [hcoordinates]
            _ = coordinates ((lambdaUnit ^ k : Kˣ) *
                  (lambda * alpha)) := ih (lambda * alpha)
            _ = coordinates
                (((lambdaUnit ^ k * lambdaUnit : Kˣ) : K) * alpha) := by
              congr 1
              simp only [lambdaUnit, Units.val_mul, Units.val_mk0]
              rw [mul_assoc])
  have hlambdaUnit_pow : lambdaUnit ^ (2 ^ n - 1) = 1 := by
    have hT_pow : T ^ (2 ^ n - 1) = 1 :=
      (orderOf_dvd_iff_pow_eq_one).1 hT_order
    apply Units.ext
    have hpow := LinearEquiv.congr_fun hT_pow (coordinates (1 : K))
    rw [hT_pow_apply] at hpow
    simpa using coordinates.injective hpow
  have hlambda_pow : lambda ^ (2 ^ n) = lambda := by
    have hpow := congrArg (fun z : Kˣ => (z : K)) hlambdaUnit_pow
    change lambda ^ (2 ^ n - 1) = 1 at hpow
    have htwo_pow_pos : 0 < 2 ^ n := pow_pos (by omega) n
    calc
      lambda ^ (2 ^ n) = lambda ^ (2 ^ n - 1 + 1) := by
        congr 1
        omega
      _ = lambda ^ (2 ^ n - 1) * lambda := by rw [pow_succ]
      _ = lambda := by rw [hpow, one_mul]
  let frob : K →ₐ[F2] K := FiniteField.frobeniusAlgHom F2 K
  let F : K →ₐ[F2] K := frob ^ n
  have hF_lambda : F lambda = lambda := by
    dsimp [F]
    rw [congrFun (AlgHom.coe_pow frob n) lambda]
    rw [show (frob : K → K) = fun x => x ^ 2 by
      exact FiniteField.coe_frobeniusAlgHom F2 K]
    rw [pow_iterate]
    exact hlambda_pow
  let A : Submodule F2 K := (F.toLinearMap - LinearMap.id).ker
  have hA_one : (1 : K) ∈ A := by
    rw [LinearMap.mem_ker]
    simp [F]
  have hA_lambda_mul : ∀ x : K, x ∈ A → lambda * x ∈ A := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    change F x - x = 0 at hx
    change F (lambda * x) - lambda * x = 0
    rw [map_mul, hF_lambda, sub_eq_zero]
    exact congrArg (lambda * ·) (sub_eq_zero.mp hx)
  let AV : Submodule F2 V := Submodule.map coordinates.toLinearMap A
  have hAV_invariant : ∀ x : V, x ∈ AV → T x ∈ AV := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨alpha, halpha, rfl⟩ := hx
    refine ⟨lambda * alpha, hA_lambda_mul alpha halpha, ?_⟩
    exact (hcoordinates alpha).symm
  have hAV_ne_bot : AV ≠ ⊥ := by
    intro hbot
    have hone_mem : coordinates (1 : K) ∈ AV := by
      rw [Submodule.mem_map]
      exact ⟨1, hA_one, rfl⟩
    rw [hbot, Submodule.mem_bot] at hone_mem
    exact one_ne_zero (coordinates.injective
      (hone_mem.trans coordinates.map_zero.symm))
  have hAV_top : AV = ⊤ :=
    (hT_irreducible AV hAV_invariant).resolve_left hAV_ne_bot
  have hF_eq_one : F = 1 := by
    apply DFunLike.ext _ _
    intro alpha
    have halpha_mem : coordinates alpha ∈ AV := by
      rw [hAV_top]
      trivial
    rw [Submodule.mem_map] at halpha_mem
    obtain ⟨beta, hbeta, hcoord⟩ := halpha_mem
    have hbeta_eq : beta = alpha := coordinates.injective hcoord
    subst beta
    have hfix := (LinearMap.mem_ker).mp hbeta
    change F alpha - alpha = 0 at hfix
    simpa using sub_eq_zero.mp hfix
  have hm_dvd_n : m ∣ n := by
    have hdvd : orderOf frob ∣ n :=
      (orderOf_dvd_iff_pow_eq_one).2 hF_eq_one
    rw [FiniteField.orderOf_frobeniusAlgHom,
      GaloisField.finrank 2 (Nat.ne_of_gt hm)] at hdvd
    exact hdvd
  have hfinrank : Module.finrank F2 V = m :=
    coordinates.finrank_eq.symm.trans
      (GaloisField.finrank 2 (Nat.ne_of_gt hm))
  simpa [hfinrank] using hm_dvd_n

set_option backward.isDefEq.respectTransparency false in
/-- A faithful irreducible binary cyclic action of order 2^n - 1 has
cardinality 2^n. This is Higman's finite-field inference m = n. -/
public theorem lemma5_irreducible_card_of_order
    {V : Type u} [AddCommGroup V] [Module F2 V] [Finite V]
    (T : V ≃ₗ[F2] V)
    (hV_irreducible :
      ∀ A : Submodule F2 V,
        (∀ x : V, x ∈ A → T x ∈ A) → A = ⊥ ∨ A = ⊤)
    (n : ℕ) (hn : 2 ≤ n) (hT_order : orderOf T = 2 ^ n - 1) :
    Nat.card V = 2 ^ n := by
  letI : Nontrivial V := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have hT_one : T = 1 := by
      apply LinearEquiv.ext
      intro x
      exact Subsingleton.elim _ _
    have horder_one : orderOf T = 1 := by rw [hT_one]; simp
    have hpow_le : 4 ≤ 2 ^ n := by
      simpa using (Nat.pow_le_pow_right (n := 2) (by omega) hn)
    omega
  obtain ⟨m, hm, lambda, coordinates, hV_card, hlambda, hT⟩ :=
    lemma5_irreducible_field_coordinates T hV_irreducible
  let K := BinaryGaloisField m
  let lambdaUnit : Kˣ := Units.mk0 lambda hlambda
  have hT_pow : ∀ k : ℕ, ∀ alpha : K,
      (T ^ k) (coordinates alpha) =
        coordinates ((lambdaUnit ^ k : Kˣ) * alpha) := by
    intro k
    induction k with
    | zero =>
        intro alpha
        simp
    | succ k ih =>
        intro alpha
        simpa only [pow_succ, LinearEquiv.mul_apply, Units.val_mul] using
          (calc
            (T ^ k) (T (coordinates alpha)) =
                (T ^ k) (coordinates (lambda * alpha)) := by rw [hT]
            _ = coordinates ((lambdaUnit ^ k : Kˣ) * (lambda * alpha)) :=
              ih (lambda * alpha)
            _ = coordinates
                (((lambdaUnit ^ k * lambdaUnit : Kˣ) : K) * alpha) := by
              congr 1
              simp only [lambdaUnit, Units.val_mul, Units.val_mk0]
              rw [mul_assoc])
  have hT_dvd_lambda : orderOf T ∣ orderOf lambdaUnit := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply LinearEquiv.ext
    intro x
    obtain ⟨alpha, rfl⟩ := coordinates.surjective x
    rw [hT_pow]
    have hpow := pow_orderOf_eq_one lambdaUnit
    rw [hpow]
    simp
  have hlambda_dvd_T : orderOf lambdaUnit ∣ orderOf T := by
    apply (orderOf_dvd_iff_pow_eq_one).2
    apply Units.ext
    have hpow := LinearEquiv.congr_fun (pow_orderOf_eq_one T)
      (coordinates (1 : K))
    rw [hT_pow] at hpow
    simpa using coordinates.injective hpow
  have hlambda_order : orderOf lambdaUnit = 2 ^ n - 1 := by
    rw [Nat.dvd_antisymm hlambda_dvd_T hT_dvd_lambda, hT_order]
  have hlambda_pow : lambda ^ (2 ^ n) = lambda := by
    have hpow := congrArg (fun z : Kˣ => (z : K))
      (pow_orderOf_eq_one lambdaUnit)
    rw [hlambda_order] at hpow
    change lambda ^ (2 ^ n - 1) = 1 at hpow
    have htwo_pow_pos : 0 < 2 ^ n := pow_pos (by omega) n
    calc
      lambda ^ (2 ^ n) = lambda ^ (2 ^ n - 1 + 1) := by
        congr 1
        omega
      _ = lambda ^ (2 ^ n - 1) * lambda := by rw [pow_succ]
      _ = lambda := by rw [hpow, one_mul]
  have hn_dvd_m : n ∣ m := by
    have hdvd : orderOf lambdaUnit ∣ Nat.card Kˣ :=
      orderOf_dvd_natCard lambdaUnit
    rw [hlambda_order, Nat.card_units, show Nat.card K = 2 ^ m by
      exact GaloisField.card 2 m (Nat.ne_of_gt hm)] at hdvd
    have hmod : 2 ^ (m % n) - 1 = 0 := by
      rw [← Nat.pow_sub_one_mod_pow_sub_one 2 n m]
      exact Nat.mod_eq_zero_of_dvd hdvd
    have hsmall_pow_pos : 0 < 2 ^ (m % n) := pow_pos (by omega) _
    have hpow_one : 2 ^ (m % n) = 1 := by omega
    have hm_mod : m % n = 0 :=
      (Nat.pow_eq_one.mp hpow_one).resolve_left (by omega)
    exact Nat.dvd_of_mod_eq_zero hm_mod
  let frob : K →ₐ[F2] K := FiniteField.frobeniusAlgHom F2 K
  let F : K →ₐ[F2] K := frob ^ n
  have hF_lambda : F lambda = lambda := by
    dsimp [F]
    rw [congrFun (AlgHom.coe_pow frob n) lambda]
    rw [show (frob : K → K) = fun x => x ^ 2 by
      exact FiniteField.coe_frobeniusAlgHom F2 K]
    rw [pow_iterate]
    exact hlambda_pow
  let A : Submodule F2 K := (F.toLinearMap - LinearMap.id).ker
  have hA_one : (1 : K) ∈ A := by
    rw [LinearMap.mem_ker]
    simp [F]
  have hA_lambda_mul : ∀ x : K, x ∈ A → lambda * x ∈ A := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    change F x - x = 0 at hx
    change F (lambda * x) - lambda * x = 0
    rw [map_mul, hF_lambda, sub_eq_zero]
    exact congrArg (lambda * ·) (sub_eq_zero.mp hx)
  let AV : Submodule F2 V := Submodule.map coordinates.toLinearMap A
  have hAV_invariant : ∀ x : V, x ∈ AV → T x ∈ AV := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨alpha, halpha, rfl⟩ := hx
    refine ⟨lambda * alpha, hA_lambda_mul alpha halpha, ?_⟩
    exact (hT alpha).symm
  have hAV_ne_bot : AV ≠ ⊥ := by
    intro hbot
    have hone_mem : coordinates (1 : K) ∈ AV := by
      rw [Submodule.mem_map]
      exact ⟨1, hA_one, rfl⟩
    rw [hbot, Submodule.mem_bot] at hone_mem
    exact one_ne_zero (coordinates.injective
      (hone_mem.trans coordinates.map_zero.symm))
  have hAV_top : AV = ⊤ :=
    (hV_irreducible AV hAV_invariant).resolve_left hAV_ne_bot
  have hF_eq_one : F = 1 := by
    apply DFunLike.ext _ _
    intro alpha
    have halpha_mem : coordinates alpha ∈ AV := by
      rw [hAV_top]
      trivial
    rw [Submodule.mem_map] at halpha_mem
    obtain ⟨beta, hbeta, hcoord⟩ := halpha_mem
    have hbeta_eq : beta = alpha := coordinates.injective hcoord
    subst beta
    have hfix := (LinearMap.mem_ker).mp hbeta
    change F alpha - alpha = 0 at hfix
    simpa using sub_eq_zero.mp hfix
  have hm_dvd_n : m ∣ n := by
    have hdvd : orderOf frob ∣ n :=
      (orderOf_dvd_iff_pow_eq_one).2 hF_eq_one
    rw [FiniteField.orderOf_frobeniusAlgHom,
      GaloisField.finrank 2 (Nat.ne_of_gt hm)] at hdvd
    exact hdvd
  have hmn : m = n := Nat.dvd_antisymm hm_dvd_n hn_dvd_m
  simpa [hmn] using hV_card

set_option backward.isDefEq.respectTransparency false in
private theorem lemma5_conjugate_eigenbasis
    {V : Type*} [AddCommGroup V] [Module F2 V] [Finite V]
    (T : V ≃ₗ[F2] V)
    (m : ℕ) (hm : 0 < m)
    (lambda : BinaryGaloisField m)
    (coordinates : BinaryGaloisField m ≃ₗ[F2] V)
    (hT :
      ∀ alpha : BinaryGaloisField m,
        T (coordinates alpha) = coordinates (lambda * alpha)) :
    ∃ u : Module.Basis (Fin m) (BinaryGaloisField m)
        (BinaryGaloisField m ⊗[F2] V),
      (∀ i : Fin m,
        (T.baseChange F2 (BinaryGaloisField m) V V) (u i) =
          lambda ^ (2 ^ (i : ℕ)) • u i) ∧
      ∀ alpha : BinaryGaloisField m,
        1 ⊗ₜ[F2] coordinates alpha =
          ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i := by
  classical
  let K := BinaryGaloisField m
  have hfinrank : Module.finrank F2 K = m :=
    GaloisField.finrank 2 hm.ne'
  have hVfinrank : Module.finrank F2 V = m :=
    coordinates.finrank_eq.symm.trans hfinrank
  let b : Module.Basis (Fin m) F2 K :=
    Module.finBasisOfFinrankEq F2 K hfinrank
  let d : Module.Basis (Fin m) F2 K := b.traceDual
  let sigma : K ≃ₐ[F2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic F2 K
  have hsigma (i : Fin m) (x : K) :
      (sigma ^ (i : ℕ)) x = x ^ (2 ^ (i : ℕ)) := by
    calc
      (sigma ^ (i : ℕ)) x = ((⇑sigma)^[i]) x :=
        congrFun (AlgEquiv.coe_pow sigma (i : ℕ)) x
      _ = x ^ (Fintype.card F2 ^ (i : ℕ)) :=
        congrFun
          (FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate
            F2 K (i : ℕ)) x
      _ = x ^ (2 ^ (i : ℕ)) := by simp [ZMod.card]
  let B : Matrix (Fin m) (Fin m) K :=
    fun i j => (sigma ^ (i : ℕ)) (b j)
  let D : Matrix (Fin m) (Fin m) K :=
    fun i j => (sigma ^ (i : ℕ)) (d j)
  have hDB : D.transpose * B = 1 := by
    ext i j
    rw [Matrix.mul_apply, Matrix.one_apply]
    simp only [D, B, Matrix.transpose_apply]
    calc
      (∑ x : Fin m,
          (sigma ^ (x : ℕ)) (d i) *
            (sigma ^ (x : ℕ)) (b j)) =
          ∑ x : Fin m, (d i * b j) ^ (2 ^ (x : ℕ)) := by
            apply Finset.sum_congr rfl
            intro x _hx
            rw [← hsigma x, map_mul]
      _ = algebraMap F2 K (Algebra.trace F2 K (d i * b j)) := by
        rw [FiniteField.algebraMap_trace_eq_sum_pow F2 K, hfinrank]
        simp only [Nat.card_zmod]
        exact Fin.sum_univ_eq_sum_range
          (fun r => (d i * b j) ^ (2 ^ r)) m
      _ = if i = j then 1 else 0 := by
        rw [b.trace_traceDual_mul]
        simp [eq_comm]
  have hBD : B * D.transpose = 1 :=
    (mul_eq_one_comm).mpr hDB
  let eval (i : Fin m) :
      (K ⊗[F2] V) →ₗ[K] K :=
    (Algebra.TensorProduct.productLeftAlgHom
      (AlgHom.id K K) (sigma ^ (i : ℕ)).toAlgHom).toLinearMap.comp
        (coordinates.symm.toLinearMap.baseChange K)
  have heval_tmul (i : Fin m) (a : K) (v : V) :
      eval i (a ⊗ₜ[F2] v) =
        a * (sigma ^ (i : ℕ)) (coordinates.symm v) := by
    change (Algebra.TensorProduct.productLeftAlgHom
        (AlgHom.id K K) (sigma ^ (i : ℕ)).toAlgHom)
        ((coordinates.symm.toLinearMap.baseChange K) (a ⊗ₜ[F2] v)) =
      a * (sigma ^ (i : ℕ)) (coordinates.symm v)
    rw [LinearMap.baseChange_tmul]
    rfl
  let uv : Fin m → K ⊗[F2] V := fun i =>
    ∑ j : Fin m, (sigma ^ (i : ℕ)) (b j) •
      (1 ⊗ₜ[F2] coordinates (d j))
  have heval_uv (k i : Fin m) :
      eval k (uv i) = if i = k then 1 else 0 := by
    rw [show eval k (uv i) =
        ∑ j : Fin m, (sigma ^ (i : ℕ)) (b j) *
          (sigma ^ (k : ℕ)) (d j) by
      simp [uv, heval_tmul]]
    have h := congrArg (fun M : Matrix (Fin m) (Fin m) K => M i k) hBD
    simpa [Matrix.mul_apply, Matrix.one_apply, B, D] using h
  have huv_li : LinearIndependent K uv := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    have hi := congrArg (eval i) hg
    simp only [map_sum, map_smul, map_zero, heval_uv] at hi
    simpa using hi
  have htensor_finrank :
      Module.finrank K (K ⊗[F2] V) = m :=
    (Module.finrank_baseChange
      (R := K) (S := F2) (M' := V)).trans hVfinrank
  letI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let u : Module.Basis (Fin m) K (K ⊗[F2] V) :=
    basisOfLinearIndependentOfCardEqFinrank huv_li
      (by simp [htensor_finrank])
  have hu_apply (i : Fin m) : u i = uv i := by
    simp [u]
  have hreval (x : K ⊗[F2] V) (k : Fin m) :
      u.repr x k = eval k x := by
    have h := congrArg (eval k) (u.sum_repr x)
    simp only [map_sum, map_smul] at h
    simpa [hu_apply, heval_uv] using h
  have heval_T (k : Fin m) (x : K ⊗[F2] V) :
      eval k ((T.baseChange F2 K V V) x) =
        (sigma ^ (k : ℕ)) lambda * eval k x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        have hv :
            T v = coordinates (lambda * coordinates.symm v) := by
          simpa using hT (coordinates.symm v)
        rw [LinearEquiv.baseChange_tmul, heval_tmul, hv,
          coordinates.symm_apply_apply, map_mul, heval_tmul]
        ring
    | add x y hx hy =>
        simp only [map_add]
        rw [hx, hy, mul_add]
  have hu_eigen :
      ∀ i : Fin m,
        (T.baseChange F2 K V V) (u i) =
          lambda ^ (2 ^ (i : ℕ)) • u i := by
    intro i
    apply u.repr.injective
    ext k
    rw [hreval, hreval, heval_T, map_smul, hu_apply, heval_uv]
    by_cases hik : i = k
    · subst k
      rw [hsigma]
      simp
    · simp [hik]
  have hu_expansion :
      ∀ alpha : K,
        1 ⊗ₜ[F2] coordinates alpha =
          ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i := by
    intro alpha
    apply u.repr.injective
    ext k
    rw [hreval, hreval]
    simp only [heval_tmul, coordinates.symm_apply_apply, one_mul,
      map_sum, map_smul, hu_apply, heval_uv]
    rw [hsigma]
    simp
  exact ⟨u, hu_eigen, hu_expansion⟩
set_option backward.isDefEq.respectTransparency false in
/-- An irreducible binary linear automorphism admits field coordinates and a
conjugate eigenbasis after scalar extension to its coordinate field. -/
public theorem lemma5_irreducible_conjugate_eigenbasis
    {V : Type u} [AddCommGroup V] [Module F2 V] [Nontrivial V]
    [Finite V] [Module.Finite F2 V]
    (T : V ≃ₗ[F2] V)
    (hT_irreducible :
      ∀ W : Submodule F2 V,
        (∀ v : V, v ∈ W → T v ∈ W) →
        W = ⊥ ∨ W = ⊤) :
    ∃ (m : ℕ) (_hm : 0 < m)
        (lambda : BinaryGaloisField m)
        (coordinates : BinaryGaloisField m ≃ₗ[F2] V)
        (u : Module.Basis (Fin m) (BinaryGaloisField m)
          (BinaryGaloisField m ⊗[F2] V)),
      Nat.card V = 2 ^ m ∧
      lambda ≠ 0 ∧
      (∀ alpha : BinaryGaloisField m,
        T (coordinates alpha) = coordinates (lambda * alpha)) ∧
      (∀ i : Fin m,
        (T.baseChange F2 (BinaryGaloisField m) V V) (u i) =
          lambda ^ (2 ^ (i : ℕ)) • u i) ∧
      ∀ alpha : BinaryGaloisField m,
        1 ⊗ₜ[F2] coordinates alpha =
          ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i := by
  obtain ⟨m, hm, lambda, coordinates, hV_card, hlambda,
      hcoordinates⟩ :=
    lemma5_irreducible_field_coordinates T hT_irreducible
  obtain ⟨u, hu_eigen, hu_expansion⟩ :=
    lemma5_conjugate_eigenbasis T m hm lambda coordinates hcoordinates
  exact ⟨m, hm, lambda, coordinates, u, hV_card, hlambda,
    hcoordinates, hu_eigen, hu_expansion⟩
set_option backward.isDefEq.respectTransparency false in
/-- Interfaces for the bracket returned by `lemma5_square_map_normal_form`.
The representative formula identifies it with the canonical lower-central
bracket, while the pure-tensor formula transports equivariance and alternation
to the scalar extension. -/
public theorem lemma5_lowerCentralBracket_interfaces
    {H : Type u} [Group H]
    (xi : MulAut H) (m : ℕ)
    (xiK : (BinaryGaloisField m ⊗[F2]
      Additive (LowerCentralFactor H 0)) ≃ₗ[BinaryGaloisField m]
        (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)))
    (bracket : Additive (LowerCentralFactor H 0) →ₗ[F2]
      Additive (LowerCentralFactor H 0) →ₗ[F2]
        Additive (LowerCentralFactor H 1))
    (bracketK : (BinaryGaloisField m ⊗[F2]
      Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
        (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
            (BinaryGaloisField m ⊗[F2]
              Additive (LowerCentralFactor H 1)))
    (hxiK_tmul :
      ∀ v : Additive (LowerCentralFactor H 0),
        xiK (1 ⊗ₜ[F2] v) =
          1 ⊗ₜ[F2] lowerCentralFactorLinearAut xi 0 v)
    (hbracketK_tmul :
      ∀ v w : Additive (LowerCentralFactor H 0),
        bracketK (1 ⊗ₜ[F2] v) (1 ⊗ₜ[F2] w) =
          1 ⊗ₜ[F2] bracket v w)
    (hbracket_mk :
      ∀ x y : higmanLowerCentralSeries H 0,
        ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1,
          bracket
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨⁅(x : H), (y : H)⁆, hcomm⟩)) :
    (∀ v w : Additive (LowerCentralFactor H 0),
      bracket (lowerCentralFactorLinearAut xi 0 v)
          (lowerCentralFactorLinearAut xi 0 w) =
        lowerCentralFactorLinearAut xi 1 (bracket v w)) ∧
    (∀ x y : BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 0),
      bracketK (xiK x) (xiK y) =
        (lowerCentralFactorLinearAut xi 1).baseChange F2
          (BinaryGaloisField m)
          (Additive (LowerCentralFactor H 1))
          (Additive (LowerCentralFactor H 1)) (bracketK x y)) ∧
    (∀ v : Additive (LowerCentralFactor H 0), bracket v v = 0) ∧
    (∀ x : BinaryGaloisField m ⊗[F2]
      Additive (LowerCentralFactor H 0), bracketK x x = 0) ∧
    Submodule.span F2
      (Set.range fun p : Additive (LowerCentralFactor H 0) ×
        Additive (LowerCentralFactor H 0) => bracket p.1 p.2) = ⊤ := by
  classical
  obtain ⟨canonical, hcanonical_mk, hcanonical_equivariant,
      hcanonical_self, hcanonical_span⟩ :=
    lemma4_exists_lowerCentralBracket (H := H)
  have hbracket_eq : bracket = canonical := by
    apply LinearMap.ext
    intro v
    apply LinearMap.ext
    intro w
    obtain ⟨x, hx⟩ :=
      QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) v.toMul
    obtain ⟨y, hy⟩ :=
      QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) w.toMul
    have hv : v = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
      apply Additive.toMul.injective
      exact hx.symm
    have hw : w = Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y) := by
      apply Additive.toMul.injective
      exact hy.symm
    rw [hv, hw]
    have hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1 := by
      change ⁅(x : H), (y : H)⁆ ∈
        (⊤ : Subgroup H).lowerCentralSeries (0 + 1)
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.subset_closure
        ⟨(x : H), x.property, (y : H), trivial, rfl⟩
    exact (hbracket_mk x y hcomm).trans
      (hcanonical_mk x y hcomm).symm
  have hbracket_equivariant :
      ∀ v w : Additive (LowerCentralFactor H 0),
        bracket (lowerCentralFactorLinearAut xi 0 v)
            (lowerCentralFactorLinearAut xi 0 w) =
          lowerCentralFactorLinearAut xi 1 (bracket v w) := by
    simpa only [hbracket_eq] using hcanonical_equivariant xi
  have hbracket_self :
      ∀ v : Additive (LowerCentralFactor H 0), bracket v v = 0 := by
    simpa only [hbracket_eq] using hcanonical_self
  have hbracket_span :
      Submodule.span F2
        (Set.range fun p : Additive (LowerCentralFactor H 0) ×
          Additive (LowerCentralFactor H 0) => bracket p.1 p.2) = ⊤ := by
    simpa only [hbracket_eq] using hcanonical_span
  let SK := (lowerCentralFactorLinearAut xi 1).baseChange F2
    (BinaryGaloisField m)
    (Additive (LowerCentralFactor H 1))
    (Additive (LowerCentralFactor H 1))
  have hbracketK_equivariant
      (x y : BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 0)) :
      bracketK (xiK x) (xiK y) = SK (bracketK x y) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b w =>
            have ha : a ⊗ₜ[F2] v = a • (1 ⊗ₜ[F2] v) := by
              rw [TensorProduct.smul_tmul']
              simp
            have hb : b ⊗ₜ[F2] w = b • (1 ⊗ₜ[F2] w) := by
              rw [TensorProduct.smul_tmul']
              simp
            rw [ha, hb]
            simp only [map_smul, LinearMap.smul_apply, smul_smul]
            rw [hxiK_tmul, hxiK_tmul,
              hbracketK_tmul, hbracketK_tmul,
              hbracket_equivariant,
              LinearEquiv.baseChange_tmul]
        | add y z hy hz =>
            simp only [map_add]
            rw [hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply]
        rw [hx, hy]
  have hadd_self_L2 (z : Additive (LowerCentralFactor H 1)) : z + z = 0 := by
    rw [← two_smul F2 z]
    simp only [CharTwo.two_eq_zero, zero_smul]
  have hbracket_symm
      (v w : Additive (LowerCentralFactor H 0)) : bracket v w = bracket w v := by
    have hsum : bracket v w + bracket w v = 0 := by
      have h := hbracket_self (v + w)
      simp only [map_add, LinearMap.add_apply] at h
      rw [hbracket_self v, hbracket_self w] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      bracket v w = bracket v w + (bracket w v + bracket w v) := by
        rw [hadd_self_L2, add_zero]
      _ = (bracket v w + bracket w v) + bracket w v := by ac_rfl
      _ = bracket w v := by rw [hsum, zero_add]
  have hadd_self_L2K
      (z : BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 1)) : z + z = 0 := by
    rw [← two_smul (BinaryGaloisField m) z]
    simp only [CharTwo.two_eq_zero, zero_smul]
  have hbracketK_symm
      (x y : BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 0)) :
      bracketK x y = bracketK y x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b w =>
            have ha : a ⊗ₜ[F2] v = a • (1 ⊗ₜ[F2] v) := by
              rw [TensorProduct.smul_tmul']
              simp
            have hb : b ⊗ₜ[F2] w = b • (1 ⊗ₜ[F2] w) := by
              rw [TensorProduct.smul_tmul']
              simp
            rw [ha, hb, map_smul, LinearMap.map_smul₂,
              map_smul, LinearMap.map_smul₂,
              hbracketK_tmul, hbracketK_tmul, hbracket_symm]
            simp [smul_smul, mul_comm]
        | add y z hy hz =>
            simp only [map_add, LinearMap.add_apply]
            rw [hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply]
        rw [hx, hy]
  have hbracketK_self
      (x : BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 0)) : bracketK x x = 0 := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        have ha : a ⊗ₜ[F2] v = a • (1 ⊗ₜ[F2] v) := by
          rw [TensorProduct.smul_tmul']
          simp
        rw [ha, map_smul, LinearMap.map_smul₂,
          hbracketK_tmul, hbracket_self]
        simp
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply]
        rw [hx, hy, hbracketK_symm y x]
        simpa only [zero_add, add_zero] using
          hadd_self_L2K (bracketK x y)
  exact ⟨hbracket_equivariant, hbracketK_equivariant,
    hbracket_self, hbracketK_self, hbracket_span⟩
private theorem lemma5_lowerCentralFactorKernel_zero_le
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1) :
    lowerCentralFactorKernel H 0 ≤
      (higmanLowerCentralSeries H 1).subgroupOf (higmanLowerCentralSeries H 0) := by
  rw [lowerCentralFactorKernel]
  apply sup_le
  · rw [squaresSubgroup, Subgroup.closure_le]
    rintro _ ⟨x, rfl⟩
    change (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1
    exact hH_square (Subgroup.subset_closure ⟨(x : H), rfl⟩)
  · exact le_rfl

private def lemma5_squareLift
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (x : higmanLowerCentralSeries H 0) :
    higmanLowerCentralSeries H 1 :=
  ⟨(x : H) ^ 2, by
    exact hH_square (Subgroup.subset_closure ⟨(x : H), rfl⟩)⟩

private def lemma5_squareCommutatorLift
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (c : higmanLowerCentralSeries H 1) :
    higmanLowerCentralSeries H 1 :=
  ⟨⁅(x : H)⁻¹, (c : H)⁆, by
    apply (⊤ : Subgroup H).lowerCentralSeries_antitone (by omega : 1 ≤ 2)
    have hcx : ⁅(c : H), (x : H)⁻¹⁆ ∈ higmanLowerCentralSeries H 2 := by
      change ⁅(c : H), (x : H)⁻¹⁆ ∈
        (⊤ : Subgroup H).lowerCentralSeries (1 + 1)
      rw [Subgroup.lowerCentralSeries_succ]
      exact Subgroup.subset_closure
        ⟨(c : H), c.property, (x : H)⁻¹, trivial, rfl⟩
    have hinv := (higmanLowerCentralSeries H 2).inv_mem hcx
    simpa only [commutatorElement_inv] using hinv⟩

private theorem lemma5_squareCommutatorLift_mem_kernel
    {H : Type u} [Group H]
    (x : higmanLowerCentralSeries H 0) (c : higmanLowerCentralSeries H 1) :
    lemma5_squareCommutatorLift x c ∈ lowerCentralFactorKernel H 1 := by
  apply (show
    (higmanLowerCentralSeries H 2).subgroupOf (higmanLowerCentralSeries H 1) ≤
      lowerCentralFactorKernel H 1 by
    rw [lowerCentralFactorKernel]
    exact le_sup_right)
  change ⁅(x : H)⁻¹, (c : H)⁆ ∈ higmanLowerCentralSeries H 2
  have hcx : ⁅(c : H), (x : H)⁻¹⁆ ∈ higmanLowerCentralSeries H 2 := by
    change ⁅(c : H), (x : H)⁻¹⁆ ∈
      (⊤ : Subgroup H).lowerCentralSeries (1 + 1)
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.subset_closure
      ⟨(c : H), c.property, (x : H)⁻¹, trivial, rfl⟩
  have hinv := (higmanLowerCentralSeries H 2).inv_mem hcx
  simpa only [commutatorElement_inv] using hinv

private theorem lemma5_squareLift_eq_of_rel
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (x y : higmanLowerCentralSeries H 0)
    (hxy : x⁻¹ * y ∈ lowerCentralFactorKernel H 0) :
    QuotientGroup.mk' (lowerCentralFactorKernel H 1)
        (lemma5_squareLift hH_square x) =
      QuotientGroup.mk' (lowerCentralFactorKernel H 1)
        (lemma5_squareLift hH_square y) := by
  let k : higmanLowerCentralSeries H 0 := x⁻¹ * y
  have hk : k ∈
      (higmanLowerCentralSeries H 1).subgroupOf (higmanLowerCentralSeries H 0) :=
    lemma5_lowerCentralFactorKernel_zero_le hH_square hxy
  let c : higmanLowerCentralSeries H 1 := ⟨(k : H), hk⟩
  have hy : (y : H) = (x : H) * (c : H) := by
    change (y : H) = (x : H) * ((x : H)⁻¹ * (y : H))
    group
  have hfactor :
      lemma5_squareLift hH_square y =
        lemma5_squareLift hH_square x *
          lemma5_squareCommutatorLift x c * c ^ 2 := by
    apply Subtype.ext
    change (y : H) ^ 2 =
      (x : H) ^ 2 * ⁅(x : H)⁻¹, (c : H)⁆ * (c : H) ^ 2
    rw [hy]
    simp only [pow_two, commutatorElement_def]
    group
  let q := QuotientGroup.mk' (lowerCentralFactorKernel H 1)
  have hcomm : q (lemma5_squareCommutatorLift x c) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    exact lemma5_squareCommutatorLift_mem_kernel x c
  have hcsq : q (c ^ 2) = 1 := by
    apply (QuotientGroup.eq_one_iff _).2
    apply (show squaresSubgroup (higmanLowerCentralSeries H 1) ≤
        lowerCentralFactorKernel H 1 by
      rw [lowerCentralFactorKernel]
      exact le_sup_left)
    exact Subgroup.subset_closure ⟨c, rfl⟩
  symm
  calc
    q (lemma5_squareLift hH_square y) =
        q (lemma5_squareLift hH_square x *
          lemma5_squareCommutatorLift x c * c ^ 2) := congrArg q hfactor
    _ = q (lemma5_squareLift hH_square x) *
          q (lemma5_squareCommutatorLift x c) * q (c ^ 2) := by
        simp only [map_mul]
    _ = q (lemma5_squareLift hH_square x) := by
        rw [hcomm, hcsq]
        simp

private def lemma5_lowerCentralSquareMap
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1) :
    Additive (LowerCentralFactor H 0) →
      Additive (LowerCentralFactor H 1) :=
  fun v =>
    Additive.ofMul <|
      Quotient.liftOn' v.toMul
        (fun x => QuotientGroup.mk' (lowerCentralFactorKernel H 1)
          (lemma5_squareLift hH_square x))
        (fun x y hxy =>
          lemma5_squareLift_eq_of_rel hH_square x y
            (QuotientGroup.leftRel_apply.mp hxy))

private theorem lemma5_lowerCentralSquareMap_mk
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (x : higmanLowerCentralSeries H 0) :
    lemma5_lowerCentralSquareMap hH_square
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
          (lemma5_squareLift hH_square x)) :=
  rfl

private theorem lemma5_lowerCentralSquareMap_mk'
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (x : higmanLowerCentralSeries H 0)
    (hsquare : (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1) :
    lemma5_lowerCentralSquareMap hH_square
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
      Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
          (⟨(x : H) ^ 2, hsquare⟩ : higmanLowerCentralSeries H 1)) := by
  rw [lemma5_lowerCentralSquareMap_mk]
  apply Additive.toMul.injective
  exact congrArg (QuotientGroup.mk' (lowerCentralFactorKernel H 1))
    (Subtype.ext (by rfl))

private theorem lemma5_lowerCentralSquareMap_equivariant
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (theta : MulAut H)
    (v : Additive (LowerCentralFactor H 0)) :
    lemma5_lowerCentralSquareMap hH_square
        (lowerCentralFactorLinearAut theta 0 v) =
      lowerCentralFactorLinearAut theta 1
        (lemma5_lowerCentralSquareMap hH_square v) := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) v.toMul
  have hv : v = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  rw [hv, lowerCentralFactorLinearAut_ofMul_mk,
    lemma5_lowerCentralSquareMap_mk, lemma5_lowerCentralSquareMap_mk,
    lowerCentralFactorLinearAut_ofMul_mk]
  apply Additive.toMul.injective
  exact congrArg (QuotientGroup.mk' (lowerCentralFactorKernel H 1))
    (Subtype.ext (by
      change (theta (x : H)) ^ 2 = theta ((x : H) ^ 2)
      exact (map_pow theta (x : H) 2).symm))

private def lemma5_commutatorLift
    {H : Type u} [Group H]
    (x y : higmanLowerCentralSeries H 0) :
    higmanLowerCentralSeries H 1 :=
  ⟨⁅(x : H), (y : H)⁆, by
    change ⁅(x : H), (y : H)⁆ ∈
      (⊤ : Subgroup H).lowerCentralSeries (0 + 1)
    rw [Subgroup.lowerCentralSeries_succ]
    exact Subgroup.subset_closure
      ⟨(x : H), x.property, (y : H), trivial, rfl⟩⟩

private theorem lemma5_lowerCentralSquareMap_add_mk
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (bracket : Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1))
    (hbracket :
      ∀ x y : higmanLowerCentralSeries H 0,
        ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1,
          bracket
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨⁅(x : H), (y : H)⁆, hcomm⟩))
    (x y : higmanLowerCentralSeries H 0) :
    lemma5_lowerCentralSquareMap hH_square
        (Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) (x * y))) =
      lemma5_lowerCentralSquareMap hH_square
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) +
        lemma5_lowerCentralSquareMap hH_square
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) +
        bracket
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) := by
  have hxinv :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x⁻¹) =
        Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
    apply Additive.toMul.injective
    let qx := QuotientGroup.mk' (lowerCentralFactorKernel H 0) x
    change qx⁻¹ = qx
    apply mul_left_cancel (a := qx)
    simpa [pow_two] using
      (lowerCentralFactor_sq_eq_one 0 qx).symm
  have hcorr :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
            (lemma5_commutatorLift x⁻¹ y)) =
        bracket
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
          (Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) := by
    calc
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
            (lemma5_commutatorLift x⁻¹ y)) =
          bracket
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x⁻¹))
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) := by
        simpa [lemma5_commutatorLift] using
          (hbracket x⁻¹ y (lemma5_commutatorLift x⁻¹ y).property).symm
      _ = bracket
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
            (Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) := by
        rw [hxinv]
  have hfactor :
      lemma5_squareLift hH_square (x * y) =
        lemma5_squareLift hH_square x *
          lemma5_commutatorLift x⁻¹ y *
          lemma5_squareLift hH_square y := by
    apply Subtype.ext
    change ((x : H) * (y : H)) ^ 2 =
      (x : H) ^ 2 * ⁅(x : H)⁻¹, (y : H)⁆ * (y : H) ^ 2
    simp only [pow_two, commutatorElement_def]
    group
  rw [lemma5_lowerCentralSquareMap_mk, lemma5_lowerCentralSquareMap_mk,
    lemma5_lowerCentralSquareMap_mk]
  have hqfactor :
      Additive.ofMul
          (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
            (lemma5_squareLift hH_square (x * y))) =
        Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
              (lemma5_squareLift hH_square x)) +
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
              (lemma5_commutatorLift x⁻¹ y)) +
          Additive.ofMul
            (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
              (lemma5_squareLift hH_square y)) := by
    apply Additive.toMul.injective
    rw [hfactor]
    simp only [map_mul, toMul_ofMul, toMul_add]
  rw [hqfactor, hcorr]
  ac_rfl

private theorem lemma5_lowerCentralSquareMap_add
    {H : Type u} [Group H]
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (bracket : Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
      Additive (LowerCentralFactor H 0) →ₗ[ZMod 2]
        Additive (LowerCentralFactor H 1))
    (hbracket :
      ∀ x y : higmanLowerCentralSeries H 0,
        ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1,
          bracket
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨⁅(x : H), (y : H)⁆, hcomm⟩))
    (v w : Additive (LowerCentralFactor H 0)) :
    lemma5_lowerCentralSquareMap hH_square (v + w) =
      lemma5_lowerCentralSquareMap hH_square v +
        lemma5_lowerCentralSquareMap hH_square w + bracket v w := by
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) v.toMul
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (lowerCentralFactorKernel H 0) w.toMul
  have hv : v = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x) := by
    apply Additive.toMul.injective
    exact hx.symm
  have hw : w = Additive.ofMul
      (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y) := by
    apply Additive.toMul.injective
    exact hy.symm
  rw [hv, hw]
  change lemma5_lowerCentralSquareMap hH_square
      (Additive.ofMul
        (QuotientGroup.mk' (lowerCentralFactorKernel H 0) (x * y))) = _
  exact lemma5_lowerCentralSquareMap_add_mk hH_square bracket hbracket x y

private theorem lemma5_square_map_normal_form_field_core
    {H : Type u} [Group H] [Finite H]
    (xi : MulAut H)
    (hL1_irreducible :
      ∀ W : Submodule F2 (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (n : ℕ) (hn : 2 ≤ n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n) :
    ∃ (m : ℕ) (_hm : 0 < m)
        (lambda : BinaryGaloisField m)
        (coordinates : BinaryGaloisField m ≃ₗ[F2]
          Additive (LowerCentralFactor H 0))
        (u : Module.Basis (Fin m) (BinaryGaloisField m)
          (BinaryGaloisField m ⊗[F2]
            Additive (LowerCentralFactor H 0)))
        (xiK : (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)) ≃ₗ[BinaryGaloisField m]
            (BinaryGaloisField m ⊗[F2]
              Additive (LowerCentralFactor H 0))),
      Nat.card (LowerCentralFactor H 0) = 2 ^ m ∧
      lambda ≠ 0 ∧
      (∀ v : Additive (LowerCentralFactor H 0),
        xiK (1 ⊗ₜ[F2] v) =
          1 ⊗ₜ[F2] lowerCentralFactorLinearAut xi 0 v) ∧
      (∀ i : Fin m,
        xiK (u i) = lambda ^ (2 ^ (i : ℕ)) • u i) ∧
      (∀ alpha : BinaryGaloisField m,
        lowerCentralFactorLinearAut xi 0 (coordinates alpha) =
          coordinates (lambda * alpha)) ∧
      ∀ alpha : BinaryGaloisField m,
        1 ⊗ₜ[F2] coordinates alpha =
          ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i := by
  classical
  have hL2_card_gt :
      1 < Nat.card (Additive (LowerCentralFactor H 1)) := by
    rw [Nat.card_congr Additive.toMul, hL2_card]
    exact one_lt_pow₀ (by norm_num : 1 < (2 : ℕ)) (by omega)
  letI : Nontrivial (Additive (LowerCentralFactor H 1)) :=
    Finite.one_lt_card_iff_nontrivial.mp hL2_card_gt
  obtain ⟨bracket, _hbracket_mk, _hbracket_equivariant,
      _hbracket_self, hbracket_span⟩ :=
    lemma4_exists_lowerCentralBracket (H := H)
  have hL1_exists :
      ∃ v : Additive (LowerCentralFactor H 0), v ≠ 0 := by
    by_contra hzero
    push Not at hzero
    have hrange :
        Set.range (fun p :
          Additive (LowerCentralFactor H 0) ×
            Additive (LowerCentralFactor H 0) =>
          bracket p.1 p.2) = {0} := by
      ext z
      constructor
      · rintro ⟨⟨v, w⟩, rfl⟩
        simp [hzero v, hzero w]
      · intro hz
        have hz0 : z = 0 := by simpa using hz
        subst z
        exact ⟨(0, 0), by simp⟩
    have htop_bot :
        (⊤ : Submodule F2 (Additive (LowerCentralFactor H 1))) = ⊥ := by
      rw [← hbracket_span, hrange]
      simp
    exact top_ne_bot htop_bot
  obtain ⟨v, hv⟩ := hL1_exists
  letI : Nontrivial (Additive (LowerCentralFactor H 0)) :=
    ⟨⟨v, 0, hv⟩⟩
  let T : Additive (LowerCentralFactor H 0) ≃ₗ[F2]
      Additive (LowerCentralFactor H 0) :=
    lowerCentralFactorLinearAut xi 0
  obtain ⟨m, hm, lambda, coordinates, hL1_card, hlambda, hT⟩ :=
    lemma5_irreducible_field_coordinates T
      (by simpa [T] using hL1_irreducible)
  obtain ⟨u, hu_eigen, hu_expansion⟩ :=
    lemma5_conjugate_eigenbasis T m hm lambda coordinates hT
  let xiK :
      (BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 0)) ≃ₗ[BinaryGaloisField m]
          (BinaryGaloisField m ⊗[F2]
            Additive (LowerCentralFactor H 0)) :=
    T.baseChange F2 (BinaryGaloisField m)
      (Additive (LowerCentralFactor H 0))
      (Additive (LowerCentralFactor H 0))
  refine ⟨m, hm, lambda, coordinates, u, xiK,
    hL1_card, hlambda, ?_, ?_, ?_, hu_expansion⟩
  · intro w
    simp [xiK, T, LinearEquiv.baseChange_tmul]
  · simpa [xiK] using hu_eigen
  · simpa [T] using hT
public theorem lemma5_square_map_normal_form_quadratic_core
    {H : Type u} [Group H]
    (xi : MulAut H)
    (m : ℕ)
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1) :
    ∃ (bracket : Additive (LowerCentralFactor H 0) →ₗ[F2]
          Additive (LowerCentralFactor H 0) →ₗ[F2]
            Additive (LowerCentralFactor H 1))
        (bracketK : (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
            (BinaryGaloisField m ⊗[F2]
              Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
                (BinaryGaloisField m ⊗[F2]
                  Additive (LowerCentralFactor H 1)))
        (squareMap : Additive (LowerCentralFactor H 0) →
          Additive (LowerCentralFactor H 1)),
      (∀ v w : Additive (LowerCentralFactor H 0),
        bracketK (1 ⊗ₜ[F2] v) (1 ⊗ₜ[F2] w) =
          1 ⊗ₜ[F2] bracket v w) ∧      (∀ v w : Additive (LowerCentralFactor H 0),
        bracket (lowerCentralFactorLinearAut xi 0 v)
            (lowerCentralFactorLinearAut xi 0 w) =
          lowerCentralFactorLinearAut xi 1 (bracket v w)) ∧      (∀ v : Additive (LowerCentralFactor H 0), bracket v v = 0) ∧
      (∀ x y : higmanLowerCentralSeries H 0,
        ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1,
          bracket
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨⁅(x : H), (y : H)⁆, hcomm⟩)) ∧
      Submodule.span F2
        (Set.range fun p : Additive (LowerCentralFactor H 0) ×
          Additive (LowerCentralFactor H 0) => bracket p.1 p.2) = ⊤ ∧
      (∀ x : higmanLowerCentralSeries H 0,
        ∀ hsquare : (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1,
          squareMap
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨(x : H) ^ 2, hsquare⟩)) ∧
      (∀ v : Additive (LowerCentralFactor H 0),
        squareMap (lowerCentralFactorLinearAut xi 0 v) =
          lowerCentralFactorLinearAut xi 1 (squareMap v)) ∧
      ∀ v w : Additive (LowerCentralFactor H 0),
        squareMap (v + w) =
          squareMap v + squareMap w + bracket v w := by
  classical
  obtain ⟨bracket, hbracket_mk, hbracket_equivariant,
      hbracket_self, hbracket_span⟩ :=
    lemma4_exists_lowerCentralBracket (H := H)
  let bracketK :
      (BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
          (BinaryGaloisField m ⊗[F2]
            Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
              (BinaryGaloisField m ⊗[F2]
                Additive (LowerCentralFactor H 1)) :=
    (LinearMap.tensorProduct F2 (BinaryGaloisField m)
      (Additive (LowerCentralFactor H 0))
      (Additive (LowerCentralFactor H 1))).comp
        (bracket.baseChange (BinaryGaloisField m))
  let squareMap :
      Additive (LowerCentralFactor H 0) →
        Additive (LowerCentralFactor H 1) :=
    lemma5_lowerCentralSquareMap hH_square
  refine ⟨bracket, bracketK, squareMap, ?_, hbracket_equivariant xi,
    hbracket_self, hbracket_mk, hbracket_span, ?_, ?_, ?_⟩
  · intro v w
    simp [bracketK, LinearMap.tensorProduct,
      LinearMap.baseChange_tmul]
  · intro x hsquare
    exact lemma5_lowerCentralSquareMap_mk' hH_square x hsquare
  · intro v
    exact lemma5_lowerCentralSquareMap_equivariant hH_square xi v
  · intro v w
    exact lemma5_lowerCentralSquareMap_add
      hH_square bracket hbracket_mk v w
private theorem lemma5_no_scalarExtension_copy
    {H : Type u} [Group H] [Finite H]
    (hH_two : IsPGroup 2 H)
    (hH_nonabelian : ¬ IsMulCommutative H)
    (xi : MulAut H)
    (hxi_odd : Odd (orderOf xi))
    (hL1_irreducible :
      ∀ W : Submodule F2 (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n)
    (m : ℕ)
    (d : Additive (LowerCentralFactor H 0) →ₗ[F2]
      BinaryGaloisField m ⊗[F2] Additive (LowerCentralFactor H 1))
    (hd :
      ∀ v : Additive (LowerCentralFactor H 0),
        d (lowerCentralFactorLinearAut xi 0 v) =
          (lowerCentralFactorLinearAut xi 1).baseChange F2
            (BinaryGaloisField m)
            (Additive (LowerCentralFactor H 1))
            (Additive (LowerCentralFactor H 1)) (d v)) :
    d = 0 := by
  classical
  let K := BinaryGaloisField m
  let V1 := Additive (LowerCentralFactor H 0)
  let V2 := Additive (LowerCentralFactor H 1)
  let T : V1 ≃ₗ[F2] V1 := lowerCentralFactorLinearAut xi 0
  let S : V2 ≃ₗ[F2] V2 := lowerCentralFactorLinearAut xi 1
  let b := Module.finBasis F2 K
  let c := Module.finBasis F2 V2
  let eval (i : Fin (Module.finrank F2 K)) :
      K ⊗[F2] V2 →ₗ[F2] V2 :=
    (TensorProduct.lid F2 V2).toLinearMap.comp
      ((b.coord i).rTensor V2)
  have heval_tmul (i : Fin (Module.finrank F2 K)) (a : K) (v : V2) :
      eval i (a ⊗ₜ[F2] v) = (b.repr a i) • v := by
    simp [eval, b, Module.Basis.coord_apply]
  let tb := b.tensorProduct c
  have heval_coord (i : Fin (Module.finrank F2 K))
      (j : Fin (Module.finrank F2 V2)) (x : K ⊗[F2] V2) :
      c.repr (eval i x) j = tb.repr x (i, j) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        simp [heval_tmul, tb, b, c, mul_comm]
    | add x y hx hy =>
        simp [hx, hy]
  have heval_separates (x : K ⊗[F2] V2)
      (hx : ∀ i, eval i x = 0) : x = 0 := by
    apply tb.repr.injective
    ext ij
    rw [← heval_coord ij.1 ij.2]
    simp [hx ij.1]
  have heval_action (i : Fin (Module.finrank F2 K))
      (x : K ⊗[F2] V2) :
      eval i (S.baseChange F2 K V2 V2 x) = S (eval i x) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        simp [heval_tmul, S, LinearEquiv.baseChange_tmul]
    | add x y hx hy =>
        simp [hx, hy]
  by_contra hdne
  have hdne' : d ≠ 0 := hdne
  have hexists : ∃ v : V1, d v ≠ 0 := by
    by_contra hzero
    push Not at hzero
    apply hdne'
    ext v
    exact hzero v
  obtain ⟨v, hv⟩ := hexists
  have hnot_all_eval : ¬ ∀ i, eval i (d v) = 0 := by
    intro hall
    exact hv (heval_separates (d v) hall)
  push Not at hnot_all_eval
  obtain ⟨i, hi⟩ := hnot_all_eval
  let f : V1 →ₗ[F2] V2 := (eval i).comp d
  have hfne : f ≠ 0 := by
    intro hf
    have := LinearMap.congr_fun hf v
    exact hi (by simpa [f] using this)
  have hf_equivariant (w : V1) : f (T w) = S (f w) := by
    change eval i (d (lowerCentralFactorLinearAut xi 0 w)) =
      S (eval i (d w))
    rw [hd]
    exact heval_action i (d w)
  have hker_invariant :
      ∀ w : V1, w ∈ f.ker → T w ∈ f.ker := by
    intro w hw
    rw [LinearMap.mem_ker] at hw ⊢
    rw [hf_equivariant, hw, map_zero]
  have hker_ne_top : f.ker ≠ ⊤ := by
    intro htop
    apply hfne
    apply LinearMap.ext
    intro w
    exact LinearMap.mem_ker.mp (htop ▸ trivial)
  have hker_bot : f.ker = ⊥ := by
    rcases hL1_irreducible f.ker
        (fun w hw => hker_invariant w hw) with hbot | htop
    · exact hbot
    · exact (hker_ne_top htop).elim
  have hf_injective : Function.Injective f :=
    LinearMap.ker_eq_bot.mp hker_bot
  have hrange_invariant :
      ∀ y : V2, y ∈ f.range → S y ∈ f.range := by
    rintro _ ⟨w, rfl⟩
    exact ⟨T w, hf_equivariant w⟩
  have hfv : f v ≠ 0 := by
    simpa [f] using hi
  have hpow_range : ∀ k : ℕ, (S ^ k) (f v) ∈ f.range := by
    intro k
    induction k with
    | zero =>
        exact ⟨v, by simp⟩
    | succ k ih =>
        simpa [pow_succ'] using hrange_invariant _ ih
  have hrange_top : f.range = ⊤ := by
    rw [eq_top_iff]
    intro y _hy
    by_cases hy : y = 0
    · subst y
      exact f.range.zero_mem
    · obtain ⟨k, hk⟩ :=
        hL2_transitive (f v) hfv y hy
      rw [← hk]
      exact hpow_range k
  have hf_surjective : Function.Surjective f :=
    LinearMap.range_eq_top.mp hrange_top
  let e : V1 ≃ₗ[F2] V2 :=
    LinearEquiv.ofBijective f ⟨hf_injective, hf_surjective⟩
  apply lemma4_gorenstein_thompson_nonisomorphic_factors
    hH_two hH_nonabelian xi hxi_odd hL1_irreducible hL2_transitive
    n hn hL2_card
  refine ⟨e, ?_⟩
  intro w
  exact hf_equivariant w
private theorem lemma5_upperTriangular_quadratic
    {K E F : Type*} [Field K] [CharP K 2]
    [AddCommGroup E] [Module K E]
    [AddCommGroup F] [Module K F]
    (m : ℕ) (u : Module.Basis (Fin m) K E)
    (B : E →ₗ[K] E →ₗ[K] F)
    (hB_self : ∀ x : E, B x x = 0) :
    ∃ q : E → F,
      q 0 = 0 ∧
      (∀ x y : E, q (x + y) = q x + q y + B x y) ∧
      ∀ a : Fin m → K,
        q (∑ i : Fin m, a i • u i) =
          ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
            (a i * a j) • B (u i) (u j) := by
  classical
  have hadd_self (x : F) : x + x = 0 := by
    rw [← two_smul K x]
    simp only [CharTwo.two_eq_zero, zero_smul]
  have hB_symm (x y : E) : B x y = B y x := by
    have hsum : B x y + B y x = 0 := by
      have h := hB_self (x + y)
      simp only [map_add] at h
      simp only [LinearMap.add_apply] at h
      rw [hB_self x, hB_self y] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      B x y = B x y + (B y x + B y x) := by
        rw [hadd_self, add_zero]
      _ = (B x y + B y x) + B y x := by ac_rfl
      _ = B y x := by rw [hsum, zero_add]
  let A : E →ₗ[K] E →ₗ[K] F :=
    u.constr (S := K) fun i =>
      u.constr (S := K) fun j =>
        if i < j then B (u i) (u j) else 0
  have hA_basis (i j : Fin m) :
      A (u i) (u j) =
        if i < j then B (u i) (u j) else 0 := by
    change
      (u.constr (S := K) fun i =>
        u.constr (S := K) fun j =>
          if i < j then B (u i) (u j) else 0) (u i) (u j) = _
    rw [u.constr_basis, u.constr_basis]
  have hA_polar : A + LinearMap.flip A = B := by
    apply u.ext
    intro i
    apply u.ext
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
  let q : E → F := fun x => A x x
  have hq_zero : q 0 = 0 := by simp [q]
  have hq_add (x y : E) : q (x + y) = q x + q y + B x y := by
    have hp : A x y + A y x = B x y := by
      have h := LinearMap.congr_fun (LinearMap.congr_fun hA_polar x) y
      simpa [LinearMap.flip_apply] using h
    change A (x + y) (x + y) = A x x + A y y + B x y
    calc
      A (x + y) (x + y) =
          A x x + A y x + (A x y + A y y) := by
        simp only [map_add, LinearMap.add_apply]
      _ = A x x + A y y + B x y := by
        rw [← hp]
        abel
  refine ⟨q, hq_zero, hq_add, ?_⟩
  intro a
  change A (∑ i : Fin m, a i • u i) (∑ i : Fin m, a i • u i) = _
  simp_rw [LinearMap.map_sum₂, map_sum, LinearMap.map_smul₂, map_smul, hA_basis]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [show Finset.Ioi i = Finset.univ.filter (fun j : Fin m => i < j) by
    ext j
    simp]
  simp [Finset.sum_filter, mul_smul]
private theorem lemma5_square_formula_candidate
    {H : Type u} [Group H]
    (xi : MulAut H)
    (m : ℕ)
    (lambda : BinaryGaloisField m)
    (coordinates : BinaryGaloisField m ≃ₗ[F2]
      Additive (LowerCentralFactor H 0))
    (u : Module.Basis (Fin m) (BinaryGaloisField m)
      (BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 0)))
    (xiK : (BinaryGaloisField m ⊗[F2]
      Additive (LowerCentralFactor H 0)) ≃ₗ[BinaryGaloisField m]
        (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)))
    (bracket : Additive (LowerCentralFactor H 0) →ₗ[F2]
      Additive (LowerCentralFactor H 0) →ₗ[F2]
        Additive (LowerCentralFactor H 1))
    (bracketK : (BinaryGaloisField m ⊗[F2]
      Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
        (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
            (BinaryGaloisField m ⊗[F2]
              Additive (LowerCentralFactor H 1)))
    (hxiK_tmul :
      ∀ v : Additive (LowerCentralFactor H 0),
        xiK (1 ⊗ₜ[F2] v) =
          1 ⊗ₜ[F2] lowerCentralFactorLinearAut xi 0 v)
    (hu_eigen :
      ∀ i : Fin m,
        xiK (u i) = lambda ^ (2 ^ (i : ℕ)) • u i)
    (hcoordinates :
      ∀ alpha : BinaryGaloisField m,
        lowerCentralFactorLinearAut xi 0 (coordinates alpha) =
          coordinates (lambda * alpha))
    (hu_expansion :
      ∀ alpha : BinaryGaloisField m,
        1 ⊗ₜ[F2] coordinates alpha =
          ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i)
    (hbracketK_tmul :
      ∀ v w : Additive (LowerCentralFactor H 0),
        bracketK (1 ⊗ₜ[F2] v) (1 ⊗ₜ[F2] w) =
          1 ⊗ₜ[F2] bracket v w)
    (hbracket_equivariant :
      ∀ v w : Additive (LowerCentralFactor H 0),
        bracket (lowerCentralFactorLinearAut xi 0 v)
            (lowerCentralFactorLinearAut xi 0 w) =
          lowerCentralFactorLinearAut xi 1 (bracket v w))
    (hbracket_self :
      ∀ v : Additive (LowerCentralFactor H 0), bracket v v = 0) :
    ∃ candidate : Additive (LowerCentralFactor H 0) →
        BinaryGaloisField m ⊗[F2] Additive (LowerCentralFactor H 1),
      candidate 0 = 0 ∧
      (∀ v w : Additive (LowerCentralFactor H 0),
        candidate (v + w) =
          candidate v + candidate w + (1 ⊗ₜ[F2] bracket v w)) ∧
      (∀ v : Additive (LowerCentralFactor H 0),
        candidate (lowerCentralFactorLinearAut xi 0 v) =
          (lowerCentralFactorLinearAut xi 1).baseChange F2
            (BinaryGaloisField m)
            (Additive (LowerCentralFactor H 1))
            (Additive (LowerCentralFactor H 1)) (candidate v)) ∧
      ∀ alpha : BinaryGaloisField m,
        candidate (coordinates alpha) =
          ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
            alpha ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
              bracketK (u i) (u j) := by
  classical
  let K := BinaryGaloisField m
  let V1 := Additive (LowerCentralFactor H 0)
  let V2 := Additive (LowerCentralFactor H 1)
  let E := K ⊗[F2] V1
  let F := K ⊗[F2] V2
  let T : V1 ≃ₗ[F2] V1 := lowerCentralFactorLinearAut xi 0
  let S : V2 ≃ₗ[F2] V2 := lowerCentralFactorLinearAut xi 1
  let SK : F ≃ₗ[K] F := S.baseChange F2 K V2 V2
  have hadd_self_V2 (x : V2) : x + x = 0 := by
    rw [← two_smul F2 x]
    simp only [CharTwo.two_eq_zero, zero_smul]
  have hbracket_symm (v w : V1) : bracket v w = bracket w v := by
    have hsum : bracket v w + bracket w v = 0 := by
      have h := hbracket_self (v + w)
      simp only [map_add] at h
      simp only [LinearMap.add_apply] at h
      rw [hbracket_self v, hbracket_self w] at h
      simpa only [zero_add, add_zero, add_assoc, add_comm] using h
    calc
      bracket v w =
          bracket v w + (bracket w v + bracket w v) := by
        rw [hadd_self_V2, add_zero]
      _ = (bracket v w + bracket w v) + bracket w v := by ac_rfl
      _ = bracket w v := by rw [hsum, zero_add]
  have hadd_self_F (x : F) : x + x = 0 := by
    rw [← two_smul K x]
    simp only [CharTwo.two_eq_zero, zero_smul]
  have hbracketK_symm (x y : E) :
      bracketK x y = bracketK y x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b w =>
            have ha : a ⊗ₜ[F2] v = a • (1 ⊗ₜ[F2] v) := by
              rw [TensorProduct.smul_tmul']
              simp
            have hb : b ⊗ₜ[F2] w = b • (1 ⊗ₜ[F2] w) := by
              rw [TensorProduct.smul_tmul']
              simp
            rw [ha, hb, map_smul, LinearMap.map_smul₂,
              map_smul, LinearMap.map_smul₂,
              hbracketK_tmul, hbracketK_tmul, hbracket_symm]
            simp [smul_smul, mul_comm]
        | add y z hy hz =>
            simp only [map_add, LinearMap.add_apply]
            rw [hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply]
        rw [hx, hy]
  have hbracketK_self (x : E) : bracketK x x = 0 := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        have ha : a ⊗ₜ[F2] v = a • (1 ⊗ₜ[F2] v) := by
          rw [TensorProduct.smul_tmul']
          simp
        rw [ha, map_smul, LinearMap.map_smul₂,
          hbracketK_tmul, hbracket_self]
        simp
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply]
        rw [hx, hy, hbracketK_symm y x]
        simpa only [zero_add, add_zero] using
          hadd_self_F (bracketK x y)
  have hbracketK_equivariant (x y : E) :
      bracketK (xiK x) (xiK y) = SK (bracketK x y) := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
        induction y using TensorProduct.induction_on with
        | zero => simp
        | tmul b w =>
            have ha : a ⊗ₜ[F2] v = a • (1 ⊗ₜ[F2] v) := by
              rw [TensorProduct.smul_tmul']
              simp
            have hb : b ⊗ₜ[F2] w = b • (1 ⊗ₜ[F2] w) := by
              rw [TensorProduct.smul_tmul']
              simp
            rw [ha, hb]
            simp only [map_smul, LinearMap.smul_apply, smul_smul]
            rw [hxiK_tmul, hxiK_tmul,
              hbracketK_tmul, hbracketK_tmul,
              hbracket_equivariant,
              LinearEquiv.baseChange_tmul]
        | add y z hy hz =>
            simp only [map_add]
            rw [hy, hz]
    | add x y hx hy =>
        simp only [map_add, LinearMap.add_apply]
        rw [hx, hy]
  obtain ⟨q, hq_zero, hq_add, hq_coordinates⟩ :=
    lemma5_upperTriangular_quadratic m u bracketK hbracketK_self
  let candidate : V1 → F := fun v => q (1 ⊗ₜ[F2] v)
  have hcandidate_zero : candidate 0 = 0 := by
    simp [candidate, hq_zero]
  have hcandidate_add (v w : V1) :
      candidate (v + w) =
        candidate v + candidate w + (1 ⊗ₜ[F2] bracket v w) := by
    change q (1 ⊗ₜ[F2] (v + w)) =
      q (1 ⊗ₜ[F2] v) + q (1 ⊗ₜ[F2] w) +
        (1 ⊗ₜ[F2] bracket v w)
    rw [TensorProduct.tmul_add, hq_add, hbracketK_tmul]
  have hcandidate_formula (alpha : K) :
      candidate (coordinates alpha) =
        ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
          alpha ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
            bracketK (u i) (u j) := by
    change q (1 ⊗ₜ[F2] coordinates alpha) = _
    rw [hu_expansion, hq_coordinates]
    apply Finset.sum_congr rfl
    intro i _hi
    apply Finset.sum_congr rfl
    intro j _hj
    rw [← pow_add]
  have hSK_basis (i j : Fin m) :
      SK (bracketK (u i) (u j)) =
        lambda ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
          bracketK (u i) (u j) := by
    calc
      SK (bracketK (u i) (u j)) =
          bracketK (xiK (u i)) (xiK (u j)) :=
        (hbracketK_equivariant (u i) (u j)).symm
      _ = bracketK
          (lambda ^ (2 ^ (i : ℕ)) • u i)
          (lambda ^ (2 ^ (j : ℕ)) • u j) := by
        rw [hu_eigen, hu_eigen]
      _ = lambda ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
          bracketK (u i) (u j) := by
        rw [map_smul, LinearMap.map_smul₂, smul_smul, ← pow_add]
        simp [add_comm]
  have hcandidate_equivariant (v : V1) :
      candidate (T v) = SK (candidate v) := by
    let alpha : K := coordinates.symm v
    have hv : v = coordinates alpha := by
      simp [alpha]
    rw [hv]
    change candidate (lowerCentralFactorLinearAut xi 0
      (coordinates alpha)) = SK (candidate (coordinates alpha))
    rw [hcoordinates, hcandidate_formula, hcandidate_formula,
      map_sum]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [map_smul, hSK_basis, smul_smul, mul_pow]
    congr 1
    ring
  refine ⟨candidate, hcandidate_zero, hcandidate_add, ?_,
    hcandidate_formula⟩
  intro v
  simpa [T, S, SK, K, V1, V2, E, F] using
    hcandidate_equivariant v

private theorem lemma5_square_map_normal_form_uniqueness_core
    {H : Type u} [Group H] [Finite H]
    (hH_two : IsPGroup 2 H)
    (hH_nonabelian : ¬ IsMulCommutative H)
    (xi : MulAut H)
    (hxi_odd : Odd (orderOf xi))
    (hL1_irreducible :
      ∀ W : Submodule F2 (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n)
    (_hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1)
    (m : ℕ) (_hm : 0 < m)
    (lambda : BinaryGaloisField m)
    (coordinates : BinaryGaloisField m ≃ₗ[F2]
      Additive (LowerCentralFactor H 0))
    (u : Module.Basis (Fin m) (BinaryGaloisField m)
      (BinaryGaloisField m ⊗[F2]
        Additive (LowerCentralFactor H 0)))
    (xiK : (BinaryGaloisField m ⊗[F2]
      Additive (LowerCentralFactor H 0)) ≃ₗ[BinaryGaloisField m]
        (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)))
    (bracket : Additive (LowerCentralFactor H 0) →ₗ[F2]
      Additive (LowerCentralFactor H 0) →ₗ[F2]
        Additive (LowerCentralFactor H 1))
    (bracketK : (BinaryGaloisField m ⊗[F2]
      Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
        (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
            (BinaryGaloisField m ⊗[F2]
              Additive (LowerCentralFactor H 1)))
    (squareMap : Additive (LowerCentralFactor H 0) →
      Additive (LowerCentralFactor H 1))
    (_hL1_card : Nat.card (LowerCentralFactor H 0) = 2 ^ m)
    (_hlambda : lambda ≠ 0)
    (hxiK_tmul :
      ∀ v : Additive (LowerCentralFactor H 0),
        xiK (1 ⊗ₜ[F2] v) =
          1 ⊗ₜ[F2] lowerCentralFactorLinearAut xi 0 v)
    (hu_eigen :
      ∀ i : Fin m,
        xiK (u i) = lambda ^ (2 ^ (i : ℕ)) • u i)
    (hcoordinates :
      ∀ alpha : BinaryGaloisField m,
        lowerCentralFactorLinearAut xi 0 (coordinates alpha) =
          coordinates (lambda * alpha))
    (hu_expansion :
      ∀ alpha : BinaryGaloisField m,
        1 ⊗ₜ[F2] coordinates alpha =
          ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i)
    (hbracketK_tmul :
      ∀ v w : Additive (LowerCentralFactor H 0),
        bracketK (1 ⊗ₜ[F2] v) (1 ⊗ₜ[F2] w) =
          1 ⊗ₜ[F2] bracket v w)
    (hbracket_equivariant :
      ∀ v w : Additive (LowerCentralFactor H 0),
        bracket (lowerCentralFactorLinearAut xi 0 v)
            (lowerCentralFactorLinearAut xi 0 w) =
          lowerCentralFactorLinearAut xi 1 (bracket v w))
    (hbracket_self :
      ∀ v : Additive (LowerCentralFactor H 0), bracket v v = 0)
    (_hbracket_mk :
      ∀ x y : higmanLowerCentralSeries H 0,
        ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1,
          bracket
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨⁅(x : H), (y : H)⁆, hcomm⟩))
    (_hsquare_mk :
      ∀ x : higmanLowerCentralSeries H 0,
        ∀ hsquare : (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1,
          squareMap
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨(x : H) ^ 2, hsquare⟩))
    (hsquare_equivariant :
      ∀ v : Additive (LowerCentralFactor H 0),
        squareMap (lowerCentralFactorLinearAut xi 0 v) =
          lowerCentralFactorLinearAut xi 1 (squareMap v))
    (hsquare_add :
      ∀ v w : Additive (LowerCentralFactor H 0),
        squareMap (v + w) =
          squareMap v + squareMap w + bracket v w) :
    ∀ alpha : BinaryGaloisField m,
      1 ⊗ₜ[F2] squareMap (coordinates alpha) =
        ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
          alpha ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
            bracketK (u i) (u j) := by
  classical
  obtain ⟨candidate, hcandidate_zero, hcandidate_add,
      hcandidate_equivariant, hcandidate_formula⟩ :=
    lemma5_square_formula_candidate xi m lambda coordinates u xiK
      bracket bracketK hxiK_tmul hu_eigen hcoordinates hu_expansion
      hbracketK_tmul hbracket_equivariant hbracket_self
  let K := BinaryGaloisField m
  let V1 := Additive (LowerCentralFactor H 0)
  let V2 := Additive (LowerCentralFactor H 1)
  let T : V1 ≃ₗ[F2] V1 := lowerCentralFactorLinearAut xi 0
  let S : V2 ≃ₗ[F2] V2 := lowerCentralFactorLinearAut xi 1
  let SK : K ⊗[F2] V2 ≃ₗ[K] K ⊗[F2] V2 :=
    S.baseChange F2 K V2 V2
  let qK : V1 → K ⊗[F2] V2 :=
    fun v => 1 ⊗ₜ[F2] squareMap v
  have hq_add (v w : V1) :
      qK (v + w) =
        qK v + qK w + (1 ⊗ₜ[F2] bracket v w) := by
    simp [qK, hsquare_add, TensorProduct.tmul_add]
  have hq_zero : qK 0 = 0 := by
    have h := hq_add 0 0
    apply add_left_cancel (a := qK 0)
    simpa using h.symm
  have hq_equivariant (v : V1) :
      qK (T v) = SK (qK v) := by
    simp [qK, T, S, SK, hsquare_equivariant,
      LinearEquiv.baseChange_tmul]
  let d : V1 →ₗ[F2] K ⊗[F2] V2 :=
    { toFun := fun v => qK v - candidate v
      map_add' := by
        intro v w
        rw [hq_add, hcandidate_add]
        abel
      map_smul' := by
        intro a v
        have ha : a = 0 ∨ a = 1 := by
          fin_cases a
          · left
            rfl
          · right
            rfl
        rcases ha with rfl | rfl
        · simp only [RingHom.id_apply, zero_smul]
          rw [hq_zero, hcandidate_zero]
          simp
        · simp only [RingHom.id_apply, one_smul] }
  have hd_equivariant (v : V1) :
      d (T v) = SK (d v) := by
    change qK (T v) - candidate (T v) =
      SK (qK v - candidate v)
    rw [hq_equivariant]
    have hc := hcandidate_equivariant v
    change candidate (T v) = SK (candidate v) at hc
    rw [hc, map_sub]
  have hd_zero : d = 0 := by
    apply lemma5_no_scalarExtension_copy
      hH_two hH_nonabelian xi hxi_odd hL1_irreducible hL2_transitive
      n hn hL2_card m d
    intro v
    simpa [T, S, SK, K, V1, V2] using hd_equivariant v
  intro alpha
  have hz := LinearMap.congr_fun hd_zero (coordinates alpha)
  have hqc :
      qK (coordinates alpha) = candidate (coordinates alpha) := by
    apply sub_eq_zero.mp
    simpa [d] using hz
  simpa [qK, hcandidate_formula alpha] using hqc

/-- Higman Lemma 5. Under `H^2 = H_2`, squaring induces the displayed
quadratic map from `L_1` to `L_2` in every conjugate basis adapted to
`xi`. All spaces and actions in the statement are the canonical
lower-central ones. -/
public theorem lemma5_square_map_normal_form
    {H : Type u} [Group H] [Finite H]
    (hH_two : IsPGroup 2 H)
    (hH_nonabelian : ¬ IsMulCommutative H)
    (xi : MulAut H)
    (hxi_odd : Odd (orderOf xi))
    (hL1_irreducible :
      ∀ W : Submodule (F2) (Additive (LowerCentralFactor H 0)),
        (∀ v : Additive (LowerCentralFactor H 0), v ∈ W →
          lowerCentralFactorLinearAut xi 0 v ∈ W) →
        W = ⊥ ∨ W = ⊤)
    (hL2_transitive :
      ∀ x : Additive (LowerCentralFactor H 1), x ≠ 0 →
        ∀ y : Additive (LowerCentralFactor H 1), y ≠ 0 →
          ∃ k : ℕ, (lowerCentralFactorLinearAut xi 1 ^ k) x = y)
    (n : ℕ) (hn : 2 ≤ n)
    (hL2_card : Nat.card (LowerCentralFactor H 1) = 2 ^ n)
    (hH_square : squaresSubgroup H ≤ higmanLowerCentralSeries H 1) :
    ∃ (m : ℕ) (_hm : 0 < m)
        (lambda : BinaryGaloisField m)
        (coordinates : BinaryGaloisField m ≃ₗ[F2]
          Additive (LowerCentralFactor H 0))
        (u : Module.Basis (Fin m) (BinaryGaloisField m)
          (BinaryGaloisField m ⊗[F2]
            Additive (LowerCentralFactor H 0)))
        (xiK : (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)) ≃ₗ[BinaryGaloisField m]
            (BinaryGaloisField m ⊗[F2]
              Additive (LowerCentralFactor H 0)))
        (bracket : Additive (LowerCentralFactor H 0) →ₗ[F2]
          Additive (LowerCentralFactor H 0) →ₗ[F2]
            Additive (LowerCentralFactor H 1))
        (bracketK : (BinaryGaloisField m ⊗[F2]
          Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
            (BinaryGaloisField m ⊗[F2]
              Additive (LowerCentralFactor H 0)) →ₗ[BinaryGaloisField m]
                (BinaryGaloisField m ⊗[F2]
                  Additive (LowerCentralFactor H 1)))
        (squareMap : Additive (LowerCentralFactor H 0) →
          Additive (LowerCentralFactor H 1)),
      Nat.card (LowerCentralFactor H 0) = 2 ^ m ∧
      lambda ≠ 0 ∧
      (∀ alpha : BinaryGaloisField m,
        lowerCentralFactorLinearAut xi 0 (coordinates alpha) =
          coordinates (lambda * alpha)) ∧
      (∀ v : Additive (LowerCentralFactor H 0),
        xiK (1 ⊗ₜ[F2] v) =
          1 ⊗ₜ[F2] lowerCentralFactorLinearAut xi 0 v) ∧
      (∀ i : Fin m,
        xiK (u i) = lambda ^ (2 ^ (i : ℕ)) • u i) ∧
      (∀ alpha : BinaryGaloisField m,
        1 ⊗ₜ[F2] coordinates alpha =
          ∑ i : Fin m, alpha ^ (2 ^ (i : ℕ)) • u i) ∧
      (∀ v w : Additive (LowerCentralFactor H 0),
        bracketK (1 ⊗ₜ[F2] v) (1 ⊗ₜ[F2] w) =
          1 ⊗ₜ[F2] bracket v w) ∧
      (∀ x y : higmanLowerCentralSeries H 0,
        ∀ hcomm : ⁅(x : H), (y : H)⁆ ∈ higmanLowerCentralSeries H 1,
          bracket
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x))
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) y)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨⁅(x : H), (y : H)⁆, hcomm⟩)) ∧
      (∀ x : higmanLowerCentralSeries H 0,
        ∀ hsquare : (x : H) ^ 2 ∈ higmanLowerCentralSeries H 1,
          squareMap
              (Additive.ofMul
                (QuotientGroup.mk' (lowerCentralFactorKernel H 0) x)) =
            Additive.ofMul
              (QuotientGroup.mk' (lowerCentralFactorKernel H 1)
                ⟨(x : H) ^ 2, hsquare⟩)) ∧
      (∀ v : Additive (LowerCentralFactor H 0),
        squareMap (lowerCentralFactorLinearAut xi 0 v) =
          lowerCentralFactorLinearAut xi 1 (squareMap v)) ∧
      (∀ v w : Additive (LowerCentralFactor H 0),
        squareMap (v + w) =
          squareMap v + squareMap w + bracket v w) ∧
      ∀ alpha : BinaryGaloisField m,
        1 ⊗ₜ[F2] squareMap (coordinates alpha) =
          ∑ i : Fin m, ∑ j ∈ Finset.Ioi i,
            alpha ^ (2 ^ (i : ℕ) + 2 ^ (j : ℕ)) •
              bracketK (u i) (u j) := by
  obtain ⟨m, hm, lambda, coordinates, u, xiK,
      hL1_card, hlambda, hxiK_tmul, hu_eigen, hcoordinates, hu_expansion⟩ :=
    lemma5_square_map_normal_form_field_core
      xi hL1_irreducible n hn hL2_card
  obtain ⟨bracket, bracketK, squareMap,
      hbracketK_tmul, hbracket_equivariant, hbracket_self, hbracket_mk,
      _hbracket_span, hsquare_mk, hsquare_equivariant, hsquare_add⟩ :=
    lemma5_square_map_normal_form_quadratic_core xi m hH_square
  refine ⟨m, hm, lambda, coordinates, u, xiK, bracket, bracketK, squareMap,
    hL1_card, hlambda, hcoordinates, hxiK_tmul, hu_eigen, hu_expansion,
    hbracketK_tmul, hbracket_mk, hsquare_mk,
    hsquare_equivariant, hsquare_add, ?_⟩
  exact lemma5_square_map_normal_form_uniqueness_core
    hH_two hH_nonabelian xi hxi_odd hL1_irreducible hL2_transitive
    n hn hL2_card hH_square m hm lambda coordinates u xiK
    bracket bracketK squareMap hL1_card hlambda hxiK_tmul hu_eigen
    hcoordinates hu_expansion hbracketK_tmul hbracket_equivariant
    hbracket_self hbracket_mk hsquare_mk
    hsquare_equivariant hsquare_add

end Higman
end External
end CFSG.BenderSuzuki


























