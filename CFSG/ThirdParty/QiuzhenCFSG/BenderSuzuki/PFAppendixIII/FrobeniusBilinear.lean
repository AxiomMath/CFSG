module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

namespace CFSG
end CFSG
open CFSG

/-!
# Frobenius coordinates for binary bilinear maps
-/

namespace CFSG.BenderSuzuki
namespace PFAppendixIII

set_option maxHeartbeats 800000 in
/-- Every binary bilinear map on a binary Galois field has a unique expansion
in products of Frobenius conjugates. -/
public theorem frobeniusBilinear_expansion
    (n : ℕ) (hn : 0 < n)
    (B : BinaryGaloisField n →ₗ[ZMod 2]
      BinaryGaloisField n →ₗ[ZMod 2] BinaryGaloisField n) :
    ∃ coeff : Fin n → Fin n → BinaryGaloisField n,
      ∀ a b : BinaryGaloisField n,
        B a b = ∑ i : Fin n, ∑ j : Fin n,
          coeff i j * a ^ (2 ^ (i : ℕ)) * b ^ (2 ^ (j : ℕ)) := by
  classical
  let K := BinaryGaloisField n
  let sigma : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  let frob (i : Fin n) : K →ₗ[ZMod 2] K := (sigma ^ (i : ℕ)).toLinearMap
  have hsigma_order : orderOf sigma = n := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      GaloisField.finrank 2 hn.ne']
  let fhom (i : Fin n) : K →* K := (sigma ^ (i : ℕ)).toMonoidHom
  have hfhom : Function.Injective fhom := by
    intro i j hij
    have hp : sigma ^ (i : ℕ) = sigma ^ (j : ℕ) := by
      apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun hij x
    have hmod := pow_eq_pow_iff_modEq.mp hp
    rw [hsigma_order] at hmod
    exact Fin.ext (hmod.eq_of_lt_of_lt i.isLt j.isLt)
  have hfun : LinearIndependent K (fun i : Fin n => (fhom i : K → K)) :=
    (linearIndependent_monoidHom K K).comp fhom hfhom
  have hfrob : LinearIndependent K frob := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    apply (Fintype.linearIndependent_iff.mp hfun g ?_ i)
    funext x
    have hx := LinearMap.congr_fun hg x
    simpa [frob, fhom] using hx
  have hfinrank_linear : Module.finrank K (K →ₗ[ZMod 2] K) = n := by
    rw [Module.finrank_linearMap, GaloisField.finrank 2 hn.ne']
    simp
  letI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let basis : Module.Basis (Fin n) K (K →ₗ[ZMod 2] K) :=
    basisOfLinearIndependentOfCardEqFinrank hfrob (by
      simpa using hfinrank_linear.symm)
  have hbasis (i : Fin n) : basis i = frob i := by
    simp [basis]
  have hfrob_apply (i : Fin n) (x : K) :
      frob i x = x ^ (2 ^ (i : ℕ)) := by
    change (sigma ^ (i : ℕ)) x = _
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  let d (j : Fin n) : K →ₗ[ZMod 2] K :=
    ({ toFun := fun a => basis.repr (B a) j
       map_zero' := by simp
       map_add' := by
         intro a b
         simp } : K →+ K).toZModLinearMap 2
  have hd_apply (j : Fin n) (x : K) :
      d j x = basis.repr (B x) j := rfl
  let coeff : Fin n → Fin n → K := fun i j => basis.repr (d j) i
  refine ⟨coeff, ?_⟩
  intro a b
  have houter := congrArg (fun L : K →ₗ[ZMod 2] K => L b)
    (basis.sum_repr (B a))
  have hinner (j : Fin n) := congrArg (fun L : K →ₗ[ZMod 2] K => L a)
    (basis.sum_repr (d j))
  have houter' : ∑ j : Fin n,
      basis.repr (B a) j * basis j b = B a b := by
    simpa only [map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul] using houter
  have hinner' (j : Fin n) : ∑ i : Fin n,
      basis.repr (d j) i * basis i a = d j a := by
    simpa only [map_sum, LinearMap.sum_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul] using hinner j
  calc
    B a b = ∑ j : Fin n, d j a * b ^ (2 ^ (j : ℕ)) := by
      rw [← houter']
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hd_apply, hbasis, hfrob_apply]
    _ = ∑ j : Fin n, (∑ i : Fin n,
          coeff i j * a ^ (2 ^ (i : ℕ))) * b ^ (2 ^ (j : ℕ)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      congr 1
      rw [← hinner' j]
      simp only [coeff, hbasis, hfrob_apply]
    _ = ∑ i : Fin n, ∑ j : Fin n,
          coeff i j * a ^ (2 ^ (i : ℕ)) * b ^ (2 ^ (j : ℕ)) := by
      have hdist (j : Fin n) :
          (∑ i : Fin n, coeff i j * a ^ (2 ^ (i : ℕ))) *
              b ^ (2 ^ (j : ℕ)) =
            ∑ i : Fin n,
              (coeff i j * a ^ (2 ^ (i : ℕ))) * b ^ (2 ^ (j : ℕ)) := by
        simpa using (Finset.sum_mul (Finset.univ : Finset (Fin n))
          (fun i : Fin n => coeff i j * a ^ (2 ^ (i : ℕ)))
          (b ^ (2 ^ (j : ℕ))))
      rw [show (∑ j : Fin n,
          (∑ i : Fin n, coeff i j * a ^ (2 ^ (i : ℕ))) *
            b ^ (2 ^ (j : ℕ))) =
          ∑ j : Fin n, ∑ i : Fin n,
            (coeff i j * a ^ (2 ^ (i : ℕ))) * b ^ (2 ^ (j : ℕ)) by
        apply Finset.sum_congr rfl
        intro j _hj
        exact hdist j]
      rw [Finset.sum_comm]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 800000 in
/-- An equivariant binary bilinear map has Frobenius coefficients supported
only on the corresponding character relation. -/
public theorem frobeniusBilinear_expansion_with_support_of_equivariant
    (n : ℕ) (hn : 0 < n)
    (B : BinaryGaloisField n →ₗ[ZMod 2]
      BinaryGaloisField n →ₗ[ZMod 2] BinaryGaloisField n)
    (alpha beta gamma : BinaryGaloisField n)
    (hequiv : ∀ a b, B (alpha * a) (beta * b) = gamma * B a b) :
    ∃ coeff : Fin n → Fin n → BinaryGaloisField n,
      (∀ a b, B a b = ∑ i : Fin n, ∑ j : Fin n,
        coeff i j * a ^ (2 ^ (i : ℕ)) * b ^ (2 ^ (j : ℕ))) ∧
      ∀ i j, coeff i j ≠ 0 →
        alpha ^ (2 ^ (i : ℕ)) * beta ^ (2 ^ (j : ℕ)) = gamma := by
  classical
  let K := BinaryGaloisField n
  let sigma : K ≃ₐ[ZMod 2] K :=
    FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod 2) K
  obtain ⟨coeff, hcoeffExpansion⟩ :=
    frobeniusBilinear_expansion n hn B
  refine ⟨coeff, hcoeffExpansion, ?_⟩
  have hsigma_order : orderOf sigma = n := by
    rw [FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic,
      GaloisField.finrank 2 hn.ne']
  let fhom (i : Fin n) : K →* K :=
    (sigma ^ (i : ℕ)).toMonoidHom
  have hfhom : Function.Injective fhom := by
    intro i j hij
    have hp : sigma ^ (i : ℕ) = sigma ^ (j : ℕ) := by
      apply AlgEquiv.ext
      intro x
      exact DFunLike.congr_fun hij x
    have hmod := pow_eq_pow_iff_modEq.mp hp
    rw [hsigma_order] at hmod
    exact Fin.ext (hmod.eq_of_lt_of_lt i.isLt j.isLt)
  have hfun :
      LinearIndependent K (fun i : Fin n => (fhom i : K → K)) :=
    (linearIndependent_monoidHom K K).comp fhom hfhom
  have hfrob_apply (i : Fin n) (x : K) :
      (fhom i : K → K) x = x ^ (2 ^ (i : ℕ)) := by
    change (sigma ^ (i : ℕ)) x = _
    rw [AlgEquiv.coe_pow,
      FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
    simp [ZMod.card]
  have houter_eq (a b : K) :
      (∑ i : Fin n,
          (∑ j : Fin n, coeff i j *
            alpha ^ (2 ^ (i : ℕ)) *
              beta ^ (2 ^ (j : ℕ)) *
                b ^ (2 ^ (j : ℕ))) * a ^ (2 ^ (i : ℕ))) =
        ∑ i : Fin n,
          (∑ j : Fin n, gamma * coeff i j *
            b ^ (2 ^ (j : ℕ))) * a ^ (2 ^ (i : ℕ)) := by
    calc
      (∑ i : Fin n,
          (∑ j : Fin n, coeff i j *
            alpha ^ (2 ^ (i : ℕ)) *
              beta ^ (2 ^ (j : ℕ)) *
                b ^ (2 ^ (j : ℕ))) * a ^ (2 ^ (i : ℕ))) =
          B (alpha * a) (beta * b) := by
        rw [hcoeffExpansion]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        rw [mul_pow, mul_pow]
        ring
      _ = gamma * B a b := hequiv a b
      _ = ∑ i : Fin n,
          (∑ j : Fin n, gamma * coeff i j *
            b ^ (2 ^ (j : ℕ))) * a ^ (2 ^ (i : ℕ)) := by
        rw [hcoeffExpansion, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _hj
        ring
  have houter_coeff (i : Fin n) (b : K) :
      (∑ j : Fin n, coeff i j *
          alpha ^ (2 ^ (i : ℕ)) *
            beta ^ (2 ^ (j : ℕ)) * b ^ (2 ^ (j : ℕ))) =
        ∑ j : Fin n, gamma * coeff i j *
          b ^ (2 ^ (j : ℕ)) := by
    let g : Fin n → K := fun i =>
      (∑ j : Fin n, coeff i j *
          alpha ^ (2 ^ (i : ℕ)) *
            beta ^ (2 ^ (j : ℕ)) * b ^ (2 ^ (j : ℕ))) -
        ∑ j : Fin n, gamma * coeff i j *
          b ^ (2 ^ (j : ℕ))
    have hg : ∑ i : Fin n, g i • (fhom i : K → K) = 0 := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
        smul_eq_mul, g, hfrob_apply, sub_mul]
      rw [Finset.sum_sub_distrib]
      exact sub_eq_zero.mpr (houter_eq a b)
    exact sub_eq_zero.mp
      (Fintype.linearIndependent_iff.mp hfun g hg i)
  intro i j hij
  let g : Fin n → K := fun j =>
    coeff i j * alpha ^ (2 ^ (i : ℕ)) *
        beta ^ (2 ^ (j : ℕ)) -
      gamma * coeff i j
  have hg : ∑ j : Fin n, g j • (fhom j : K → K) = 0 := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply,
      smul_eq_mul, g, hfrob_apply, sub_mul]
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (houter_coeff i b)
  have hcoeff := Fintype.linearIndependent_iff.mp hfun g hg j
  change coeff i j * alpha ^ (2 ^ (i : ℕ)) *
      beta ^ (2 ^ (j : ℕ)) - gamma * coeff i j = 0 at hcoeff
  apply mul_left_cancel₀ hij
  calc
    coeff i j *
          (alpha ^ (2 ^ (i : ℕ)) * beta ^ (2 ^ (j : ℕ))) =
        coeff i j * alpha ^ (2 ^ (i : ℕ)) *
          beta ^ (2 ^ (j : ℕ)) := by rw [mul_assoc]
    _ = gamma * coeff i j := sub_eq_zero.mp hcoeff
    _ = coeff i j * gamma := by rw [mul_comm]
end PFAppendixIII
end CFSG.BenderSuzuki
