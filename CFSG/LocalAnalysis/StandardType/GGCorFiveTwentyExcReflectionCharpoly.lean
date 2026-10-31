module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcInvolutionCharpoly
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Univ
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Basic.Real.Basic

public section

namespace CFSG.StandardType

open Polynomial Module Matrix

lemma rootMultiplicity_one_pow_X_sub_one_mul_X_add_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (a b : ℕ) :
    rootMultiplicity (1 : F) ((X - 1 : F[X]) ^ a * (X + 1) ^ b) = a := by
  have hR : (X + 1 : F[X]) = X - C (-1) := by
    rw [map_neg, map_one, sub_neg_eq_add]
  have hne : (X - 1 : F[X]) ^ a * (X + 1) ^ b ≠ 0 :=
    mul_ne_zero
      (pow_ne_zero _ (by
        rw [show (X - 1 : F[X]) = X - C (1 : F) by rw [map_one]]
        exact X_sub_C_ne_zero 1))
      (pow_ne_zero _ (by rw [hR]; exact X_sub_C_ne_zero (-1)))
  rw [rootMultiplicity_mul hne]
  have hleft : rootMultiplicity (1 : F) ((X - 1 : F[X]) ^ a) = a := by
    rw [show (X - 1 : F[X]) = X - C (1 : F) by rw [map_one], rootMultiplicity_X_sub_C_pow]
  have hright : rootMultiplicity (1 : F) ((X + 1 : F[X]) ^ b) = 0 := by
    apply rootMultiplicity_eq_zero
    intro hroot
    rw [hR, IsRoot.def, eval_pow] at hroot
    have hb : (X - C (-1) : F[X]).eval (1 : F) ≠ 0 := by
      rw [eval_sub, eval_X, eval_C]
      have h : (1 : F) - (-1) = 2 := by ring
      rw [h]; exact h2
    exact pow_ne_zero b hb hroot
  rw [hleft, hright, add_zero]

lemma rootMultiplicity_neg_one_pow_X_sub_one_mul_X_add_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    (a b : ℕ) :
    rootMultiplicity (-1 : F) ((X - 1 : F[X]) ^ a * (X + 1) ^ b) = b := by
  have hL : (X - 1 : F[X]) = X - C (1 : F) := by rw [map_one]
  have hR : (X + 1 : F[X]) = X - C (-1) := by
    rw [map_neg, map_one, sub_neg_eq_add]
  have hne : (X - 1 : F[X]) ^ a * (X + 1) ^ b ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (by rw [hL]; exact X_sub_C_ne_zero 1))
      (pow_ne_zero _ (by rw [hR]; exact X_sub_C_ne_zero (-1)))
  rw [rootMultiplicity_mul hne]
  have hleft : rootMultiplicity (-1 : F) ((X - 1 : F[X]) ^ a) = 0 := by
    rw [hL]
    apply rootMultiplicity_eq_zero
    intro hroot
    rw [IsRoot.def, eval_pow] at hroot
    have hb : (X - C (1 : F) : F[X]).eval (-1 : F) ≠ 0 := by
      rw [eval_sub, eval_X, eval_C]
      have h : (-1 : F) - 1 = -2 := by ring
      rw [h]
      exact neg_ne_zero.mpr h2
    exact pow_ne_zero a hb hroot
  have hright : rootMultiplicity (-1 : F) ((X + 1 : F[X]) ^ b) = b := by
    rw [hR, rootMultiplicity_X_sub_C_pow]
  rw [hleft, hright, zero_add]

theorem pow_mul_pow_eq_iff {F : Type*} [Field F] (h2 : (2 : F) ≠ 0) {a b c d : ℕ}
    (h : (X - 1 : F[X]) ^ a * (X + 1) ^ b = (X - 1) ^ c * (X + 1) ^ d) : a = c ∧ b = d := by
  have h1 := congrArg (rootMultiplicity (1 : F)) h
  have h2' := congrArg (rootMultiplicity (-1 : F)) h
  rw [rootMultiplicity_one_pow_X_sub_one_mul_X_add_one h2,
    rootMultiplicity_one_pow_X_sub_one_mul_X_add_one h2] at h1
  rw [rootMultiplicity_neg_one_pow_X_sub_one_mul_X_add_one h2,
    rootMultiplicity_neg_one_pow_X_sub_one_mul_X_add_one h2] at h2'
  exact ⟨h1, h2'⟩

lemma finrank_ker_sub_one_add_one_eq_of_natCard_fixed {n : Type*} [Fintype n] [DecidableEq n]
    {p k : ℕ} [Fact p.Prime] (hp2 : (2 : ZMod p) ≠ 0) (M : Matrix n n (ZMod p))
    (hM : M * M = 1) (hcard : Fintype.card n = k + 1)
    (hfix : Nat.card {f : n → ZMod p // M *ᵥ f = f} = p ^ k) :
    finrank (ZMod p) (LinearMap.ker (M.mulVecLin - 1)) = k ∧
      finrank (ZMod p) (LinearMap.ker (M.mulVecLin + 1)) = 1 := by
  have hp : p.Prime := Fact.out
  have hcardker : Nat.card (LinearMap.ker (M.mulVecLin - 1)) =
      Nat.card {f : n → ZMod p // M *ᵥ f = f} := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun f => by
      simp only [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply,
        Matrix.mulVecLin_apply, sub_eq_zero])
  have h1 : p ^ finrank (ZMod p) (LinearMap.ker (M.mulVecLin - 1)) =
      Nat.card (LinearMap.ker (M.mulVecLin - 1)) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  have hpow : p ^ finrank (ZMod p) (LinearMap.ker (M.mulVecLin - 1)) = p ^ k := by
    rw [h1, hcardker, hfix]
  have ha : finrank (ZMod p) (LinearMap.ker (M.mulVecLin - 1)) = k :=
    Nat.pow_right_injective hp.two_le hpow
  have hab := finrank_ker_matrix_involution_add hp2 M hM
  have hb : finrank (ZMod p) (LinearMap.ker (M.mulVecLin + 1)) = 1 := by
    have hsum : finrank (ZMod p) (LinearMap.ker (M.mulVecLin - 1)) +
        finrank (ZMod p) (LinearMap.ker (M.mulVecLin + 1)) = k + 1 := by
      rw [hab, hcard]
    omega
  exact ⟨ha, hb⟩

theorem charpoly_eq_of_natCard_fixed_zmod {n : Type*} [Fintype n] [DecidableEq n] {p k : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) (M : Matrix n n ℤ) (hM : M * M = 1)
    (hcard : Fintype.card n = k + 1)
    (hfix : Nat.card {f : n → ZMod p // (M.map (Int.castRingHom (ZMod p))) *ᵥ f = f} = p ^ k) :
    M.charpoly = (X - 1) ^ k * (X + 1) := by
  have hp : p.Prime := Fact.out
  have h2p : (2 : ZMod p) ≠ 0 := by
    intro h
    have hdvd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
  have h2Q : (2 : ℚ) ≠ 0 := by norm_num
  let fQ : ℤ →+* ℚ := Int.castRingHom ℚ
  let fP : ℤ →+* ZMod p := Int.castRingHom (ZMod p)
  let MQ : Matrix n n ℚ := M.map fQ
  let MP : Matrix n n (ZMod p) := M.map fP
  have hMQ : MQ * MQ = 1 := by
    dsimp [MQ]
    rw [← Matrix.map_mul, hM]
    simp
  have hMP : MP * MP = 1 := by
    dsimp [MP]
    rw [← Matrix.map_mul, hM]
    simp
  have hPQ : M.charpoly.map fQ =
      (X - 1 : ℚ[X]) ^ finrank ℚ (LinearMap.ker (MQ.mulVecLin - 1)) *
        (X + 1) ^ finrank ℚ (LinearMap.ker (MQ.mulVecLin + 1)) := by
    rw [← Matrix.charpoly_map M fQ, charpoly_matrix_involution h2Q MQ hMQ]
  have hPint : M.charpoly = (X - 1 : ℤ[X]) ^ finrank ℚ (LinearMap.ker (MQ.mulVecLin - 1)) *
      (X + 1) ^ finrank ℚ (LinearMap.ker (MQ.mulVecLin + 1)) := by
    apply Polynomial.map_injective fQ (RingHom.injective_int fQ)
    rw [hPQ]
    simp
  have hPp : M.charpoly.map fP =
      (X - 1 : (ZMod p)[X]) ^ finrank (ZMod p) (LinearMap.ker (MP.mulVecLin - 1)) *
        (X + 1) ^ finrank (ZMod p) (LinearMap.ker (MP.mulVecLin + 1)) := by
    rw [← Matrix.charpoly_map M fP, charpoly_matrix_involution h2p MP hMP]
  have hker := finrank_ker_sub_one_add_one_eq_of_natCard_fixed h2p MP hMP hcard
    (by simpa only [MP, fP] using hfix)
  obtain ⟨haP, hbP⟩ := hker
  have hPp' : M.charpoly.map fP = (X - 1 : (ZMod p)[X]) ^ k * (X + 1) ^ 1 := by
    rw [hPp, haP, hbP]
  have hPp'' : M.charpoly.map fP =
      (X - 1 : (ZMod p)[X]) ^ finrank ℚ (LinearMap.ker (MQ.mulVecLin - 1)) *
        (X + 1) ^ finrank ℚ (LinearMap.ker (MQ.mulVecLin + 1)) := by
    rw [hPint]
    simp
  have heq : (X - 1 : (ZMod p)[X]) ^ finrank ℚ (LinearMap.ker (MQ.mulVecLin - 1)) *
        (X + 1) ^ finrank ℚ (LinearMap.ker (MQ.mulVecLin + 1)) =
      (X - 1 : (ZMod p)[X]) ^ k * (X + 1) ^ 1 :=
    hPp''.symm.trans hPp'
  obtain ⟨haQ, hbQ⟩ := pow_mul_pow_eq_iff h2p heq
  rw [hPint, haQ, hbQ, pow_one]

end CFSG.StandardType

end
