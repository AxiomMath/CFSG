module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup

import CFSG.Walter.PSL2Facts.Even
import CFSG.Quasithin.Background.F918Z4bAut
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFrobenius

public section

namespace CFSG.Walter

open scoped MatrixGroups

private theorem mem_normalizer_of_conj_eq_of_mapsTo {G : Type*} [Group G] [Finite G]
    {φ : MulAut G} {b : G} (hb : φ = MulAut.conj b) {U : Subgroup G}
    (hU : ∀ x ∈ U, φ x ∈ U) : b ∈ Subgroup.normalizer (U : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    rw [Subgroup.mem_comap, ← hb]
    exact hU x hx
  · rw [Subgroup.card_map_of_injective (MulAut.conj b).injective]

private theorem eq_one_of_conj_eq_one_psl2 {K : Type*} [Field K] [Finite K] {c : PSL(2, K)}
    (h : MulAut.conj c = 1) : c = 1 := by
  have hc : c ∈ Subgroup.center (PSL(2, K)) := by
    rw [Subgroup.mem_center_iff]
    intro x
    have hx := congrArg (fun f : MulAut (PSL(2, K)) => f x) h
    simp only [MulAut.one_apply, MulAut.conj_apply] at hx
    have hx' : c * x = x * c := by
      calc c * x = (c * x * c⁻¹) * c := by group
        _ = x * c := by rw [hx]
    exact hx'.symm
  rw [CFSG.GorensteinWalter.psl2_center_eq_bot K, Subgroup.mem_bot] at hc
  exact hc

theorem psl2_even_aut_pow_gcd_mul_gcd_eq_one {n : ℕ} (hn : n ≠ 0)
    (θ : MulAut PSL(2, GaloisField 2 n)) (U : Sylow 2 PSL(2, GaloisField 2 n))
    (hU : ∀ x ∈ (U : Subgroup PSL(2, GaloisField 2 n)),
      θ x ∈ (U : Subgroup PSL(2, GaloisField 2 n)))
    {N : ℕ} (hN : Odd N) (hθ : θ ^ N = 1) :
    θ ^ (Nat.gcd N n * Nat.gcd N (2 ^ n - 1)) = 1 := by
  classical
  have hK : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n hn
  set σ : GaloisField 2 n ≃+* GaloisField 2 n :=
    CFSG.Quasithin.autFieldPart (GaloisField 2 n) θ with hσ
  have hσN : σ ^ N = 1 := by
    rw [hσ, ← map_pow, hθ, map_one]
  have hσn : σ ^ n = 1 := by
    have hcard : Nat.card (RingAut (GaloisField 2 n)) = n :=
      (CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.ringAut_card_and_cyclic
        (F := GaloisField 2 n) hK).1
    have h := pow_card_eq_one' (G := RingAut (GaloisField 2 n)) (x := σ)
    rwa [hcard] at h
  have hσe : σ ^ Nat.gcd N n = 1 := pow_gcd_eq_one.mpr ⟨hσN, hσn⟩
  obtain ⟨b, hb⟩ : ∃ b, θ ^ Nat.gcd N n = MulAut.conj b :=
    CFSG.Quasithin.exists_conj_of_autFieldPart_eq_one (K := GaloisField 2 n)
      (α := θ ^ Nat.gcd N n) (by rw [map_pow, ← hσ]; exact hσe)
  have hpowU : ∀ k : ℕ, ∀ x ∈ (U : Subgroup PSL(2, GaloisField 2 n)),
      (θ ^ k) x ∈ (U : Subgroup PSL(2, GaloisField 2 n)) := by
    intro k
    induction k with
    | zero => intro x hx; simpa using hx
    | succ k ih => intro x hx; rw [pow_succ']; exact hU _ (ih x hx)
  have hbU : b ∈ Subgroup.normalizer ((U : Subgroup PSL(2, GaloisField 2 n)) :
      Set PSL(2, GaloisField 2 n)) :=
    mem_normalizer_of_conj_eq_of_mapsTo hb (hpowU (Nat.gcd N n))
  have hbpow : b ^ (N / Nat.gcd N n) = 1 :=
    eq_one_of_conj_eq_one_psl2 (K := GaloisField 2 n) (by
      rw [map_pow, ← hb, ← pow_mul, Nat.mul_div_cancel' (Nat.gcd_dvd_left N n), hθ])
  have hbN : b ^ N = 1 := by
    rw [← Nat.mul_div_cancel' (Nat.gcd_dvd_left N n), mul_comm, pow_mul, hbpow, one_pow]
  have hbOrdN : orderOf b ∣ N := orderOf_dvd_of_pow_eq_one hbN
  have hbOrdOdd : Odd (orderOf b) := Odd.of_dvd_nat hN hbOrdN
  have hbOrdNorm : orderOf b ∣ Nat.card (Subgroup.normalizer
      ((U : Subgroup PSL(2, GaloisField 2 n)) : Set PSL(2, GaloisField 2 n))) :=
    Subgroup.orderOf_dvd_natCard _ hbU
  rw [psl2_even_card_normalizer_sylow_two hn U] at hbOrdNorm
  have hcop : Nat.Coprime (orderOf b) (2 ^ n) := by
    have h2 : Nat.Coprime (orderOf b) 2 := hbOrdOdd.coprime_two_right
    simpa using h2.pow_right n
  have hbOrde2 : orderOf b ∣ Nat.gcd N (2 ^ n - 1) :=
    Nat.dvd_gcd hbOrdN (hcop.dvd_of_dvd_mul_left hbOrdNorm)
  have hbe2 : b ^ Nat.gcd N (2 ^ n - 1) = 1 := orderOf_dvd_iff_pow_eq_one.mp hbOrde2
  calc θ ^ (Nat.gcd N n * Nat.gcd N (2 ^ n - 1))
      = (θ ^ Nat.gcd N n) ^ Nat.gcd N (2 ^ n - 1) := pow_mul _ _ _
    _ = (MulAut.conj b) ^ Nat.gcd N (2 ^ n - 1) := by rw [hb]
    _ = MulAut.conj (b ^ Nat.gcd N (2 ^ n - 1)) := (map_pow _ _ _).symm
    _ = 1 := by rw [hbe2, map_one]

theorem psl2_mulAut_pow_gcd_mul_gcd_eq_one_of_mulEquiv {A : Type*} [Group A] [Finite A]
    {n : ℕ} (hn : n ≠ 0) (e : A ≃* PSL(2, GaloisField 2 n)) (ψ : MulAut A)
    (T : Sylow 2 A) (hT : ∀ x ∈ (T : Subgroup A), ψ x ∈ (T : Subgroup A))
    {N : ℕ} (hN : Odd N) (hψ : ψ ^ N = 1) :
    ψ ^ (Nat.gcd N n * Nat.gcd N (2 ^ n - 1)) = 1 := by
  let θ : MulAut PSL(2, GaloisField 2 n) := (MulAut.congr e) ψ
  let U : Sylow 2 PSL(2, GaloisField 2 n) :=
    T.mapSurjective (f := e.toMonoidHom) e.surjective
  have hUcoe : (U : Subgroup PSL(2, GaloisField 2 n)) =
      (T : Subgroup A).map e.toMonoidHom :=
    Sylow.coe_mapSurjective (f := e.toMonoidHom) e.surjective T
  have hU : ∀ x ∈ (U : Subgroup PSL(2, GaloisField 2 n)),
      θ x ∈ (U : Subgroup PSL(2, GaloisField 2 n)) := by
    intro x hx
    rw [hUcoe] at hx ⊢
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    have hcongr : θ (e t) = e (ψ t) := by
      simp [θ, MulAut.congr]
    refine Subgroup.mem_map.mpr ⟨ψ t, hT t ht, ?_⟩
    exact hcongr.symm
  have hθN : θ ^ N = 1 := by
    have h : ((MulAut.congr e) ψ) ^ N = 1 := by
      rw [← map_pow, hψ, map_one]
    exact h
  have hθd := psl2_even_aut_pow_gcd_mul_gcd_eq_one hn θ U hU hN hθN
  apply (MulAut.congr e).injective
  rw [map_pow, map_one]
  exact hθd

end CFSG.Walter

end
