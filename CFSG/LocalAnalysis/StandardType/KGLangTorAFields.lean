module

public import CFSG.GroupTheory.SteinbergBKSemilinearFixedBasis
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.FieldTheory.Finite.Basic
import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryField
import CFSG.SignalizerFunctorTheorem.CatalogBridge.FixedFieldCard
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib

public section

namespace CFSG.StandardType

open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

theorem kgLangTorA_hilbert90 {F : Type} [Field F] {p : ℕ} (hp : p.Prime) {σ : F ≃+* F}
    (hσ : orderOf σ = p) {ω : F} (hω : σ ω = ω) (hωp : ω ^ p = 1) :
    ∃ u : Fˣ, σ (u : F) = ω * u := by
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    exact hp.ne_one hσ.symm
  have hω0 : ω ≠ 0 := by
    intro h0
    rw [h0, zero_pow hp.ne_zero] at hωp
    exact zero_ne_one hωp
  have hfix : ∀ i : ℕ, (σ ^ i) ω⁻¹ = ω⁻¹ := by
    intro i
    have hωi : (σ ^ i) ω = ω := by
      induction i with
      | zero => rw [pow_zero, RingAut.one_apply]
      | succ i ih => rw [pow_succ', RingAut.mul_apply, ih, hω]
    simpa using congrArg Inv.inv hωi
  have hN : TableBUF.partNorm σ ω⁻¹ p = 1 := by
    simp only [TableBUF.partNorm]
    rw [Finset.prod_congr rfl (fun i _ => hfix i)]
    simp [Finset.prod_const, Finset.card_range, ← inv_pow, hωp]
  obtain ⟨b, hb0, hb⟩ := TableBUF.exists_hilbert90 hp hσp hσ1 (inv_ne_zero hω0) hN
  refine ⟨Units.mk0 b hb0, ?_⟩
  change σ b = ω * b
  rw [hb, inv_inv]

theorem kgLangTorA_hilbert90_unitary {F : Type} [Field F] [Finite F] {n p : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = (2 ^ n) ^ 2) (hp : p.Prime) {σ : F ≃+* F} (hσ : orderOf σ = p)
    {ω : F} (hωp : ω ^ p = 1) (hωq : ω ^ (2 ^ n + 1) = 1) :
    ∃ c : F, c ^ (2 ^ n + 1) = 1 ∧ σ c = ω * c := by
  have hσp : σ ^ p = 1 := hσ ▸ pow_orderOf_eq_one σ
  have hσ1 : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hσ
    exact hp.ne_one hσ.symm
  have hω : σ ω = ω := TableBUF.ringEquiv_apply_eq_of_pow_eq_one hp hσp hωp
  have hfix : ∀ i : ℕ, (σ ^ i) ω = ω := by
    intro i
    induction i with
    | zero => rw [pow_zero, RingAut.one_apply]
    | succ i ih => rw [pow_succ', RingAut.mul_apply, ih, hω]
  have hN : TableBUF.partNorm σ ω p = 1 := by
    simp only [TableBUF.partNorm]
    rw [Finset.prod_congr rfl (fun i _ => hfix i)]
    simp [Finset.prod_const, Finset.card_range, hωp]
  exact TableBUF.exists_hilbert90_unitary hF
    (Even.pow_of_ne_zero even_two (by omega : n ≠ 0)) Nat.one_le_two_pow hp hσp hσ1 hωq hN

theorem kgLangTorA_aeval_pow_card {d p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hpF : ¬ p ∣ Nat.card F) {e : Matrix (Fin d) (Fin d) F} (he : e ^ p = 1)
    (P : Polynomial F) :
    Polynomial.aeval e P ^ (Nat.card F ^ (p - 1)) = Polynomial.aeval e P := by
  haveI := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card]
  have hQstep : ∀ x : Matrix (Fin d) (Fin d) F,
      Polynomial.aeval x P ^ Fintype.card F = Polynomial.aeval (x ^ Fintype.card F) P := by
    intro x
    rw [← map_pow, ← FiniteField.expand_card P, Polynomial.expand_aeval]
  have hkey : ∀ k : ℕ, Polynomial.aeval e P ^ (Fintype.card F ^ k) =
      Polynomial.aeval (e ^ (Fintype.card F ^ k)) P := by
    intro k
    induction k with
    | zero => rw [pow_zero, pow_one, pow_one]
    | succ k ih =>
      rw [pow_succ, pow_mul, ih, hQstep, pow_mul]
  have hcop : Nat.Coprime (Fintype.card F) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr
      (by simpa [Nat.card_eq_fintype_card] using hpF)).symm
  have hmod : Fintype.card F ^ (p - 1) ≡ 1 [MOD p] := by
    simpa [Nat.totient_prime hp] using Nat.ModEq.pow_totient hcop
  have hep : e ^ (Fintype.card F ^ (p - 1)) = e := by
    simpa using pow_eq_pow_of_modEq hmod he
  rw [hkey (p - 1), hep]

private theorem kgLangTorAFldAux_map_scalar {d : ℕ} {F : Type} [Field F] (f : F →+* F) (a : F) :
    (Matrix.scalar (Fin d) a).map f = Matrix.scalar (Fin d) (f a) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  · simp [Matrix.scalar_apply, Matrix.diagonal_apply, h]

theorem kgLangTorA_unitary_correct {d n p : ℕ} {F : Type} [Field F] [Finite F] (hp : p.Prime)
    (hp2 : p ≠ 2) (hF : Nat.card F = (2 ^ n) ^ 2) {σ : F ≃+* F} {e : GL (Fin d) F}
    (heu : Matrix.transpose ((e : Matrix (Fin d) (Fin d) F).map (· ^ 2 ^ n)) *
      (e : Matrix (Fin d) (Fin d) F) = 1)
    (he : Matrix.GeneralLinearGroup.map (σ : F →+* F) e = e) (hep : e ^ p = 1)
    {s : GL (Fin d) F} {P : Polynomial F}
    (hs : (s : Matrix (Fin d) (Fin d) F) = Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) P)
    (hsσ : Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * e) :
    ∃ (s' : GL (Fin d) F) (P' : Polynomial F),
      (s' : Matrix (Fin d) (Fin d) F) = Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) P' ∧
      Matrix.transpose ((s' : Matrix (Fin d) (Fin d) F).map (· ^ 2 ^ n)) *
        (s' : Matrix (Fin d) (Fin d) F) = 1 ∧
      Matrix.GeneralLinearGroup.map (σ : F →+* F) s' = s' * e := by
  haveI := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm]
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2 * n) (by simpa using hcardF)
  let φ : F →+* F := iterateFrobenius F 2 n
  have hφ : ∀ x : F, φ x = x ^ 2 ^ n := fun x => iterateFrobenius_def 2 n x
  have hφφ : ∀ x : F, φ (φ x) = x := by
    intro x
    rw [hφ, hφ, ← pow_mul]
    rw [show 2 ^ n * 2 ^ n = 2 ^ (2 * n) by rw [← pow_add]; congr 1; omega, ← hcardF]
    exact FiniteField.pow_card x
  have hσφ : ∀ x : F, σ (φ x) = φ (σ x) := by
    intro x
    rw [hφ, hφ, map_pow]
  let star : Matrix (Fin d) (Fin d) F → Matrix (Fin d) (Fin d) F :=
    fun M => Matrix.transpose (M.map ⇑φ)
  have star_add : ∀ M N, star (M + N) = star M + star N := by
    intro M N; ext i j; simp [star, Matrix.map_apply, Matrix.transpose_apply]
  have star_mul : ∀ M N, star (M * N) = star N * star M := by
    intro M N; simp only [star, Matrix.map_mul, Matrix.transpose_mul]
  have star_one : star 1 = 1 := by
    simp only [star]
    rw [Matrix.map_one (⇑φ) (map_zero φ) (map_one φ), Matrix.transpose_one]
  have star_star : ∀ M, star (star M) = M := by
    intro M
    simp only [star]
    rw [Matrix.transpose_map, Matrix.transpose_transpose, Matrix.map_map]
    rw [show (⇑φ ∘ ⇑φ) = id from funext (fun x => hφφ x), Matrix.map_id]
  have star_scalar : ∀ a : F, star (Matrix.scalar (Fin d) a) = Matrix.scalar (Fin d) (φ a) := by
    intro a
    simp only [star]
    rw [kgLangTorAFldAux_map_scalar]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply, Matrix.transpose_apply, eq_comm]
  have star_pow : ∀ M : Matrix (Fin d) (Fin d) F, ∀ k : ℕ, star (M ^ k) = (star M) ^ k := by
    intro M k
    induction k with
    | zero => rw [pow_zero, pow_zero, star_one]
    | succ k ih => rw [pow_succ', star_mul, ih, pow_succ]
  have hmapφ : ∀ M : Matrix (Fin d) (Fin d) F, M.map (· ^ 2 ^ n) = M.map ⇑φ := by
    intro M
    ext i j
    simp only [Matrix.map_apply]
    exact (hφ _).symm
  have heu' : star (e : Matrix (Fin d) (Fin d) F) * (e : Matrix (Fin d) (Fin d) F) = 1 := by
    have h := heu
    rw [hmapφ] at h
    exact h
  have hep' : (e : Matrix (Fin d) (Fin d) F) ^ p = 1 := by
    simpa using congrArg (fun u : GL (Fin d) F => (u : Matrix (Fin d) (Fin d) F)) hep
  let starU : GL (Fin d) F → GL (Fin d) F := fun u =>
    ⟨star (u : Matrix (Fin d) (Fin d) F),
      star ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F),
      by rw [← star_mul, Units.inv_mul, star_one],
      by rw [← star_mul, Units.mul_inv, star_one]⟩
  have hstarU' : ∀ u, (starU u : Matrix (Fin d) (Fin d) F) =
      Matrix.transpose ((u : Matrix (Fin d) (Fin d) F).map ⇑φ) := fun u => rfl
  have hstarU : ∀ u, (starU u : Matrix (Fin d) (Fin d) F) = star (u : Matrix (Fin d) (Fin d) F) :=
    fun u => rfl
  have hstarU_mul : ∀ u v, starU (u * v) = starU v * starU u := by
    intro u v
    apply Units.ext
    rw [hstarU, Units.val_mul, Units.val_mul, hstarU, hstarU, star_mul]
  have hstarU_one : starU 1 = 1 := by
    apply Units.ext
    rw [hstarU, Units.val_one, star_one]
  have hstarU_inv : ∀ u, starU u⁻¹ = (starU u)⁻¹ := by
    intro u
    apply eq_inv_of_mul_eq_one_left
    rw [← hstarU_mul, mul_inv_cancel, hstarU_one]
  have hstarU_star : ∀ u, starU (starU u) = u := by
    intro u
    apply Units.ext
    rw [hstarU, hstarU, star_star]
  have hstarU_pow : ∀ u : GL (Fin d) F, ∀ k : ℕ, starU (u ^ k) = (starU u) ^ k := by
    intro u k
    induction k with
    | zero => rw [pow_zero, pow_zero, hstarU_one]
    | succ k ih => rw [pow_succ', hstarU_mul, ih, pow_succ]
  have hstar_e : star (e : Matrix (Fin d) (Fin d) F) = (e : Matrix (Fin d) (Fin d) F) ^ (p - 1) := by
    have h1 : starU e * e = 1 := by
      apply Units.ext
      rw [Units.val_mul, hstarU]
      exact heu'
    have h2 : e ^ (p - 1) * e = 1 := by
      rw [← pow_succ, Nat.sub_add_cancel hp.one_le, hep]
    have h3 : starU e = e ^ (p - 1) := mul_right_cancel (by rw [h1, h2])
    rw [← hstarU e, h3, Units.val_pow_eq_pow_val]
  have hstar_σ : ∀ M : Matrix (Fin d) (Fin d) F,
      star (M.map (σ : F →+* F)) = (star M).map (σ : F →+* F) := by
    intro M
    ext i j
    simp only [star, Matrix.transpose_apply, Matrix.map_apply]
    exact (hσφ (M j i)).symm
  have hse : (s : Matrix (Fin d) (Fin d) F).map (σ : F →+* F) =
      (s : Matrix (Fin d) (Fin d) F) * (e : Matrix (Fin d) (Fin d) F) := by
    simpa using congrArg (fun u : GL (Fin d) F => (u : Matrix (Fin d) (Fin d) F)) hsσ
  have hstar_poly : ∀ P : Polynomial F, ∃ R : Polynomial F,
      star (Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) P) =
        Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) R := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P Q hP hQ =>
      obtain ⟨RP, hRP⟩ := hP
      obtain ⟨RQ, hRQ⟩ := hQ
      exact ⟨RP + RQ, by rw [Polynomial.aeval_add, star_add, hRP, hRQ, Polynomial.aeval_add]⟩
    | monomial k a =>
      refine ⟨Polynomial.X ^ ((p - 1) * k) * Polynomial.C (φ a), ?_⟩
      rw [Polynomial.aeval_mul, Polynomial.aeval_X_pow, Polynomial.aeval_C]
      rw [Polynomial.aeval_monomial]
      change star (Matrix.scalar (Fin d) a * (e : Matrix (Fin d) (Fin d) F) ^ k) =
        (e : Matrix (Fin d) (Fin d) F) ^ ((p - 1) * k) * Matrix.scalar (Fin d) (φ a)
      rw [star_mul, star_pow, hstar_e, star_scalar, ← pow_mul]
  obtain ⟨Q, hQ⟩ := hstar_poly P
  have hsQ : star (s : Matrix (Fin d) (Fin d) F) =
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) Q := by
    rw [hs, hQ]
  have hM : star (s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F) =
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) (Q * P) := by
    rw [hsQ, hs, Polynomial.aeval_mul]
  have haeval_comm : ∀ R S : Polynomial F,
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) R *
          Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) S =
        Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) S *
          Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) R := by
    intro R S
    rw [← Polynomial.aeval_mul, ← Polynomial.aeval_mul]
    congr 1
    ring
  have hcomm : Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) (Q * P) *
      (e : Matrix (Fin d) (Fin d) F) =
      (e : Matrix (Fin d) (Fin d) F) *
        Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) (Q * P) := by
    simpa using haeval_comm (Q * P) Polynomial.X
  have hσ_h : ((starU s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F)).map
      (σ : F →+* F) = (starU s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F) := by
    have hstep : ((starU s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F)).map
        (σ : F →+* F) = (e : Matrix (Fin d) (Fin d) F) ^ (p - 1) *
          ((starU s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F)) *
          (e : Matrix (Fin d) (Fin d) F) := by
      rw [Matrix.map_mul, hstarU, ← hstar_σ, hse, star_mul, hstar_e]
      simp only [mul_assoc]
    rw [hstep, hstarU, hM, mul_assoc, hcomm, ← mul_assoc, ← pow_succ, Nat.sub_add_cancel hp.one_le,
      hep', one_mul]
  have hpF : ¬ p ∣ Nat.card F := by
    rw [hF]
    intro h
    have h2 : p ∣ 2 ^ n := hp.dvd_of_dvd_pow h
    have h3 : p ∣ 2 := hp.dvd_of_dvd_pow h2
    rcases (Nat.dvd_prime Nat.prime_two).1 h3 with h1 | h2'
    · exact hp.ne_one h1
    · exact hp2 h2'
  set m : ℕ := Nat.card F ^ (p - 1) with hm_def
  have hF5 : ∀ R : Polynomial F,
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) R ^ m =
        Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) R := by
    intro R
    rw [hm_def]
    exact kgLangTorA_aeval_pow_card hp hpF hep' R
  have hcard_ge2 : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hp1 : 1 < p := hp.one_lt
  have hn1 : 1 ≤ n := by
    by_contra h
    have h0 : n = 0 := by omega
    rw [h0] at hF
    have h1 : Nat.card F = 1 := by simpa using hF
    omega
  have hm_ge2 : 2 ≤ m := by
    rw [hm_def]
    calc 2 ≤ Nat.card F ^ 1 := by simpa using hcard_ge2
      _ ≤ Nat.card F ^ (p - 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hm_even : Even m := by
    rw [hm_def]
    have h2n : Nat.card F = 2 ^ (2 * n) := by
      rw [← hcardF]
      exact Nat.card_eq_fintype_card
    rw [h2n, ← pow_mul]
    exact Nat.even_pow.mpr ⟨even_two, Nat.mul_ne_zero (by omega) (by omega)⟩
  have hM_coe : (starU s * s : Matrix (Fin d) (Fin d) F) =
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) (Q * P) := by
    change (starU s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F) =
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) (Q * P)
    rw [hstarU, hM]
  set u : GL (Fin d) F := (starU s * s) ^ (m / 2) with hu_def
  have hu2 : u ^ 2 = starU s * s := by
    apply Units.ext
    rw [hu_def, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← pow_mul,
      Nat.div_two_mul_two_of_even hm_even]
    change (starU s * s : Matrix (Fin d) (Fin d) F) ^ m = (starU s * s : Matrix (Fin d) (Fin d) F)
    rw [hM_coe, hF5]
  set Upoly : Polynomial F := (Q * P) ^ (m / 2) with hUpoly
  have hu_coe : (u : Matrix (Fin d) (Fin d) F) =
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) Upoly := by
    rw [hu_def, Units.val_pow_eq_pow_val]
    change (starU s * s : Matrix (Fin d) (Fin d) F) ^ (m / 2) =
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) Upoly
    rw [hUpoly, hM_coe, ← map_pow]
  have hstarU_u : starU u = u := by
    rw [hu_def, hstarU_pow]
    congr 1
    rw [hstarU_mul, hstarU_star]
  have hstar_u : star (u : Matrix (Fin d) (Fin d) F) = (u : Matrix (Fin d) (Fin d) F) := by
    rw [← hstarU u, hstarU_u]
  have hσ_u : (u : Matrix (Fin d) (Fin d) F).map (σ : F →+* F) =
      (u : Matrix (Fin d) (Fin d) F) := by
    rw [hu_def, Units.val_pow_eq_pow_val, Matrix.map_pow]
    change ((starU s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F)).map
        (σ : F →+* F) ^ (m / 2) =
      ((starU s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F)) ^ (m / 2)
    rw [hσ_h]
  have hu_pow_fix : u ^ m = u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hu_coe]
    exact hF5 Upoly
  have hu_m1 : u ^ (m - 1) = 1 := by
    have h : u ^ (m - 1) * u = u := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m), hu_pow_fix]
    have h' := congrArg (fun x : GL (Fin d) F => x * u⁻¹) h
    simpa [mul_assoc] using h'
  have hu_inv : u⁻¹ = u ^ (m - 2) := by
    have h2 : u ^ (m - 2) * u = 1 := by
      rw [← pow_succ, show m - 2 + 1 = m - 1 by omega, hu_m1]
    exact (eq_inv_of_mul_eq_one_left h2).symm
  set U' : Polynomial F := Upoly ^ (m - 2) with hU'
  have hu_inv_coe : Units.val (u⁻¹) =
      Polynomial.aeval (e : Matrix (Fin d) (Fin d) F) U' := by
    rw [hu_inv, Units.val_pow_eq_pow_val, hu_coe, hU', ← map_pow]
  have hstar_u_inv : star ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) =
      ((u⁻¹ : GL (Fin d) F) : Matrix (Fin d) (Fin d) F) := by
    have h2 : starU u⁻¹ = u⁻¹ := by rw [hstarU_inv, hstarU_u]
    simpa only [hstarU] using
      congrArg (fun x : GL (Fin d) F => (x : Matrix (Fin d) (Fin d) F)) h2
  have hh : star (s : Matrix (Fin d) (Fin d) F) * (s : Matrix (Fin d) (Fin d) F) =
      (u : Matrix (Fin d) (Fin d) F) * (u : Matrix (Fin d) (Fin d) F) := by
    rw [← hstarU s, ← Units.val_mul, ← hu2, Units.val_pow_eq_pow_val, pow_two]
  have he_comm_u : e * u⁻¹ = u⁻¹ * e := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hu_inv_coe]
    simpa using (haeval_comm U' Polynomial.X).symm
  have hσU_u : Matrix.GeneralLinearGroup.map (σ : F →+* F) u = u := by
    apply Units.ext
    simpa using hσ_u
  refine ⟨s * u⁻¹, P * U', ?_, ?_, ?_⟩
  · rw [Units.val_mul, hu_inv_coe, hs, ← Polynomial.aeval_mul]
  · rw [hmapφ, ← hstarU' (s * u⁻¹), ← Units.val_mul]
    have hs' : starU (s * u⁻¹) * (s * u⁻¹) = 1 := by
      rw [hstarU_mul, hstarU_inv, hstarU_u, mul_assoc, ← mul_assoc (starU s) s u⁻¹, ← hu2]
      group
    rw [hs', Units.val_one]
  · rw [map_mul, hsσ, map_inv, hσU_u]
    simp only [mul_assoc]
    rw [he_comm_u]

theorem kgLangTorA_card_fixed_linear {F : Type} [Field F] [Finite F] {n p : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) {σ : F ≃+* F} (hσ : orderOf σ = p) :
    p ∣ n ∧ Nat.card (semilinearFixedSubfield σ) = 2 ^ (n / p) := by
  exact CFSG.SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf
    Nat.prime_two hn hF σ hσ

theorem kgLangTorA_card_fixed_unitary {F : Type} [Field F] [Finite F] {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = (2 ^ n) ^ 2) {σ : F ≃+* F}
    (hσ : orderOf σ = p) :
    p ∣ n ∧ Nat.card (semilinearFixedSubfield σ) = (2 ^ (n / p)) ^ 2 := by
  have hcard : Nat.card F = 2 ^ (2 * n) := by
    rw [hF, ← pow_mul, mul_comm]
  obtain ⟨hdvd, hfix⟩ :=
    CFSG.SignalizerFunctorTheorem.CatalogBridge.card_fixedField_of_orderOf Nat.prime_two
      (by omega : 1 ≤ 2 * n) hcard σ hσ
  have hpn : p ∣ n := by
    rcases (Nat.Prime.dvd_mul hp).1 hdvd with h2 | hn'
    · rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h1 | h2'
      · exact absurd h1 hp.ne_one
      · exact absurd h2' hp2
    · exact hn'
  refine ⟨hpn, ?_⟩
  have hfix' : Nat.card (semilinearFixedSubfield σ) = 2 ^ (2 * n / p) := hfix
  rw [hfix', Nat.mul_div_assoc 2 hpn, ← pow_mul]
  congr 1
  omega

theorem kgLangTorA_pow_eq_on_fixed {F : Type} [Field F] [Finite F] {n p : ℕ} (hn : 1 ≤ n)
    (hp : p.Prime) (hp2 : p ≠ 2) (hF : Nat.card F = (2 ^ n) ^ 2) {σ : F ≃+* F}
    (hσ : orderOf σ = p) (x : semilinearFixedSubfield σ) :
    (x : F) ^ 2 ^ n = (x : F) ^ 2 ^ (n / p) := by
  obtain ⟨hpn, hcard0⟩ := kgLangTorA_card_fixed_unitary hn hp hp2 hF hσ
  set q₀ := 2 ^ (n / p) with hq₀
  haveI : Fintype (semilinearFixedSubfield σ) := Fintype.ofFinite _
  have hcard0' : Fintype.card (semilinearFixedSubfield σ) = q₀ ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hcard0, hq₀]
  have hfixpow : ∀ m : ℕ, ∀ y : semilinearFixedSubfield σ, y ^ ((q₀ ^ 2) ^ m) = y := by
    intro m
    induction m with
    | zero => intro y; rw [pow_zero, pow_one]
    | succ m ih =>
      intro y
      rw [pow_succ, pow_mul, ih, ← hcard0', FiniteField.pow_card]
  have h2n : 2 ^ n = q₀ ^ p := by
    obtain ⟨k, hk⟩ := hpn
    have hk' : n / p = k := by rw [hk, Nat.mul_div_right _ hp.pos]
    rw [hk, hq₀, hk', mul_comm p k, pow_mul]
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hp_eq : p = 2 * ((p - 1) / 2) + 1 := by
    rw [Nat.odd_iff] at hpodd
    omega
  have hqp : q₀ ^ p = q₀ * (q₀ ^ 2) ^ ((p - 1) / 2) := by
    conv_lhs => rw [hp_eq]
    rw [pow_add, pow_mul, pow_one, mul_comm]
  have hxm : (x : F) ^ 2 ^ n = ((x : F) ^ q₀) ^ ((q₀ ^ 2) ^ ((p - 1) / 2)) := by
    rw [h2n, hqp, pow_mul]
  have hy : ((x ^ q₀ : semilinearFixedSubfield σ) : F) = (x : F) ^ q₀ := rfl
  calc (x : F) ^ 2 ^ n
      = ((x : F) ^ q₀) ^ ((q₀ ^ 2) ^ ((p - 1) / 2)) := hxm
    _ = (((x ^ q₀ : semilinearFixedSubfield σ) : F)) ^ ((q₀ ^ 2) ^ ((p - 1) / 2)) := by
          rw [hy]
    _ = (((x ^ q₀ : semilinearFixedSubfield σ) ^ ((q₀ ^ 2) ^ ((p - 1) / 2)) :
          semilinearFixedSubfield σ) : F) := by push_cast; rfl
    _ = ((x ^ q₀ : semilinearFixedSubfield σ) : F) := by
          rw [hfixpow ((p - 1) / 2) (x ^ q₀)]
    _ = (x : F) ^ q₀ := hy
    _ = (x : F) ^ 2 ^ (n / p) := by rw [hq₀]

theorem kgLangTorA_pow_lang {d p : ℕ} {F : Type} [Field F] {σ : F ≃+* F}
    {e s : GL (Fin d) F} (hes : s * e = e * s) (hep : e ^ p = 1)
    (hs : Matrix.GeneralLinearGroup.map (σ : F →+* F) s = s * e) {N : ℕ} (hN : N % p = 1) :
    Matrix.GeneralLinearGroup.map (σ : F →+* F) (s ^ N) = s ^ N * e := by
  have hes' : Commute s e := hes
  rw [map_pow, hs, hes'.mul_pow, pow_eq_pow_mod N hep, hN, pow_one]

end CFSG.StandardType
