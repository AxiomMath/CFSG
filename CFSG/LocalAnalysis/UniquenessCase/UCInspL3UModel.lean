module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Field
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UHerm
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3UNorm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix CFSG.LieType.Universal.Unitary
open scoped MatrixGroups

section Arith

theorem exists_prime_dvd_coxeter (Q : ℕ) (hQ2 : 2 ≤ Q) (hQ3 : Q % 3 = 1) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ Q ^ 3 + 1 ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ ¬ ℓ ∣ Q - 1 ∧ ¬ ℓ ∣ Q + 1 := by
  set m := Q * (Q - 1) + 1 with hm
  have hn : m ≠ 1 := by
    have h2 : 2 ≤ Q * (Q - 1) := by
      have h1 : 1 ≤ Q - 1 := by omega
      nlinarith
    omega
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hn
  have hodd : m % 2 = 1 := by
    obtain ⟨k, hk⟩ := Nat.even_mul_pred_self Q
    omega
  have hmod3 : m % 3 = 1 := by
    simp [hm, Nat.add_mod, Nat.mul_mod, hQ3, show (Q - 1) % 3 = 0 by omega]
  have hcube : Q ^ 3 + 1 = (Q + 1) * m := by
    obtain ⟨k, rfl⟩ : ∃ k, Q = k + 1 := ⟨Q - 1, by omega⟩
    simp only [hm, Nat.add_sub_cancel]
    ring
  have hsq : m = (Q + 1) * (Q - 2) + 3 := by
    obtain ⟨k, rfl⟩ : ∃ k, Q = k + 2 := ⟨Q - 2, by omega⟩
    simp only [hm]
    rw [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
    ring
  have h2 : ℓ ≠ 2 := by
    rintro rfl
    omega
  have h3 : ℓ ≠ 3 := by
    rintro rfl
    omega
  refine ⟨ℓ, hℓ, ?_, h2, h3, ?_, ?_⟩
  · rw [hcube]
    exact dvd_mul_of_dvd_right hdvd _
  · intro h
    have h1 : ℓ ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_right h Q)).1 hdvd
    exact hℓ.not_dvd_one h1
  · intro h
    have h3' : ℓ ∣ 3 := by
      rw [hsq] at hdvd
      exact (Nat.dvd_add_right (dvd_mul_of_dvd_left h _)).1 hdvd
    exact h3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3')

end Arith

section Field

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

instance instCharPL3 : CharP (L3 K p) p :=
  charP_of_injective_algebraMap (algebraMap K (L3 K p)).injective p

variable (K p) (f : ℕ)

@[expose] noncomputable def betaL : L3 K p ≃+* L3 K p :=
  iterateFrobeniusEquiv (L3 K p) p (3 * f)

variable {K p f}

theorem betaL_apply (x : L3 K p) : betaL K p f x = x ^ (p ^ f) ^ 3 := by
  show x ^ p ^ (3 * f) = _
  rw [pow_mul']

theorem betaL_algebraMap (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ p ^ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (c : K) :
    betaL K p f (algebraMap K (L3 K p) c) = algebraMap K (L3 K p) (σ c) := by
  rw [betaL_apply, ← map_pow, hσ]
  congr 1
  have hpc : c ^ (p ^ f) ^ 2 = c := by
    haveI := Fintype.ofFinite K
    rw [← hK, Nat.card_eq_fintype_card, FiniteField.pow_card]
  calc c ^ (p ^ f) ^ 3 = c ^ ((p ^ f) ^ 2 * p ^ f) := by rw [pow_succ]
    _ = (c ^ (p ^ f) ^ 2) ^ p ^ f := by rw [pow_mul]
    _ = c ^ p ^ f := by rw [hpc]

theorem betaL_betaL (hK : Nat.card K = (p ^ f) ^ 2) (x : L3 K p) :
    betaL K p f (betaL K p f x) = x := by
  haveI := Fintype.ofFinite (L3 K p)
  rw [betaL_apply, betaL_apply, ← pow_mul]
  have e : (p ^ f) ^ 3 * (p ^ f) ^ 3 = Nat.card (L3 K p) := by
    rw [FiniteField.natCard_extension, hK]
    ring
  rw [e, Nat.card_eq_fintype_card, FiniteField.pow_card]

theorem exists_model_U (σ : K ≃+* K) (hσ : ∀ c : K, σ c = c ^ p ^ f)
    (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f % 3 = 1) :
    ∃ (ℓ : ℕ) (S Φ Z : Matrix (Fin 3) (Fin 3) K), ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧
      ¬ ℓ ∣ Nat.card K - 1 ∧ conjTr σ S = S ∧ S.det ≠ 0 ∧
      conjTr σ Φ * S * Φ = S ∧ Φ * Φ * Φ = 1 ∧ Φ.det = 1 ∧
      (∀ c : K, Φ ≠ c • (1 : Matrix (Fin 3) (Fin 3) K)) ∧
      conjTr σ Z * S * Z = S ∧ Z ^ ℓ = 1 ∧ Z ≠ 1 ∧ Z.det = 1 ∧ Φ * Z = Z ^ Nat.card K * Φ := by
  set Q := p ^ f with hQdef
  have hQ2 : 2 ≤ Q := two_le_of_card_eq_sq hK
  obtain ⟨ℓ, hℓ, hℓ3Q, hℓ2, hℓ3, hℓQ1, hℓQ2⟩ := exists_prime_dvd_coxeter Q hQ2 hq
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓN : ¬ ℓ ∣ Nat.card K - 1 := by
    rw [hK]
    have e : Q ^ 2 - 1 = (Q - 1) * (Q + 1) := by
      have h1Q : 1 ≤ Q := by omega
      have h1Q2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1Q, h1Q2]
      ring
    rw [e]
    intro h
    rcases (Nat.Prime.dvd_mul hℓ).1 h with h | h
    exacts [hℓQ1 h, hℓQ2 h]
  have hβK := betaL_algebraMap σ hσ hK
  have hββ := betaL_betaL hK
  set β : L3 K p ≃+* L3 K p := betaL K p f with hβdef
  have hcardL : Nat.card (L3 K p) = (Q ^ 2) ^ 3 := by
    rw [FiniteField.natCard_extension, hK]
  have hdvdL : ℓ ∣ Nat.card (L3 K p)ˣ := by
    rw [Nat.card_units, hcardL]
    have e : (Q ^ 2) ^ 3 - 1 = (Q ^ 3 - 1) * (Q ^ 3 + 1) := by
      have h1 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
      have h2 : 1 ≤ (Q ^ 2) ^ 3 := Nat.one_le_pow _ _ (by positivity)
      zify [h1, h2]
      ring
    rw [e]
    exact dvd_mul_of_dvd_right hℓ3Q _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := (L3 K p)ˣ) ℓ hdvdL
  have hwpow : (w : L3 K p) ^ ℓ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hw, pow_orderOf_eq_one, Units.val_one]
  have hw1 : (w : L3 K p) ≠ 1 := by
    intro h
    have : w = 1 := Units.ext h
    rw [this, orderOf_one] at hw
    exact hℓ.one_lt.ne hw
  have hβw : β (w : L3 K p) * (w : L3 K p) = 1 := by
    rw [hβdef, betaL_apply, ← pow_succ]
    obtain ⟨k, hk⟩ := hℓ3Q
    rw [hk, pow_mul, hwpow, one_pow]
  have hΦiso : ∀ x y : L3 K p, hermForm σ β hβK (frobL K p x) (frobL K p y) =
      hermForm σ β hβK x y := by
    intro x y
    rw [hermForm_apply, hermForm_apply, frobL_apply, frobL_apply, map_pow, ← mul_pow]
    have := Algebra.trace_eq_of_algEquiv (FiniteField.Extension.frob K p 3) (β x * y)
    rw [FiniteField.Extension.frob_apply] at this
    exact this
  have hZiso : ∀ x y : L3 K p, hermForm σ β hβK (mulL K p (w : L3 K p) x)
      (mulL K p (w : L3 K p) y) = hermForm σ β hβK x y := by
    intro x y
    have hx : ∀ z : L3 K p, mulL K p (w : L3 K p) z = (w : L3 K p) * z := fun z => rfl
    rw [hx, hx, hermForm_apply, hermForm_apply, map_mul β]
    calc Algebra.trace K (L3 K p) (β (w : L3 K p) * β x * ((w : L3 K p) * y))
        = Algebra.trace K (L3 K p) ((β (w : L3 K p) * (w : L3 K p)) * (β x * y)) := by
          congr 1
          ring
      _ = Algebra.trace K (L3 K p) (β x * y) := by rw [hβw, one_mul]
  set S : Matrix (Fin 3) (Fin 3) K := gram σ hβK (bL K p) with hS
  have hSherm : conjTr σ S = S := conjTr_gram σ hβK (bL K p) hββ
  have hSdet : S.det ≠ 0 := det_gram_ne_zero σ hβK (bL K p) hββ
  set Φ : Matrix (Fin 3) (Fin 3) K := TL K p (frobL K p) with hΦ
  set Z : Matrix (Fin 3) (Fin 3) K := TL K p (mulL K p (w : L3 K p)) with hZ
  have hΦS : conjTr σ Φ * S * Φ = S := conjTr_mul_gram_mul σ hβK (bL K p) (frobL K p) hΦiso
  have hZS : conjTr σ Z * S * Z = S :=
    conjTr_mul_gram_mul σ hβK (bL K p) (mulL K p (w : L3 K p)) hZiso
  have hΦ3 : Φ * Φ * Φ = 1 := by
    rw [hΦ, ← map_mul, ← map_mul, frobL_cube, map_one]
  have hΦns : ∀ c : K, Φ ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hc
    apply frobL_ne_scalar c
    apply (TL K p).injective
    rw [← hΦ, hc, map_smul, map_one]
  have hΦdet : Φ.det = 1 := by
    have h1 : Φ.det ^ 3 = 1 := by
      rw [← Matrix.det_pow, pow_succ, pow_two, hΦ3, Matrix.det_one]
    have hcop : Nat.Coprime 3 (Q + 1) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
    exact det_eq_one_of_isometry σ hSdet hΦS hσ h1 hcop
  have hZℓ : Z ^ ℓ = 1 := by
    rw [hZ, ← map_pow, ← mulL_pow, hwpow, mulL_one, map_one]
  have hZdet : Z.det = 1 := by
    have h1 : Z.det ^ ℓ = 1 := by rw [← Matrix.det_pow, hZℓ, Matrix.det_one]
    have hcop : Nat.Coprime ℓ (Q + 1) := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓQ2
    exact det_eq_one_of_isometry σ hSdet hZS hσ h1 hcop
  have hZne : Z ≠ 1 := by
    intro h
    apply hw1
    rw [← mulL_eq_one_iff (K := K) (p := p)]
    apply (TL K p).injective
    rw [← hZ, h, map_one]
  have hrel : Φ * Z = Z ^ Nat.card K * Φ := by
    rw [hΦ, hZ, ← map_pow, ← mulL_pow, ← map_mul, ← map_mul, frobL_mulL]
  exact ⟨ℓ, S, Φ, Z, hℓ, hℓ2, hℓ3, hℓN, hSherm, hSdet, hΦS, hΦ3, hΦdet, hΦns, hZS, hZℓ, hZne,
    hZdet, hrel⟩

end Field

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
