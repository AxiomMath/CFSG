module

public import CFSG.LocalAnalysis.UniquenessCase.UCInspL3Cyc
public import Mathlib.FieldTheory.Finite.Extension

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.Insp

open Matrix
open scoped MatrixGroups

section Field3

variable (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime] [CharP K p]

abbrev L3 : Type := FiniteField.Extension K p 3

@[expose] noncomputable def bL : Module.Basis (Fin 3) K (L3 K p) :=
  Module.finBasisOfFinrankEq K (L3 K p) (FiniteField.finrank_extension K p 3)

@[expose] noncomputable def TL : Module.End K (L3 K p) ≃ₐ[K] Matrix (Fin 3) (Fin 3) K :=
  LinearMap.toMatrixAlgEquiv (bL K p)

@[expose] noncomputable def frobL : Module.End K (L3 K p) :=
  (FiniteField.Extension.frob K p 3 : L3 K p ≃ₐ[K] L3 K p).toLinearMap

@[expose] noncomputable def mulL (w : L3 K p) : Module.End K (L3 K p) := Algebra.lmul K (L3 K p) w

variable {K p}

theorem frobL_apply (x : L3 K p) : frobL K p x = x ^ Nat.card K := by
  simp [frobL]

theorem mulL_one : mulL K p 1 = 1 := map_one (Algebra.lmul K (L3 K p))

theorem mulL_pow (w : L3 K p) (n : ℕ) : mulL K p (w ^ n) = mulL K p w ^ n :=
  map_pow (Algebra.lmul K (L3 K p)) w n

theorem mulL_eq_one_iff (w : L3 K p) : mulL K p w = 1 ↔ w = 1 := by
  constructor
  · intro h
    have := LinearMap.congr_fun h 1
    simpa [mulL] using this
  · rintro rfl
    exact mulL_one

theorem frobL_mulL (w : L3 K p) :
    frobL K p * mulL K p w = mulL K p (w ^ Nat.card K) * frobL K p := by
  ext x
  simp [frobL_apply, mulL, mul_pow]

theorem frobL_cube : frobL K p * frobL K p * frobL K p = 1 := by
  have h : (FiniteField.Extension.frob K p 3) ^ 3 = 1 := by
    have := pow_card_eq_one' (G := (L3 K p ≃ₐ[K] L3 K p))
      (x := FiniteField.Extension.frob K p 3)
    rwa [FiniteField.natCard_algEquiv_extension] at this
  ext x
  have hx := congrArg (fun g : L3 K p ≃ₐ[K] L3 K p => g x) h
  simpa [pow_succ, frobL, AlgEquiv.mul_apply] using hx

theorem frob_ne_one : FiniteField.Extension.frob K p 3 ≠ 1 := by
  intro h
  have hall : ∀ g : L3 K p ≃ₐ[K] L3 K p, g = 1 := fun g => by
    obtain ⟨i, -, hi⟩ := FiniteField.Extension.exists_frob_pow_eq K p 3 g
    rw [← hi, h, one_pow]
  haveI : Subsingleton (L3 K p ≃ₐ[K] L3 K p) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  have h1 := Nat.card_of_subsingleton (1 : L3 K p ≃ₐ[K] L3 K p)
  have h3 := FiniteField.natCard_algEquiv_extension K p 3
  have h13 : (1 : ℕ) = 3 := h1.symm.trans h3
  omega

theorem frobL_ne_scalar (c : K) : frobL K p ≠ c • (1 : Module.End K (L3 K p)) := by
  intro h
  have h1 := LinearMap.congr_fun h 1
  simp only [frobL_apply, one_pow, LinearMap.smul_apply, Module.End.one_apply] at h1
  have hc : c = 1 := by
    have h2 : algebraMap K (L3 K p) c = algebraMap K (L3 K p) 1 := by
      rw [map_one]
      simpa [Algebra.smul_def] using h1.symm
    exact (algebraMap K (L3 K p)).injective h2
  apply frob_ne_one (K := K) (p := p)
  ext x
  have := LinearMap.congr_fun h x
  rw [hc] at this
  simpa [frobL_apply] using this

end Field3

section Arith

theorem exists_prime_dvd_singer (q : ℕ) (hq2 : 2 ≤ q) (hq3 : q % 3 = 2) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ q ^ 2 + q + 1 ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ ¬ ℓ ∣ q - 1 := by
  have hn : q ^ 2 + q + 1 ≠ 1 := by nlinarith
  obtain ⟨ℓ, hℓ, hdvd⟩ := Nat.exists_prime_and_dvd hn
  have hodd : (q ^ 2 + q + 1) % 2 = 1 := by
    rcases Nat.even_or_odd q with h | h
    · obtain ⟨k, rfl⟩ := h
      ring_nf
      omega
    · obtain ⟨k, rfl⟩ := h
      ring_nf
      omega
  have hmod3 : (q ^ 2 + q + 1) % 3 = 1 := by
    simp [Nat.add_mod, Nat.pow_mod, hq3]
  refine ⟨ℓ, hℓ, hdvd, ?_, ?_, ?_⟩
  · rintro rfl
    omega
  · rintro rfl
    omega
  · intro h
    have e : q ^ 2 + q + 1 = (q - 1) * (q + 2) + 3 := by
      obtain ⟨k, rfl⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      ring
    have h3 : ℓ ∣ 3 := by
      have := (Nat.dvd_add_right (dvd_mul_of_dvd_left h (q + 2))).1 (e ▸ hdvd)
      exact this
    have hℓ3 : ℓ = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3
    rw [hℓ3] at hdvd
    omega

end Arith

section KFacts

variable {K : Type} [Field K] [Finite K]

theorem cube_roots_trivial (hq : Nat.card K % 3 = 2) : ∀ c : K, c ^ 3 = 1 → c = 1 := by
  intro c hc
  have hc0 : c ≠ 0 := fun h => by simp [h] at hc
  let u : Kˣ := Units.mk0 c hc0
  have hu : u ^ 3 = 1 := Units.ext (by simp [u, hc])
  have hord : orderOf u ∣ 3 := orderOf_dvd_of_pow_eq_one hu
  have hord2 : orderOf u ∣ Nat.card K - 1 := by
    rw [← Nat.card_units]
    exact orderOf_dvd_natCard u
  have hcop : Nat.Coprime 3 (Nat.card K - 1) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 (by omega)
  have h1 : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop hord hord2
  exact congrArg Units.val (orderOf_eq_one_iff.1 h1)

theorem no_root_of_cube_trivial (h3 : (3 : K) ≠ 0) (hcube : ∀ c : K, c ^ 3 = 1 → c = 1) :
    ∀ c : K, c ^ 2 + c + 1 ≠ 0 := by
  intro c hc
  have h1 : c ^ 3 = 1 := by linear_combination (c - 1) * hc
  have h2 : c = 1 := hcube c h1
  rw [h2] at hc
  apply h3
  linear_combination hc

end KFacts

section Model

variable {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]

theorem three_ne_zero_of_card_mod {f : ℕ} (hf : 1 ≤ f) (hpf : Nat.card K = p ^ f)
    (hq : Nat.card K % 3 = 2) : (3 : K) ≠ 0 := by
  intro h
  have h' : ((3 : ℕ) : K) = 0 := by simpa using h
  have hdvd : p ∣ 3 := (CharP.cast_eq_zero_iff K p 3).1 h'
  have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_three).1 hdvd
  rw [hpf, hp3] at hq
  have : 3 ∣ 3 ^ f := dvd_pow_self 3 (by omega)
  omega

theorem exists_model_L {f : ℕ} (hf : 1 ≤ f) (hpf : Nat.card K = p ^ f)
    (hq : Nat.card K % 3 = 2) :
    ∃ (ℓ : ℕ) (b z : SL(3, K)), ℓ.Prime ∧ ℓ ≠ 2 ∧ ℓ ≠ 3 ∧ ¬ ℓ ∣ Nat.card K - 1 ∧
      b ^ 3 = 1 ∧ (∀ c : K, (b : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) ∧
      z ^ ℓ = 1 ∧ z ≠ 1 ∧ b * z * b⁻¹ = z ^ Nat.card K := by
  have hcube := cube_roots_trivial hq
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card_mod hf hpf hq
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  obtain ⟨ℓ, hℓ, hℓdvd, hℓ2, hℓ3, hℓq⟩ := exists_prime_dvd_singer (Nat.card K) hq2 hq
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hcardL : Nat.card (L3 K p) = Nat.card K ^ 3 := FiniteField.natCard_extension K p 3
  have hdvdL : ℓ ∣ Nat.card (L3 K p)ˣ := by
    rw [Nat.card_units, hcardL]
    have e : Nat.card K ^ 3 - 1 = (Nat.card K - 1) * (Nat.card K ^ 2 + Nat.card K + 1) := by
      obtain ⟨k, hk⟩ : ∃ k, Nat.card K = k + 1 := ⟨Nat.card K - 1, by omega⟩
      rw [hk]
      simp only [Nat.add_sub_cancel]
      ring_nf
      omega
    rw [e]
    exact dvd_mul_of_dvd_right hℓdvd _
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := (L3 K p)ˣ) ℓ hdvdL
  have hwpow : (w : L3 K p) ^ ℓ = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← hw, pow_orderOf_eq_one, Units.val_one]
  have hw1 : (w : L3 K p) ≠ 1 := by
    intro h
    have : w = 1 := Units.ext h
    rw [this, orderOf_one] at hw
    exact hℓ.one_lt.ne hw
  set Φ : Matrix (Fin 3) (Fin 3) K := TL K p (frobL K p) with hΦ
  have hΦ3 : Φ * Φ * Φ = 1 := by
    rw [hΦ, ← map_mul, ← map_mul, frobL_cube, map_one]
  have hΦdet : Φ.det = 1 := by
    have h1 : Φ.det ^ 3 = 1 := by
      rw [← Matrix.det_pow, pow_succ, pow_two, hΦ3, Matrix.det_one]
    exact hcube _ h1
  have hΦns : ∀ c : K, Φ ≠ c • (1 : Matrix (Fin 3) (Fin 3) K) := by
    intro c hc
    apply frobL_ne_scalar c
    apply (TL K p).injective
    rw [← hΦ, hc, map_smul, map_one]
  set Z : Matrix (Fin 3) (Fin 3) K := TL K p (mulL K p (w : L3 K p)) with hZ
  have hZℓ : Z ^ ℓ = 1 := by
    rw [hZ, ← map_pow, ← mulL_pow, hwpow, mulL_one, map_one]
  have hZdet : Z.det = 1 := by
    have h1 : Z.det ^ ℓ = 1 := by rw [← Matrix.det_pow, hZℓ, Matrix.det_one]
    have hne : Z.det ≠ 0 := fun h0 => by rw [h0, zero_pow hℓ.ne_zero] at h1; exact zero_ne_one h1
    let u : Kˣ := Units.mk0 _ hne
    have hu : u ^ ℓ = 1 := Units.ext (by simp [u, h1])
    have hord : orderOf u ∣ ℓ := orderOf_dvd_of_pow_eq_one hu
    have hord2 : orderOf u ∣ Nat.card K - 1 := by
      rw [← Nat.card_units]
      exact orderOf_dvd_natCard u
    have hcop : Nat.Coprime ℓ (Nat.card K - 1) := (Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓq
    have h1' : orderOf u = 1 := Nat.eq_one_of_dvd_coprimes hcop hord hord2
    exact congrArg Units.val (orderOf_eq_one_iff.1 h1')
  have hZne : Z ≠ 1 := by
    intro h
    apply hw1
    rw [← mulL_eq_one_iff (K := K) (p := p)]
    apply (TL K p).injective
    rw [← hZ, h, map_one]
  have hrel : Φ * Z = Z ^ Nat.card K * Φ := by
    rw [hΦ, hZ, ← map_pow, ← mulL_pow, ← map_mul, ← map_mul, frobL_mulL]
  obtain ⟨b, hb⟩ : ∃ b : SL(3, K), (b : Matrix (Fin 3) (Fin 3) K) = Φ := ⟨⟨Φ, hΦdet⟩, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : SL(3, K), (z : Matrix (Fin 3) (Fin 3) K) = Z := ⟨⟨Z, hZdet⟩, rfl⟩
  refine ⟨ℓ, b, z, hℓ, hℓ2, hℓ3, hℓq, ?_, by rw [hb]; exact hΦns, ?_, ?_, ?_⟩
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hb, Matrix.SpecialLinearGroup.coe_one, pow_succ,
      pow_two, hΦ3]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_pow, hz, Matrix.SpecialLinearGroup.coe_one]
    exact hZℓ
  · intro h
    apply hZne
    rw [← hz, h]
    rfl
  · rw [mul_inv_eq_iff_eq_mul]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_pow, hb, hz]
    exact hrel

end Model

end CFSG.LocalAnalysis.UniquenessCase.UCK.Insp
