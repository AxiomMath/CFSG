module

public import CFSG.Permutation.UnitaryThreeRecognition.ModelBasic

public section

namespace CFSG.UnitaryThreeRecognition.WeylAlg

open CFSG.BenderSuzuki.MatrixGroups

theorem sq_eq_one_of_involutive {H : Type*} [CommGroup H] {q : ℕ} (hq : 1 ≤ q)
    (hexp : ∀ x : H, x ^ (q * q) = x) (σ : H →* H) (hσσ : ∀ x, σ (σ x) = x)
    (hfix : ∀ x, σ x = x ↔ x ^ (q + 1) = 1) (x : H) : (σ x * x ^ q) ^ 2 = 1 := by
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
  have hx1 : x ^ (r * (r + 2)) = 1 := by
    have h := hexp x
    have e : (r + 1) * (r + 1) = r * (r + 2) + 1 := by ring
    rw [e, pow_succ] at h
    exact mul_eq_right.mp h
  have hw : (x * σ x) ^ (r + 2) = 1 := by
    have : σ (x * σ x) = x * σ x := by rw [map_mul, hσσ, mul_comm]
    exact (hfix _).mp this
  have hrw : σ x * x ^ (r + 1) = x * σ x * x ^ r := by
    rw [pow_succ, mul_comm (x ^ r) x, ← mul_assoc, mul_comm (σ x) x]
  have he1 : (σ x * x ^ (r + 1)) ^ (r + 2) = 1 := by
    rw [hrw, mul_pow, hw, one_mul, ← pow_mul, hx1]
  have hσe : σ (σ x * x ^ (r + 1)) = σ x * x ^ (r + 1) := (hfix _).mpr he1
  have h1 : x * σ x ^ (r + 1) = σ x * x ^ (r + 1) := by
    rw [map_mul, hσσ, map_pow] at hσe
    exact hσe
  have h2 : σ x ^ r = x ^ r := by
    have h3 : x * σ x * σ x ^ r = x * σ x * x ^ r := by
      calc x * σ x * σ x ^ r = x * σ x ^ (r + 1) := by rw [pow_succ', mul_assoc]
        _ = σ x * x ^ (r + 1) := h1
        _ = x * σ x * x ^ r := hrw
    exact mul_left_cancel h3
  have he2 : (σ x * x ^ (r + 1)) ^ r = 1 := by
    rw [mul_pow, h2, ← pow_mul, ← pow_add]
    rw [show r + (r + 1) * r = r * (r + 2) by ring, hx1]
  calc (σ x * x ^ (r + 1)) ^ 2 = (σ x * x ^ (r + 1)) ^ r * (σ x * x ^ (r + 1)) ^ 2 := by
        rw [he2, one_mul]
    _ = (σ x * x ^ (r + 1)) ^ (r + 2) := (pow_add _ r 2).symm
    _ = 1 := he1

variable {K : Type*} [Field K] (J : HermitianForm 3 K)

@[expose] def nrm (x : K) : K := x * J.conj x

theorem nrm_def (x : K) : nrm J x = x * J.conj x := rfl

theorem conj_nrm (x : K) : J.conj (nrm J x) = nrm J x := by
  rw [nrm_def, map_mul, Model.conj_conj, mul_comm]

theorem nrm_mul (x y : K) : nrm J (x * y) = nrm J x * nrm J y := by
  simp only [nrm_def, map_mul]; ring

theorem nrm_ne_zero {x : K} (hx : x ≠ 0) : nrm J x ≠ 0 :=
  mul_ne_zero hx ((map_ne_zero J.conj).2 hx)

theorem nrm_inv (x : K) : nrm J x⁻¹ = (nrm J x)⁻¹ := by
  simp only [nrm_def, map_inv₀, mul_inv]

section Finite

variable [Finite K] {q : ℕ} (hK : Nat.card K = q ^ 2) (hconj : ∀ x, J.conj x = x ^ q)
include hK hconj

omit hconj in
theorem units_pow_sq (k : Kˣ) : k ^ (q * q) = k := by
  have : Fintype K := Fintype.ofFinite K
  have h := FiniteField.pow_card (k : K)
  rw [← Nat.card_eq_fintype_card, hK, sq] at h
  exact Units.ext (by simpa using h)

omit [Finite K] hK in
theorem nrm_eq_pow (x : K) : nrm J x = x ^ (q + 1) := by
  rw [nrm_def, hconj, pow_succ, mul_comm]

theorem exists_units_nrm_eq (hq : 1 ≤ q) {y : K} (hy : y ≠ 0) (hyc : J.conj y = y) :
    ∃ k : Kˣ, nrm J k = y := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hqq : q * q - 1 = (q - 1) * (q + 1) := by
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    rw [show (r + 1) * (r + 1) = r * (r + 2) + 1 by ring, Nat.add_sub_cancel,
      Nat.add_sub_cancel]
  have hcardK : Fintype.card Kˣ = q * q - 1 := by
    rw [Fintype.card_units, ← Nat.card_eq_fintype_card, hK, sq]
  have hog : orderOf g = q * q - 1 := by
    rw [← hcardK, ← Nat.card_eq_fintype_card]; exact orderOf_eq_card_of_forall_mem_zpowers hg
  set u := Units.mk0 y hy
  obtain ⟨i, hi⟩ : ∃ i : ℕ, g ^ i = u := by
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg u)
    have hpos : (0 : ℤ) < ((q * q - 1 : ℕ) : ℤ) := by
      have h1 : 1 < q * q := by
        have : 1 < Nat.card K := Finite.one_lt_card
        rw [hK, sq] at this; exact this
      exact_mod_cast (by omega : 0 < q * q - 1)
    refine ⟨(n % (q * q - 1 : ℕ)).toNat, ?_⟩
    rw [← hn, ← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ hpos.ne'), ← hog,
      zpow_mod_orderOf]
  have hu : u ^ (q - 1) = 1 := by
    apply Units.ext
    have h1 : y ^ q = y := by rw [← hconj, hyc]
    have h2 : y ^ (q - 1) * y = y := by rw [← pow_succ, Nat.sub_add_cancel hq, h1]
    simp only [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, u]
    exact (mul_eq_right₀ hy).mp h2
  have hdvd : q + 1 ∣ i := by
    have hu' : g ^ (i * (q - 1)) = 1 := by rw [pow_mul, hi, hu]
    have h3 : (q - 1) * (q + 1) ∣ i * (q - 1) := by
      rw [← hqq, ← hog]
      exact orderOf_dvd_of_pow_eq_one hu'
    rcases Nat.eq_or_lt_of_le hq with hq1 | hpos
    · exfalso
      rw [← hq1] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · rw [mul_comm i] at h3
      exact Nat.dvd_of_mul_dvd_mul_left (by omega) h3
  obtain ⟨m, rfl⟩ := hdvd
  refine ⟨g ^ m, ?_⟩
  rw [nrm_eq_pow J hconj, ← Units.val_pow_eq_pow_val, ← pow_mul, mul_comm m, hi]
  rfl

end Finite

end CFSG.UnitaryThreeRecognition.WeylAlg
