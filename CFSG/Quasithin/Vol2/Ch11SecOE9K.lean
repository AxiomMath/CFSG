module

public import CFSG.Quasithin.Vol2.Ch3E213MP6BE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
open CFSG.Quasithin.SteinbergBS (conj_uElt_coords upper_diag_ne_zero minorAut_sq_pow_uElt
  zero_pow_two_pow)
open CFSG.Quasithin.Ch3E213M (IsUpper mem_normalizer_of_isUpper)

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem card_pow_two_pow_eq_mul_le {e : ℕ} (he : 1 ≤ e) (μ : K) :
    Nat.card {b : K // b ^ 2 ^ e = μ * b} ≤ 2 ^ e := by
  classical
  have := Fintype.ofFinite K
  set p : Polynomial K := Polynomial.X ^ 2 ^ e - Polynomial.C μ * Polynomial.X with hp
  have h2 : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
  have hdeg : p.natDegree = 2 ^ e := by
    rw [hp, Polynomial.natDegree_sub_eq_left_of_natDegree_lt] <;>
      rw [Polynomial.natDegree_X_pow]
    exact ((Polynomial.natDegree_C_mul_le μ Polynomial.X).trans
      Polynomial.natDegree_X_le).trans_lt h2
  have hp0 : p ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hdeg
    omega
  have hsub : (Finset.univ.filter fun b : K => b ^ 2 ^ e = μ * b).val ⊆ p.roots := by
    intro b hb
    rw [Finset.mem_val, Finset.mem_filter] at hb
    rw [Polynomial.mem_roots hp0, Polynomial.IsRoot.def, hp]
    simp [hb.2]
  have h := Polynomial.card_le_degree_of_subset_roots hsub
  rw [hdeg] at h
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact h

theorem pow_two_pow_mod (hK : Nat.card K = 2 ^ n) (b : K) (m : ℕ) :
    b ^ 2 ^ m = b ^ 2 ^ (m % n) := by
  have := Fintype.ofFinite K
  have hq : ∀ c : K, c ^ 2 ^ n = c := fun c => by
    rw [← hK, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card c
  have hk : ∀ k : ℕ, b ^ 2 ^ (n * k) = b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hq]
  conv_lhs => rw [← Nat.div_add_mod m n, pow_add, pow_mul, hk]

variable [CharP K 2]

theorem card_le_of_fixed_swap (hK : Nat.card K = 2 ^ n) (hev : Even n) (hn : 1 ≤ n)
    {h : antiSp K} (hh : IsUpper h) (r : ℕ) {A : Subgroup (antiSp K)}
    (hAZ : A ≤ antiUnipotentCenter K)
    (hfix : ∀ z ∈ A, (MulAut.conj h * minorAut K ^ (2 * r + 1)) z = z) :
    Nat.card A ≤ 2 ^ (n - 1) := by
  set M := glMat (h : GL (Fin 4) K) with hM
  obtain ⟨d0, d1, -, -⟩ := upper_diag_ne_zero hh
  set e := (2 * r + 1) % n with he
  have heo : e % 2 = 1 := by
    obtain ⟨m, rfl⟩ := hev
    rw [he, Nat.mod_mod_of_dvd _ ⟨m, by ring⟩]
    omega
  have hen : e < n := Nat.mod_lt _ (by omega)
  set ν := M 0 0 * M 1 1 * (M 0 0 ^ 2) ^ 2 ^ r with hν
  have hν0 : ν ≠ 0 := mul_ne_zero (mul_ne_zero d0 d1) (pow_ne_zero _ (pow_ne_zero _ d0))
  have hcoord : ∀ b c : K, uElt 0 b c 0 ∈ A →
      c = M 0 0 ^ 2 * (b ^ 2 ^ r) ^ 2 ∧ b ^ 2 ^ e = ν⁻¹ * b := by
    intro b c hz
    have h1 := hfix _ hz
    rw [CFSG.Quasithin.Ch3E213M.P6B.sigma_uElt_center hh] at h1
    obtain ⟨-, hb, hc, -⟩ := uElt_inj h1
    refine ⟨hc.symm, ?_⟩
    have h2 : b = ν * b ^ 2 ^ (2 * r + 1) := by
      calc b = M 0 0 * M 1 1 * c ^ 2 ^ r := hb.symm
        _ = M 0 0 * M 1 1 * (M 0 0 ^ 2 * (b ^ 2 ^ r) ^ 2) ^ 2 ^ r := by rw [hc]
        _ = ν * b ^ 2 ^ (2 * r + 1) := by rw [hν]; ring
    rw [pow_two_pow_mod hK b, ← he] at h2
    rw [eq_inv_mul_iff_mul_eq₀ hν0]
    exact h2.symm
  have hmem : ∀ z ∈ A, ∃ b c : K, z = uElt 0 b c 0 := fun z hz => hAZ hz
  let f : ↥A → {b : K // b ^ 2 ^ e = ν⁻¹ * b} := fun z =>
    ⟨glMat ((z : antiSp K) : GL (Fin 4) K) 0 2, by
      obtain ⟨b, c, hz⟩ := hmem z z.2
      have := (hcoord b c (hz ▸ z.2)).2
      rw [hz, glMat_uElt]
      simpa [uMat] using this⟩
  have hf : Function.Injective f := by
    intro z₁ z₂ h12
    obtain ⟨b₁, c₁, hz₁⟩ := hmem z₁ z₁.2
    obtain ⟨b₂, c₂, hz₂⟩ := hmem z₂ z₂.2
    have hb : b₁ = b₂ := by
      have := congrArg Subtype.val h12
      simp only [f, hz₁, hz₂, glMat_uElt] at this
      simpa [uMat] using this
    have hc₁ := (hcoord b₁ c₁ (hz₁ ▸ z₁.2)).1
    have hc₂ := (hcoord b₂ c₂ (hz₂ ▸ z₂.2)).1
    apply Subtype.ext
    rw [hz₁, hz₂, hc₁, hc₂, hb]
  calc Nat.card A ≤ Nat.card {b : K // b ^ 2 ^ e = ν⁻¹ * b} := Nat.card_le_card_of_injective f hf
    _ ≤ 2 ^ e := card_pow_two_pow_eq_mul_le (by omega) _
    _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem exists_not_mem_radA1 (hK : Nat.card K = 2 ^ n) {h : antiSp K} (hh : IsUpper h) {s : ℕ}
    (hs : 1 ≤ s) (hsn : s < n) :
    ∃ x : K, (MulAut.conj h * (minorAut K ^ 2) ^ s) (uElt x 0 0 0) * (uElt x 0 0 0)⁻¹ ∉
      radA1 K := by
  set M := glMat (h : GL (Fin 4) K) with hM
  obtain ⟨d0, d1, -, -⟩ := upper_diag_ne_zero hh
  obtain ⟨x, hx⟩ : ∃ x : K, M 0 0 * x ^ 2 ^ s ≠ x * M 1 1 := by
    by_contra hc
    push Not at hc
    have h1 := hc 1
    rw [one_pow, mul_one, one_mul] at h1
    have hall : ∀ y : K, y ^ 2 ^ s = 1 * y := fun y => by
      have h2 := hc y
      rw [h1] at h2
      rw [one_mul]
      exact mul_left_cancel₀ d1 (h2.trans (mul_comm y _))
    have hcard := card_pow_two_pow_eq_mul_le (K := K) hs 1
    rw [Nat.card_congr (Equiv.subtypeUnivEquiv hall), hK] at hcard
    have := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hsn
    omega
  have himg : (MulAut.conj h * (minorAut K ^ 2) ^ s) (uElt x 0 0 0) =
      h * uElt (x ^ 2 ^ s) 0 0 0 * h⁻¹ := by
    rw [MulAut.mul_apply, minorAut_sq_pow_uElt, zero_pow_two_pow, MulAut.conj_apply]
  obtain ⟨a', b', c', d', he⟩ :=
    (Subgroup.mem_normalizer_iff.mp (mem_normalizer_of_isUpper hh) _).mp
      (uElt_mem_antiUnipotent (x ^ 2 ^ s) 0 0 0)
  obtain ⟨e1, -⟩ := conj_uElt_coords hh he
  refine ⟨x, fun hmem => hx ?_⟩
  rw [himg, he] at hmem
  obtain ⟨B, C, D, hBCD⟩ := hmem
  rw [uElt_inv, uElt_mul] at hBCD
  obtain ⟨hA, -⟩ := uElt_inj hBCD
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have ha : a' = x := by linear_combination hA - x * h2
  rw [← ha] at e1 ⊢
  exact e1.symm

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3.Sp4
