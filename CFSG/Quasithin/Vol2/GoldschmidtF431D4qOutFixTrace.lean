module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qOutFixField

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.Chevalley

variable {K : Type} [Field K] [Finite K] {σ δ : K ≃+* K} {e : ℕ} (he : 1 ≤ e)
  (hK : Nat.card K = 2 ^ (6 * e)) (hσ : ∀ c, σ c = c ^ 2 ^ (2 * e))
  (hδ : ∀ c, δ c = c ^ 2 ^ (3 * e))

omit [Finite K] in
include hσ hδ in
theorem trace_eq_of_fix {s : K} (hs : δ s = s) :
    s + σ s + σ (σ s) = s ^ 2 ^ (2 * e) + s ^ 2 ^ e + s := by
  have h3 : s ^ 2 ^ (3 * e) = s := by rw [← hδ, hs]
  have h4 : σ (σ s) = s ^ 2 ^ e := by
    rw [hσ, hσ, ← pow_mul, ← pow_add]
    calc s ^ 2 ^ (2 * e + 2 * e) = (s ^ 2 ^ (3 * e)) ^ 2 ^ e := by
          rw [← pow_mul, ← pow_add]
          ring_nf
      _ = s ^ 2 ^ e := by rw [h3]
  rw [h4, hσ]
  ring

include he hK hσ hδ in
theorem exists_trace_one : ∃ s : K, δ s = s ∧ s + σ s + σ (σ s) = 1 := by
  classical
  have hK6 := hK
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK6
  have : Fintype K := Fintype.ofFinite K
  have hnz : ∃ s : K, δ s = s ∧ s + σ s + σ (σ s) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    let P : Polynomial K := Polynomial.X ^ 2 ^ (2 * e) + Polynomial.X ^ 2 ^ e + Polynomial.X
    have hlt1 : 2 ^ e < 2 ^ (2 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hlt2 : 1 < 2 ^ e := Nat.one_lt_two_pow (by omega)
    have hP0 : P ≠ 0 := by
      intro h0
      have h1 := congrArg (fun p : Polynomial K => p.coeff 1) h0
      have n1 : (1 : ℕ) ≠ 2 ^ (2 * e) := by omega
      have n2 : (1 : ℕ) ≠ 2 ^ e := by omega
      simp [P, Polynomial.coeff_X_pow, n1, n2] at h1
    have hdeg : P.natDegree ≤ 2 ^ (2 * e) := by
      refine (Polynomial.natDegree_add_le _ _).trans (max_le
        ((Polynomial.natDegree_add_le _ _).trans
          (max_le (by rw [Polynomial.natDegree_X_pow])
            (by rw [Polynomial.natDegree_X_pow]; omega))) ?_)
      exact Polynomial.natDegree_X_le.trans (by omega)
    have hsub : (Finset.univ.filter fun s : K => δ s = s) ⊆ P.roots.toFinset := by
      intro s hs
      rw [Finset.mem_filter] at hs
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0]
      have h := trace_eq_of_fix hσ hδ hs.2
      have h2 := hcon s hs.2
      simp only [Polynomial.IsRoot, P, Polynomial.eval_add, Polynomial.eval_pow,
        Polynomial.eval_X]
      rw [← h]
      exact h2
    have hcard : Nat.card {a : K // δ a = a} = 2 ^ (3 * e) := card_fix_delta he hK hδ
    have h1 : 2 ^ (3 * e) ≤ P.natDegree := by
      calc 2 ^ (3 * e) = (Finset.univ.filter fun s : K => δ s = s).card := by
            rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype]
        _ ≤ P.roots.toFinset.card := Finset.card_le_card hsub
        _ ≤ P.roots.card := Multiset.toFinset_card_le _
        _ ≤ P.natDegree := Polynomial.card_roots' _
    have h2 : 2 ^ (2 * e) < 2 ^ (3 * e) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨s, hs, hts⟩ := hnz
  set t := s + σ s + σ (σ s) with ht
  have hσ3 : ∀ c, σ (σ (σ c)) = c := fun c => by
    rw [hσ, hσ, hσ, ← pow_mul, ← pow_mul]
    have h : 2 ^ (2 * e) * (2 ^ (2 * e) * 2 ^ (2 * e)) = 2 ^ (6 * e) := by
      rw [← pow_add, ← pow_add]
      ring_nf
    rw [h, ← hK6, Nat.card_eq_fintype_card, FiniteField.pow_card]
  have htσ : σ t = t := by
    simp only [ht, map_add, hσ3]
    ring
  have htδ : δ t = t := by
    have h1 : δ (σ s) = σ s := by rw [ringEquiv_comm_of_finite σ δ s, hs]
    have h2 : δ (σ (σ s)) = σ (σ s) := by rw [ringEquiv_comm_of_finite σ δ (σ s), h1]
    simp only [ht, map_add, hs, h1, h2]
  refine ⟨t⁻¹ * s, ?_, ?_⟩
  · rw [map_mul, map_inv₀, htδ, hs]
  · simp only [map_mul, map_inv₀, htσ]
    calc t⁻¹ * s + t⁻¹ * σ s + t⁻¹ * σ (σ s) = t⁻¹ * (s + σ s + σ (σ s)) := by ring
      _ = 1 := by rw [← ht, inv_mul_cancel₀ hts]

end CFSG.Quasithin.H13.F431.D4q.Out
