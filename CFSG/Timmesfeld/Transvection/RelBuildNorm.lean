module

public import CFSG.Timmesfeld.Transvection.RelBuildField
public import CFSG.LieType.BorelTits.UnitaryForm

public section

namespace CFSG.Timmesfeld.Transvection.RelBuild

open CFSG.LieType.BorelTits

variable {F : Type*} [Field F] [CharP F 2]

theorem exists_tw_of_add_of_norm {σ : F ≃+* F} {φ : F → F}
    (hadd : ∀ s t, φ (s + t) = φ s + φ t) {m : F}
    (hN : ∀ s, σ (φ s) * φ s = m * (σ s * s)) :
    ∃ e, ∀ s, φ s = φ 1 * tw σ e s := by
  have h1 : m = σ (φ 1) * φ 1 := by
    simpa using (hN 1).symm
  by_cases hK : φ 1 = 0
  · have hm0 : m = 0 := by rw [h1, hK, map_zero, zero_mul]
    have hφ : ∀ s, φ s = 0 := by
      intro s
      have h := hN s
      rw [hm0, zero_mul] at h
      rcases mul_eq_zero.mp h with h' | h'
      · exact σ.injective (by simpa using h')
      · exact h'
    refine ⟨false, fun s => ?_⟩
    simp [hφ s, hK]
  · have hσK : σ (φ 1) ≠ 0 := by
      intro h
      exact hK (σ.injective (h.trans (map_zero σ).symm))
    have key : ∀ s, (φ s - φ 1 * s) * (φ s - φ 1 * σ s) = 0 := by
      intro s
      have h2 : σ (φ s) * φ s = m * (σ s * s) := hN s
      have h4 : (σ (φ s) + σ (φ 1)) * (φ s + φ 1) = m * ((σ s + 1) * (s + 1)) := by
        simpa [hadd s 1] using hN (s + 1)
      have h3 : φ 1 * σ (φ s) + σ (φ 1) * φ s = m * (σ s + s) := by
        linear_combination h4 - h2 + h1
      rw [h1] at h2 h3
      have hmain : σ (φ 1) * ((φ s - φ 1 * s) * (φ s - φ 1 * σ s)) =
          φ s * (φ 1 * σ (φ s) + σ (φ 1) * φ s - (σ (φ 1) * φ 1) * (σ s + s)) -
            φ 1 * (σ (φ s) * φ s - (σ (φ 1) * φ 1) * (σ s * s)) := by
        ring
      rw [h2, h3] at hmain
      simp only [sub_self, mul_zero, sub_zero] at hmain
      exact (mul_eq_zero.mp hmain).resolve_left hσK
    have hPQ : ∀ s, (φ s = φ 1 * s) ∨ (φ s = φ 1 * σ s) := by
      intro s
      rcases mul_eq_zero.mp (key s) with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (sub_eq_zero.mp h)
    rcases forall_or_forall_of_add (P := fun t => φ t = φ 1 * t)
        (Q := fun t => φ t = φ 1 * σ t)
        (fun a b ha hb => by rw [hadd a b, ha, hb]; ring)
        (fun a b ha hb => by rw [hadd a b, ha, hb, map_add]; ring) hPQ with h | h
    · exact ⟨false, fun s => by rw [tw_false]; exact h s⟩
    · exact ⟨true, fun s => by rw [tw_true]; exact h s⟩

theorem exists_norm_eq_one_pow_six_ne_one {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 2 ≤ n) :
    ∃ b : K, unitaryInvolution K 2 n b * b = 1 ∧ b ^ 6 ≠ 1 := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  have hq2 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = (2 ^ n) ^ 2 - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf g = (2 ^ n) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
  have hfac : (2 ^ n - 1) * (2 ^ n + 1) = (2 ^ n) ^ 2 - 1 := by
    simpa [mul_comm, one_pow] using (Nat.sq_sub_sq (2 ^ n) 1).symm
  refine ⟨((g ^ (2 ^ n - 1) : Kˣ) : K), ?_, ?_⟩
  · rw [unitaryInvolution_apply, ← pow_succ, ← Units.val_pow_eq_pow_val, ← pow_mul, hfac, ← hord,
      pow_orderOf_eq_one, Units.val_one]
  · intro h
    have h6 : (g ^ (2 ^ n - 1)) ^ 6 = 1 := by
      refine Units.ext ?_
      rw [Units.val_pow_eq_pow_val]
      simpa using h
    have h6' : g ^ ((2 ^ n - 1) * 6) = 1 := by
      rw [pow_mul]
      exact h6
    have hdvd0 := orderOf_dvd_of_pow_eq_one h6'
    rw [hord, ← hfac] at hdvd0
    have hdvd : 2 ^ n + 1 ∣ 6 := Nat.dvd_of_mul_dvd_mul_left (by omega) hdvd0
    have hle : 2 ^ n + 1 ≤ 6 := Nat.le_of_dvd (by norm_num) hdvd
    have hnle : n ≤ 2 := by
      by_contra hlt
      have h8 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num at h8
      omega
    interval_cases n
    norm_num at hdvd

end CFSG.Timmesfeld.Transvection.RelBuild
