module

public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

theorem eq_one_of_fix_of_outer {S : Type} [Group S] [Finite S] (hZ : Subgroup.center S = ⊥)
    (hOut : ∀ σ : MulAut S, ∃ k : ℕ, σ ^ (2 ^ k) ∈ (MulAut.conj : S →* MulAut S).range)
    (C : Subgroup S) (hC3 : ∀ g : S, (∀ c ∈ C, g * c = c * g) → ∃ n : ℕ, g ^ (3 ^ n) = 1)
    (hτ : ∀ τ : MulAut S, τ ^ 2 = 1 → τ ∉ (MulAut.conj : S →* MulAut S).range →
      ¬ ∀ c ∈ C, τ c = c) :
    ∀ σ : MulAut S, Nat.Coprime (orderOf σ) 3 → (∀ c ∈ C, σ c = c) → σ = 1 := by
  have hconj : ∀ x : S, MulAut.conj x = 1 → x = 1 := by
    intro x hx
    have hcen : x ∈ Subgroup.center S := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg := DFunLike.congr_fun hx g
      rw [MulAut.conj_apply, MulAut.one_apply] at hg
      exact (mul_inv_eq_iff_eq_mul.mp hg).symm
    rw [hZ] at hcen
    exact Subgroup.mem_bot.mp hcen
  have hcent : ∀ h : S, (∀ c ∈ C, h * c = c * h) → ∀ N : ℕ, Nat.Coprime N 3 →
      h ^ N = 1 → h = 1 := by
    intro h hh N hN hpow
    obtain ⟨j, hj⟩ := hC3 h hh
    have hg : h ^ (Nat.gcd N (3 ^ j)) = 1 := pow_gcd_eq_one.mpr ⟨hpow, hj⟩
    have hcop : Nat.gcd N (3 ^ j) = 1 := Nat.Coprime.pow_right j hN
    rw [hcop, pow_one] at hg
    exact hg
  have hinv : ∀ ν : MulAut S, ν ^ 2 = 1 → (∀ c ∈ C, ν c = c) → ν = 1 := by
    intro ν hν2 hfix
    have hrange : ν ∈ (MulAut.conj : S →* MulAut S).range := by
      by_contra hnr
      exact hτ ν hν2 hnr hfix
    obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hrange
    subst hg
    have hg2 : g ^ 2 = 1 := by
      apply hconj
      rw [map_pow]
      exact hν2
    have hcomm : ∀ c ∈ C, g * c = c * g := by
      intro c hc
      have hgc := hfix c hc
      rw [MulAut.conj_apply] at hgc
      exact mul_inv_eq_iff_eq_mul.mp hgc
    have hg1 : g = 1 := hcent g hcomm 2 (by decide) hg2
    rw [hg1, map_one]
  intro σ hcop hfix
  have hpow_fix : ∀ m : ℕ, ∀ c ∈ C, (σ ^ m) c = c := by
    intro m c hc
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ, MulAut.mul_apply, hfix c hc, ih]
  have hn0 : 0 < orderOf σ := by
    apply Nat.pos_of_ne_zero
    intro h
    rw [h] at hcop
    exact absurd hcop (by decide)
  obtain ⟨k, hk⟩ := hOut σ
  obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp hk
  have hgC : ∀ c ∈ C, g * c = c * g := by
    intro c hc
    have h1 : MulAut.conj g c = c := by
      rw [hg]
      exact hpow_fix (2 ^ k) c hc
    rw [MulAut.conj_apply] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  have hgn : g ^ orderOf σ = 1 := by
    apply hconj
    rw [map_pow, hg, ← pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  have hg1 : g = 1 := hcent g hgC (orderOf σ) hcop hgn
  have hpow2 : σ ^ (2 ^ k) = 1 := by
    rw [← hg, hg1, map_one]
  have hdvd2 : orderOf σ ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hpow2
  have hodd : ¬ 2 ∣ orderOf σ := by
    intro h2
    have hhalf : orderOf σ / 2 ≠ 0 := by
      have hle : 2 ≤ orderOf σ := Nat.le_of_dvd hn0 h2
      omega
    have hν : σ ^ (orderOf σ / 2) ≠ 1 := by
      intro h1
      have hd : orderOf σ ∣ orderOf σ / 2 := orderOf_dvd_of_pow_eq_one h1
      have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hhalf) hd
      have hlt : orderOf σ / 2 < orderOf σ := Nat.div_lt_self hn0 (by decide)
      omega
    have hν2 : (σ ^ (orderOf σ / 2)) ^ 2 = 1 := by
      rw [← pow_mul, Nat.div_mul_cancel h2, pow_orderOf_eq_one]
    exact hν (hinv _ hν2 (hpow_fix _))
  obtain ⟨i, _, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd2
  cases i with
  | zero =>
    rw [pow_zero] at hi
    exact orderOf_eq_one_iff.mp hi
  | succ i =>
    exfalso
    apply hodd
    rw [hi]
    exact dvd_pow_self 2 (Nat.succ_ne_zero i)

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Proving

end
