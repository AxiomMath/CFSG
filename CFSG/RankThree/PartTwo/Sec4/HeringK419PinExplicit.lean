module

public import CFSG.RankThree.PartTwo.Sec4.HeringK419PinNum

public section

namespace CFSG.RankThree.PartTwo.Sec4.HeringPin

open Finset

@[expose] def ExplicitD : Finset ℕ :=
  {362880, 1080, 7560,
   7920, 95040, 443520, 10200960, 244823040, 175560, 604800, 50232960, 86775571046077562880,
   898128000, 44352000, 4030387200, 460815505920, 145926144000,
   3 * 7920, 3 * 95040, 3 * 443520, 3 * 10200960, 3 * 244823040, 3 * 175560, 3 * 604800,
   3 * 50232960, 3 * 86775571046077562880, 3 * 898128000, 3 * 44352000, 3 * 4030387200,
   3 * 460815505920,
   17971200, 9999360, 1451520, 4 ^ 10 * 254840625, 5616, 42456960, 6048, 42573600, 12130560,
   25474176, 19595520}

theorem ExplicitD_pos : ∀ D ∈ ExplicitD, 0 < D := by decide +kernel

theorem ExplicitD_lt : ∀ D ∈ ExplicitD, D < 360 ^ 8 := by decide +kernel

theorem ExplicitD_pow8 : ∀ D ∈ ExplicitD, ∀ p < 360, p.Prime → p ^ 8 ∣ D → p = 2 := by
  decide +kernel

theorem ExplicitD_two : ∀ D ∈ ExplicitD, ¬ 2 ^ 22 ∣ D := by decide +kernel

theorem pow_dvd_explicit {D p k : ℕ} (hD : D ∈ ExplicitD) (hp : p.Prime) (hk : 8 ≤ k)
    (h : p ^ k ∣ D) : p = 2 ∧ k ≤ 21 := by
  have h8 : p ^ 8 ∣ D := (pow_dvd_pow p hk).trans h
  have hlt : p < 360 := by
    by_contra hc
    push Not at hc
    have h1 := Nat.pow_le_pow_left hc 8
    have h2 := Nat.le_of_dvd (ExplicitD_pos D hD) h8
    have h3 := ExplicitD_lt D hD
    omega
  have hp2 := ExplicitD_pow8 D hD p hlt hp h8
  subst hp2
  refine ⟨rfl, ?_⟩
  by_contra hc
  push Not at hc
  exact ExplicitD_two D hD ((pow_dvd_pow 2 hc).trans h)

theorem explicit_sl42 : ∀ D ∈ ExplicitD, ∀ g ∈ ({1, 3} : Finset ℕ),
    ¬ ((2 ^ 2) ^ (4 * (4 - 1) / 2) * ∏ j ∈ Icc 2 4, ((2 ^ 2) ^ j - 1)) ∣ D * g := by
  decide +kernel

theorem explicit_sl43 : ∀ D ∈ ExplicitD, ∀ g ∈ ({1, 7} : Finset ℕ),
    ¬ ((2 ^ 3) ^ (4 * (4 - 1) / 2) * ∏ j ∈ Icc 2 4, ((2 ^ 3) ^ j - 1)) ∣ D * g := by
  decide +kernel

theorem explicit_sl52 : ∀ D ∈ ExplicitD, ∀ g ∈ ({1, 3} : Finset ℕ),
    ¬ ((2 ^ 2) ^ (5 * (5 - 1) / 2) * ∏ j ∈ Icc 2 5, ((2 ^ 2) ^ j - 1)) ∣ D * g := by
  decide +kernel

theorem explicit_sp32 : ∀ D ∈ ExplicitD,
    ¬ ((2 ^ 2) ^ (3 ^ 2) * ∏ j ∈ Icc 1 3, ((2 ^ 2) ^ (2 * j) - 1)) ∣ D := by
  decide +kernel

theorem explicit_false {M p e D : ℕ} (hX : XOrd M p e) (hp : p.Prime) (he : 2 ≤ e)
    (hD : D ∈ ExplicitD) (hMD : M ∣ D) : False := by
  cases hX with
  | sl n g hn hg h =>
    have hT2 : 2 * (n * (n - 1) / 2) = n * (n - 1) :=
      Nat.mul_div_cancel' (Nat.even_mul_pred_self n).two_dvd
    obtain ⟨hT6, -, -⟩ := tri_facts hn hT2
    have hP : ¬ p ∣ ∏ j ∈ Icc 2 n, ((p ^ e) ^ j - 1) :=
      not_dvd_prod_pow_sub_one hp (by omega) _ (fun j => j)
        (fun j hj => by have := (mem_Icc.mp hj).1; show 1 ≤ j; omega)
    have hpg : ¬ p ∣ g := by
      intro hpg
      have h2 := not_dvd_pow_pow_sub_one (p := p) (e := e) (j := 1) hp (by omega) le_rfl
      rw [pow_one] at h2
      exact h2 (hpg.trans hg)
    have hdvd : p ^ (e * (n * (n - 1) / 2)) ∣ M :=
      (exact_pow_of_mul_eq hp hpg hP (by rw [h, ← pow_mul])).1
    have hk8 : 8 ≤ e * (n * (n - 1) / 2) := by nlinarith
    obtain ⟨rfl, hk21⟩ := pow_dvd_explicit hD hp hk8 (hdvd.trans hMD)
    have hn5 : n ≤ 5 := by
      by_contra hc
      push Not at hc
      have : 15 ≤ n * (n - 1) / 2 := by
        have : 30 ≤ n * (n - 1) := by
          obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
          simp only [Nat.add_sub_cancel]
          nlinarith
        omega
      nlinarith
    have hn45 : n = 4 ∨ n = 5 := by omega
    rcases hn45 with rfl | rfl
    · have he3 : e ≤ 3 := by
        have : e * 6 ≤ 21 := by simpa using hk21
        omega
      interval_cases e
      · have hg' : g ∈ ({1, 3} : Finset ℕ) := by
          have h3 : g ∣ 3 := by simpa using hg
          rcases (Nat.dvd_prime Nat.prime_three).mp h3 with rfl | rfl <;> simp
        exact explicit_sl42 D hD g hg' (by rw [← h]; exact Nat.mul_dvd_mul_right hMD g)
      · have hg' : g ∈ ({1, 7} : Finset ℕ) := by
          have h3 : g ∣ 7 := by simpa using hg
          rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h3 with rfl | rfl <;> simp
        exact explicit_sl43 D hD g hg' (by rw [← h]; exact Nat.mul_dvd_mul_right hMD g)
    · have he2 : e = 2 := by
        have : e * 10 ≤ 21 := by simpa using hk21
        omega
      subst he2
      have hg' : g ∈ ({1, 3} : Finset ℕ) := by
        have h3 : g ∣ 3 := by simpa using hg
        rcases (Nat.dvd_prime Nat.prime_three).mp h3 with rfl | rfl <;> simp
      exact explicit_sl52 D hD g hg' (by rw [← h]; exact Nat.mul_dvd_mul_right hMD g)
  | spOdd r hr hp2 h =>
    have hP : ¬ p ∣ ∏ j ∈ Icc 1 r, ((p ^ e) ^ (2 * j) - 1) :=
      not_dvd_prod_pow_sub_one hp (by omega) _ (fun j => 2 * j)
        (fun j hj => by have := (mem_Icc.mp hj).1; show 1 ≤ 2 * j; omega)
    have hp2' : ¬ p ∣ 2 := fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
    have hdvd : p ^ (e * r ^ 2) ∣ M :=
      (exact_pow_of_mul_eq hp hp2' hP (by rw [h, ← pow_mul])).1
    have hr4 : 4 ≤ r ^ 2 := by nlinarith
    have hk8 : 8 ≤ e * r ^ 2 := by nlinarith
    exact hp2 (pow_dvd_explicit hD hp hk8 (hdvd.trans hMD)).1
  | spEven r hr hp2 h =>
    subst hp2
    have hdvd : 2 ^ (e * r ^ 2) ∣ M := ⟨_, by rw [h, ← pow_mul]⟩
    have hr9 : 9 ≤ r ^ 2 := by nlinarith
    have hk8 : 8 ≤ e * r ^ 2 := by nlinarith
    obtain ⟨-, hk21⟩ := pow_dvd_explicit hD hp hk8 (hdvd.trans hMD)
    have hr3 : r = 3 := by
      by_contra hc
      have : 16 ≤ r ^ 2 := by nlinarith [show 4 ≤ r by omega]
      nlinarith
    subst hr3
    have he2 : e = 2 := by omega
    subst he2
    exact explicit_sp32 D hD (h ▸ hMD)

end CFSG.RankThree.PartTwo.Sec4.HeringPin
