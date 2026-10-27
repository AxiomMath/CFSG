module

public import CFSG.Open.Defs
public import CFSG.Open.StatedDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P51eZsig

public section

namespace CFSG.RankThree.GF2n.Smith81.Smith219Arith

open CFSG.Open CFSG.ComponentClassification.HarrisLit.T1.P51e

@[expose] def sylowExp : StatedLieTag → ℕ → ℕ
  | .PSL, k => k * (k - 1) / 2
  | .PSp, k => k * k
  | .POmegaPlus, k => k * (k - 1)
  | .POmegaMinus, k => k * (k - 1)
  | .G2, _ => 6
  | .trialityD4, _ => 12
  | .F4, _ => 24
  | .E6, _ => 36
  | .twistedE6, _ => 36
  | .E7, _ => 63
  | .E8, _ => 120
  | _, _ => 0

theorem two_mul_sylowExp_PSL (k : ℕ) : 2 * sylowExp .PSL k = k * (k - 1) :=
  Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self k)

theorem le_add_two_of_mul_le {f N N₀ a : ℕ} (h : f * N ≤ f * N₀ + a) (ha : a < 3 * f) :
    N ≤ N₀ + 2 := by
  by_contra hN
  have : f * (N₀ + 3) ≤ f * N := Nat.mul_le_mul_left f (by omega)
  nlinarith

theorem four_mul_add_one_lt_three_mul_two_pow {v : ℕ} (hv : 1 ≤ v) : 4 * v + 1 < 3 * 2 ^ v := by
  induction v, hv using Nat.le_induction with
  | base => norm_num
  | succ v hv ih =>
    have : 2 ≤ 2 ^ v := by simpa using Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hv
    rw [pow_succ]
    omega

theorem four_mul_padicValNat_two_add_one_lt {f : ℕ} (hf : 0 < f) :
    4 * padicValNat 2 f + 1 < 3 * f := by
  have hle : 2 ^ padicValNat 2 f ≤ f := Nat.le_of_dvd hf pow_padicValNat_dvd
  rcases Nat.eq_zero_or_pos (padicValNat 2 f) with h0 | hpos
  · rw [h0]; omega
  · have := four_mul_add_one_lt_three_mul_two_pow hpos
    omega

theorem eq_of_mul_pred_window {a k : ℕ} (ha : 2 ≤ a) (h1 : a * (a - 1) ≤ k * (k - 1))
    (h2 : k * (k - 1) < (a + 1) * a) : k = a := by
  rcases Nat.lt_or_ge k a with hk | hk
  · have h3 : k * (k - 1) ≤ (a - 1) * (a - 2) := Nat.mul_le_mul (by omega) (by omega)
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
    simp only [show b + 2 - 1 = b + 1 by omega, Nat.add_sub_cancel] at h1 h3
    nlinarith
  · rcases Nat.eq_or_lt_of_le hk with h | h
    · exact h.symm
    · have : (a + 1) * a ≤ k * (k - 1) := Nat.mul_le_mul h (by omega)
      omega

theorem laneA_window {t : StatedLieTag} {k m : ℕ} (hm : 2 ≤ m)
    (hlo : (m + 1) * (m + 2) ≤ sylowExp t k) (hhi : sylowExp t k ≤ (m + 1) * (m + 2) + 2)
    (hPSL : t = .PSL → 2 * m + 2 ≤ k) :
    ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ k = m + 2) ∨ (t = .trialityD4 ∧ m = 2) := by
  have hΩ : (m + 1) * (m + 2) ≤ k * (k - 1) → k * (k - 1) ≤ (m + 1) * (m + 2) + 2 → k = m + 2 :=
    fun h1 h2 => eq_of_mul_pred_window (by omega)
      (by simpa [show m + 2 - 1 = m + 1 by omega, Nat.mul_comm] using h1)
      (by nlinarith)
  cases t <;> simp only [sylowExp] at hlo hhi
  case PSL =>
    have h2 := two_mul_sylowExp_PSL k
    simp only [sylowExp] at h2
    have hk := hPSL rfl
    have : (2 * m + 2) * (2 * m + 1) ≤ k * (k - 1) := Nat.mul_le_mul hk (by omega)
    nlinarith
  case PSp =>
    rcases Nat.lt_or_ge k (m + 2) with hk | hk
    · have : k * k ≤ (m + 1) * (m + 1) := Nat.mul_le_mul (by omega) (by omega)
      nlinarith
    · have : (m + 2) * (m + 2) ≤ k * k := Nat.mul_le_mul hk hk
      nlinarith
  case POmegaPlus => exact Or.inl ⟨Or.inl rfl, hΩ hlo hhi⟩
  case POmegaMinus => exact Or.inl ⟨Or.inr rfl, hΩ hlo hhi⟩
  all_goals
    have hm10 : m ≤ 10 := by nlinarith
    interval_cases m <;> first | omega | exact Or.inr ⟨rfl, rfl⟩

theorem laneB_window {t : StatedLieTag} {k n N₀ : ℕ}
    (hn : (n = 10 ∧ N₀ = 36) ∨ (n = 16 ∧ N₀ = 63) ∨ (n = 28 ∧ N₀ = 120))
    (hlo : N₀ ≤ sylowExp t k) (hhi : sylowExp t k ≤ N₀ + 2)
    (hPSL : t = .PSL → n + 2 ≤ k) (hPSp : t = .PSp → n + 3 ≤ 2 * k) :
    (n = 10 ∧ (t = .E6 ∨ t = .twistedE6)) ∨ (n = 16 ∧ t = .E7) ∨ (n = 28 ∧ t = .E8) := by
  have h2 := two_mul_sylowExp_PSL k
  simp only [sylowExp] at h2
  rcases hn with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cases t <;>
    simp only [sylowExp] at hlo hhi
  all_goals first
    | omega
    | decide
    | (have hk := hPSL rfl
       have := Nat.mul_le_mul hk (Nat.sub_le_sub_right hk 1)
       omega)
    | (have hk := hPSp rfl; nlinarith)
    | (have hk : k ≤ 12 := by
         by_contra hk
         have : 13 * 12 ≤ k * (k - 1) := Nat.mul_le_mul (by omega) (by omega)
         omega
       interval_cases k <;> omega)

section PPD

variable {ℓ q e : ℕ}

private theorem not_dvd_div_of_not_dvd {a b : ℕ} (h : ¬ ℓ ∣ a) (hb : b ∣ a) : ¬ ℓ ∣ a / b :=
  fun h' => h (h'.trans (Nat.div_dvd_of_dvd hb))

private theorem odd_dvd_of_dvd_two_mul {k : ℕ} (he : Odd e) (h : e ∣ 2 * k) : e ∣ k :=
  (Nat.coprime_two_right.mpr he).dvd_of_dvd_mul_left h

theorem ne_two_of_even (h : IsPrimDiv ℓ q e) (hq : 2 ≤ q) (hqe : Even q) (he : 0 < e) :
    ℓ ≠ 2 := by
  rintro rfl
  have h1 : 2 ∣ q ^ e := (even_iff_two_dvd.mp hqe).pow he.ne'
  have h2 := Nat.dvd_sub h1 h.2.1
  rw [Nat.sub_sub_self (Nat.one_le_pow _ _ (by omega))] at h2
  omega

theorem not_dvd_pow_add_one_of_odd (h : IsPrimDiv ℓ q e) (hq : 2 ≤ q) (hqe : Even q)
    (he : Odd e) (j : ℕ) : ¬ ℓ ∣ q ^ j + 1 := by
  intro hd
  have hm := odd_dvd_of_dvd_two_mul he (h.dvd_two_mul_of_dvd_add_one (by omega) he.pos hd)
  have hs := (h.dvd_iff (by omega) he.pos j).mpr hm
  have h2 := Nat.dvd_sub hd hs
  rw [show q ^ j + 1 - (q ^ j - 1) = 2 by
    have := Nat.one_le_pow j q (by omega); omega] at h2
  exact ne_two_of_even h hq hqe he.pos ((Nat.prime_dvd_prime_iff_eq h.1 Nat.prime_two).mp h2)

theorem dvd_ordA (h : IsPrimDiv ℓ q e) (hq : 0 < q) (he : 2 ≤ e) {n : ℕ}
    (hen : e ≤ n + 1) : ℓ ∣ ordA n q := by
  unfold ordA
  set P := q ^ (n * (n + 1) / 2) * ∏ i ∈ Finset.Icc 2 (n + 1), (q ^ i - 1)
  have hg : Nat.gcd (n + 1) (q - 1) ∣ q - 1 := Nat.gcd_dvd_right _ _
  have hqP : q - 1 ∣ P :=
    (by simpa using Nat.sub_dvd_pow_sub_pow q 1 2 : q - 1 ∣ q ^ 2 - 1).trans
      (dvd_mul_of_dvd_right
        (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩)) _)
  have hP : ℓ ∣ P := dvd_mul_of_dvd_right
    (h.2.1.trans (Finset.dvd_prod_of_mem (fun i => q ^ i - 1) (Finset.mem_Icc.mpr ⟨he, hen⟩))) _
  have hgl : ¬ ℓ ∣ Nat.gcd (n + 1) (q - 1) := fun hd =>
    h.not_dvd_pow_sub_one hq (by omega) (f := 1)
      (fun h1 => by have := Nat.le_of_dvd one_pos h1; omega) (by rw [pow_one]; exact hd.trans hg)
  rw [← Nat.mul_div_cancel' (hg.trans hqP)] at hP
  exact ((Nat.Prime.dvd_mul h.1).mp hP).resolve_left hgl

private theorem add_one_dvd_sq_sub_one (q : ℕ) : q + 1 ∣ q ^ 2 - 1 := by
  have := pow_two_mul_sub_one q 1
  simp only [mul_one, pow_one] at this
  rw [this]
  exact dvd_mul_left _ _

theorem not_dvd_ordTwistedE6_five (h : IsPrimDiv ℓ q 5) (hq : 2 ≤ q) (hqe : Even q) :
    ¬ ℓ ∣ ordTwistedE6 q := by
  have hq0 : 0 < q := by omega
  unfold ordTwistedE6
  refine not_dvd_div_of_not_dvd ?_ ((Nat.gcd_dvd_right _ _).trans
    ((add_one_dvd_sq_sub_one q).trans (dvd_mul_left _ _)))
  simp only [h.1.dvd_mul, not_or]
  repeat' constructor
  all_goals first
    | exact h.not_dvd_pow_base hq0 (by norm_num) _
    | exact h.not_dvd_pow_sub_one hq0 (by norm_num) (by norm_num)
    | exact not_dvd_pow_add_one_of_odd h hq hqe (by decide) _

theorem not_dvd_ordE6_ten (h : IsPrimDiv ℓ q 10) (hq : 0 < q) : ¬ ℓ ∣ ordE6 q := by
  unfold ordE6
  refine not_dvd_div_of_not_dvd ?_ ((Nat.gcd_dvd_right _ _).trans
    ((by simpa using Nat.sub_dvd_pow_sub_pow q 1 2 : q - 1 ∣ q ^ 2 - 1).trans
      (dvd_mul_left _ _)))
  simp only [h.1.dvd_mul, not_or]
  repeat' constructor
  all_goals first
    | exact h.not_dvd_pow_base hq (by norm_num) _
    | exact h.not_dvd_pow_sub_one hq (by norm_num) (by norm_num)

private theorem toNat_pow_sub_neg_one_pow_of_odd {j : ℕ} (hj : Odd j) (q : ℕ) :
    ((q : ℤ) ^ j - (-1) ^ j).toNat = q ^ j + 1 := by
  rw [hj.neg_one_pow, show (q : ℤ) ^ j - -1 = ((q ^ j + 1 : ℕ) : ℤ) by push_cast; ring,
    Int.toNat_natCast]

theorem dvd_ordTwistedA_five (h : IsPrimDiv ℓ q 10) (hq : 0 < q) :
    ℓ ∣ ordTwistedA 5 q := by
  unfold ordTwistedA
  set P := q ^ (5 * (5 + 1) / 2) *
    ∏ i ∈ Finset.Icc 2 (5 + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat
  have hg : Nat.gcd (5 + 1) (q + 1) ∣ q + 1 := Nat.gcd_dvd_right _ _
  have hfac : ∀ j ∈ Finset.Icc 2 (5 + 1), Odd j →
      q ^ j + 1 ∣ ∏ i ∈ Finset.Icc 2 (5 + 1), ((q : ℤ) ^ i - (-1 : ℤ) ^ i).toNat :=
    fun j hj hjo => toNat_pow_sub_neg_one_pow_of_odd hjo q ▸ Finset.dvd_prod_of_mem _ hj
  have hqP : q + 1 ∣ P := dvd_mul_of_dvd_right
    ((by simpa using Odd.nat_add_dvd_pow_add_pow q 1 (by decide : Odd 3) :
      q + 1 ∣ q ^ 3 + 1).trans (hfac 3 (by decide) (by decide))) _
  have hP : ℓ ∣ P := dvd_mul_of_dvd_right
    ((h.dvd_pow_add_one (k := 5) (by norm_num)).trans (hfac 5 (by decide) (by decide))) _
  have hgl : ¬ ℓ ∣ Nat.gcd (5 + 1) (q + 1) := fun hd =>
    h.not_dvd_pow_add_one hq (by norm_num) (f := 1) (by norm_num)
      (by rw [pow_one]; exact hd.trans hg)
  rw [← Nat.mul_div_cancel' (hg.trans hqP)] at hP
  exact ((Nat.Prime.dvd_mul h.1).mp hP).resolve_left hgl

end PPD

theorem laneB_ppd_L6 {q : ℕ} (hq : 4 ≤ q) (hqe : Even q) :
    ∃ ℓ, ℓ.Prime ∧ ℓ ∣ ordA 5 q ∧ ¬ ℓ ∣ ordTwistedE6 q := by
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv (by omega : 3 ≤ q) (by norm_num : 3 ≤ 5)
  exact ⟨ℓ, hℓ.1, dvd_ordA hℓ (by omega) (by norm_num) (by norm_num),
    not_dvd_ordTwistedE6_five hℓ (by omega) hqe⟩

theorem laneB_ppd_U6 {q : ℕ} (hq : 3 ≤ q) :
    ∃ ℓ, ℓ.Prime ∧ ℓ ∣ ordTwistedA 5 q ∧ ¬ ℓ ∣ ordE6 q := by
  obtain ⟨ℓ, hℓ⟩ := exists_isPrimDiv hq (by norm_num : 3 ≤ 10)
  exact ⟨ℓ, hℓ.1, dvd_ordTwistedA_five hℓ (by omega), not_dvd_ordE6_ten hℓ (by omega)⟩

end CFSG.RankThree.GF2n.Smith81.Smith219Arith
