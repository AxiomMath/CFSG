module

public import CFSG.RankThree.PartOne.D4RC.OrdWindows
public import CFSG.RankThree.PartOne.D4RC.OrdPart
import all CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartOne.D4RC

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

@[expose] def SimplyLacedOrder (f m : ℕ) : Prop :=
  (∃ n, 2 ≤ n ∧ m = ordA n (2 ^ f)) ∨ (∃ n, 4 ≤ n ∧ m = ordD n (2 ^ f)) ∨
    m = ordE6 (2 ^ f) ∨ m = ordE7 (2 ^ f) ∨ m = ordE8 (2 ^ f)

@[expose] def NSLOrder (m : ℕ) : Prop :=
  (∃ n g, 3 ≤ n ∧ 1 ≤ g ∧ m = ordBC n (2 ^ g)) ∨
    (∃ n g, 4 ≤ n ∧ 1 ≤ g ∧ m = ordTwistedD n (2 ^ g)) ∨
    (∃ g, 2 ≤ g ∧ m = ordG2 (2 ^ g)) ∨
    (∃ g, 1 ≤ g ∧ (m = ordTrialityD4 (2 ^ g) ∨ m = ordF4 (2 ^ g) ∨ m = ordTwistedE6 (2 ^ g))) ∨
    m = 6048

theorem rcs_part_ge {p M m k : ℕ} (hp : p.Prime) (hM : M ≠ 0) (hk : p ^ k ∣ M)
    (hpm : p ^ padicValNat p M ∣ m) : p ^ k ∣ m := by
  have := Fact.mk hp
  exact (pow_dvd_pow p ((padicValNat_dvd_iff_le hM).mp hk)).trans hpm

theorem rcs_not_zD4_four {f : ℕ} (hf : 0 < f) : ¬ zD4 f (f * 4) := by
  have h := rcs_zD4_mul hf (b := 1) (t := 4)
  rw [mul_one] at h
  exact fun hz => (by decide : ¬ zD4 1 4) (h.mp hz)

theorem rcs_not_zD4_five {f : ℕ} (hf : 0 < f) : ¬ zD4 f (f * 5) := by
  have h := rcs_zD4_mul hf (b := 1) (t := 5)
  rw [mul_one] at h
  exact fun hz => (by decide : ¬ zD4 1 5) (h.mp hz)

theorem rcs_simply_laced {c f p m : ℕ} (hc : c = 3 ∨ c = 6) (hf : 0 < f) (hp : p.Prime)
    (hpK : p ∣ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) (hmM : m ∣ ordTrialityD4 (2 ^ f))
    (hRm : rOrd c f ∣ m) (hpm : p ^ padicValNat p (ordTrialityD4 (2 ^ f)) ∣ m)
    (hfam : SimplyLacedOrder f m) : False := by
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow hf.ne'
  have hM := profile_ordTrialityD4 hf
  rcases hfam with ⟨n, hn, rfl⟩ | ⟨n, hn, rfl⟩ | rfl | rfl | rfl
  ·
    obtain ⟨h2, h3, -, -⟩ := rcs_prelude hc hf (profile_ordA (by omega) hf) hmM hRm
    have h3' : n * (n + 1) / 2 ≤ 12 := Nat.le_of_mul_le_mul_left (by linarith) hf
    have hn4 : n ≤ 4 := by
      by_contra h
      have : 5 * 6 ≤ n * (n + 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    interval_cases n
    · exact rcs_psl3_part hp hpK hq hpm
    · refine absurd (rcs_transfer (profile_ordA (by omega) hf) hM hmM (k := f * 4)
        (by omega) (by omega) ⟨4, by simp, ⟨1, by ring⟩⟩) (rcs_not_zD4_four hf)
    · refine absurd (rcs_transfer (profile_ordA (by omega) hf) hM hmM (k := f * 5)
        (by omega) (by omega) ⟨5, by simp, ⟨1, by ring⟩⟩) (rcs_not_zD4_five hf)
  ·
    obtain ⟨h2, h3, -, -⟩ := rcs_prelude hc hf (profile_ordD (by omega) hf) hmM hRm
    have h3' : n * (n - 1) ≤ 12 := Nat.le_of_mul_le_mul_left (by linarith) hf
    have hn4 : n ≤ 4 := by
      by_contra h
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
      have : 5 * 4 ≤ (k + 5) * (k + 5 - 1) := Nat.mul_le_mul (by omega) (by omega)
      omega
    obtain rfl : n = 4 := by omega
    exact absurd (rcs_transfer (profile_ordD (by omega) hf) hM hmM (k := f * 4)
      (by omega) (by omega) (Or.inl dvd_rfl)) (rcs_not_zD4_four hf)
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude hc hf (profile_ordE6 hf) hmM hRm
    omega
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude hc hf (profile_ordE7 hf) hmM hRm
    omega
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude hc hf (profile_ordE8 hf) hmM hRm
    omega


theorem rcs_f2_psp : ∀ n ∈ Finset.Icc 3 4, ∀ g ∈ Finset.Icc 1 2,
    ¬ (ordBC n (2 ^ g) ∣ ordTrialityD4 (2 ^ 2) ∧ rOrd 3 2 ∣ ordBC n (2 ^ g) ∧
      7 ^ 2 ∣ ordBC n (2 ^ g)) := by
  decide +kernel

theorem rcs_f2_pom : ∀ n ∈ Finset.Icc 4 5, ∀ g ∈ Finset.Icc 1 2,
    ¬ (ordTwistedD n (2 ^ g) ∣ ordTrialityD4 (2 ^ 2) ∧ rOrd 3 2 ∣ ordTwistedD n (2 ^ g) ∧
      7 ^ 2 ∣ ordTwistedD n (2 ^ g)) := by
  decide +kernel

theorem rcs_f2_g2 : ∀ g ∈ Finset.Icc 2 4,
    ¬ (ordG2 (2 ^ g) ∣ ordTrialityD4 (2 ^ 2) ∧ rOrd 3 2 ∣ ordG2 (2 ^ g) ∧
      7 ^ 2 ∣ ordG2 (2 ^ g)) := by
  decide +kernel

theorem rcs_f2_d4 : ¬ (ordTrialityD4 (2 ^ 1) ∣ ordTrialityD4 (2 ^ 2) ∧
    rOrd 3 2 ∣ ordTrialityD4 (2 ^ 1)) := by
  decide +kernel

theorem rcs_f2_f4 : ¬ (ordF4 (2 ^ 1) ∣ ordTrialityD4 (2 ^ 2) ∧ rOrd 3 2 ∣ ordF4 (2 ^ 1)) := by
  decide +kernel

theorem rcs_f2_psu : ¬ rOrd 3 2 ∣ 6048 := by decide +kernel

theorem rcs_nsl_f2 {m : ℕ} (hmM : m ∣ ordTrialityD4 (2 ^ 2)) (hRm : rOrd 3 2 ∣ m)
    (h49 : 7 ^ 2 ∣ m) (hfam : NSLOrder m) : m = ordTrialityD4 (2 ^ 2) := by
  rcases hfam with ⟨n, g, hn, hg, rfl⟩ | ⟨n, g, hn, hg, rfl⟩ | ⟨g, hg, rfl⟩ |
    ⟨g, hg, rfl | rfl | rfl⟩ | rfl
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude (Or.inl rfl) (by norm_num) (profile_ordBC hg) hmM hRm
    have h9 : 9 ≤ n * n := Nat.mul_le_mul hn hn
    have hg2 : g ≤ 2 := by
      have := Nat.mul_le_mul_left g h9
      omega
    have hn4 : n ≤ 4 := by
      by_contra h
      have h25 : 5 * 5 ≤ n * n := Nat.mul_le_mul (show 5 ≤ n by omega) (show 5 ≤ n by omega)
      have := Nat.mul_le_mul_left g h25
      omega
    exact absurd ⟨hmM, hRm, h49⟩ (rcs_f2_psp n (Finset.mem_Icc.mpr ⟨hn, hn4⟩) g
      (Finset.mem_Icc.mpr ⟨hg, hg2⟩))
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude (Or.inl rfl) (by norm_num)
      (profile_ordTwistedD (by omega) hg) hmM hRm
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hn (show 3 ≤ n - 1 by omega)
    have hg2 : g ≤ 2 := by
      have := Nat.mul_le_mul_left g h12
      omega
    have hn5 : n ≤ 5 := by
      by_contra h
      have h30 : 6 * 5 ≤ n * (n - 1) :=
        Nat.mul_le_mul (show 6 ≤ n by omega) (show 5 ≤ n - 1 by omega)
      have := Nat.mul_le_mul_left g h30
      omega
    exact absurd ⟨hmM, hRm, h49⟩ (rcs_f2_pom n (Finset.mem_Icc.mpr ⟨hn, hn5⟩) g
      (Finset.mem_Icc.mpr ⟨hg, hg2⟩))
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude (Or.inl rfl) (by norm_num) (profile_ordG2 (by omega))
      hmM hRm
    exact absurd ⟨hmM, hRm, h49⟩ (rcs_f2_g2 g (Finset.mem_Icc.mpr ⟨hg, by omega⟩))
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude (Or.inl rfl) (by norm_num) (profile_ordTrialityD4 hg)
      hmM hRm
    obtain rfl | rfl : g = 1 ∨ g = 2 := by omega
    · exact absurd ⟨hmM, hRm⟩ rcs_f2_d4
    · rfl
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude (Or.inl rfl) (by norm_num) (profile_ordF4 hg) hmM hRm
    obtain rfl : g = 1 := by omega
    exact absurd ⟨hmM, hRm⟩ rcs_f2_f4
  · obtain ⟨-, h3, -, -⟩ := rcs_prelude (Or.inl rfl) (by norm_num) (profile_ordTwistedE6 hg)
      hmM hRm
    omega
  · exact absurd hRm rcs_f2_psu

theorem rcs_rOrd_big {c f : ℕ} (hf : 2 ≤ f) : 6048 < rOrd c f := by
  have hq4 : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have h3 : 64 ≤ (2 ^ f) ^ 3 := by
    calc 64 = 4 ^ 3 := by norm_num
      _ ≤ (2 ^ f) ^ 3 := Nat.pow_le_pow_left hq4 3
  have h2 : 16 ≤ (2 ^ f) ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ f) ^ 2 := Nat.pow_le_pow_left hq4 2
  have h2' : 15 ≤ (2 ^ f) ^ 2 - 1 := by omega
  unfold rOrd
  split_ifs
  · have h3' : 63 ≤ (2 ^ f) ^ 3 - 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h3 h2') h3'
    omega
  · have h3' : 63 ≤ (2 ^ f) ^ 3 + 1 := by omega
    have := Nat.mul_le_mul (Nat.mul_le_mul h3 h2') h3'
    omega

theorem rcs_nsl {c f p m : ℕ} (hc : c = 3 ∨ c = 6) (hf : 0 < f) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpΦ : p ∣ phiOrd c (2 ^ f)) (hmM : m ∣ ordTrialityD4 (2 ^ f)) (hRm : rOrd c f ∣ m)
    (hpm : p ^ padicValNat p (ordTrialityD4 (2 ^ f)) ∣ m) (hfam : NSLOrder m) :
    m = ordTrialityD4 (2 ^ f) := by
  have hq : 1 < 2 ^ f := Nat.one_lt_two_pow hf.ne'
  have hpK : p ∣ (2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1 := rcs_prime_dvd_triality hc (by omega) hpΦ
  have hM0 : ordTrialityD4 (2 ^ f) ≠ 0 := by
    have h1 : 0 < (2 ^ f) ^ 6 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
    have h2 : 0 < (2 ^ f) ^ 2 - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow (by norm_num) hq)
    unfold ordTrialityD4
    positivity
  have hne : ¬ (c = 6 ∧ f = 1) := by
    rintro ⟨rfl, rfl⟩
    have h3 : p ∣ 3 := by simpa [phiOrd] using hpΦ
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  by_cases hspec : c = 3 ∧ f = 2
  · obtain ⟨rfl, rfl⟩ := hspec
    have hp21 : p ∣ 7 * 3 := by simpa [phiOrd] using hpΦ
    have hp7 : p = 7 := by
      rcases (Nat.Prime.dvd_mul hp).mp hp21 with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp h
      · have := Nat.le_of_dvd (by norm_num) h
        omega
    subst hp7
    exact rcs_nsl_f2 hmM hRm (rcs_part_ge hp hM0 (by decide) hpm) hfam
  have h6 : c * f ≠ 6 := by rcases hc with rfl | rfl <;> omega
  rcases hfam with ⟨n, g, hn, hg, rfl⟩ | ⟨n, g, hn, hg, rfl⟩ | ⟨g, hg, rfl⟩ |
    ⟨g, hg, rfl | rfl | rfl⟩ | rfl
  ·
    obtain ⟨h2, h3, hG, hR⟩ := rcs_prelude hc hf (profile_ordBC hg) hmM hRm
    obtain ⟨hc3, hn3, hfg⟩ := rcs_window_psp hc hn hf hg hG hR (rcs_first_index hc hf h6 hR) h2 h3
    subst hn3 hc3
    have hg2 : 2 ≤ g := by omega
    rw [hfg] at hmM
    exact absurd hmM (rcs_sp6_not_dvd hg2)
  ·
    obtain ⟨h2, h3, hG, hR⟩ := rcs_prelude hc hf (profile_ordTwistedD (by omega) hg) hmM hRm
    exact (rcs_window_pom hc hn hf hg hG hR (rcs_first_index hc hf h6 hR) h2 h3).elim
  ·
    obtain ⟨h2, h3, hG, hR⟩ := rcs_prelude hc hf (profile_ordG2 (by omega)) hmM hRm
    obtain rfl := rcs_window_g2 hc hf (by omega) hG hR (rcs_first_index hc hf h6 hR) h2 h3
    exact absurd hpm (rcs_g2_part hp hpK hq)
  ·
    obtain ⟨h2, h3, hG, hR⟩ := rcs_prelude hc hf (profile_ordTrialityD4 hg) hmM hRm
    obtain rfl := rcs_window_d4 hc hf hg hG hR (rcs_first_index hc hf h6 hR) h2 h3
    rfl
  ·
    obtain ⟨h2, h3, hG, hR⟩ := rcs_prelude hc hf (profile_ordF4 hg) hmM hRm
    obtain ⟨hc3, hfg⟩ := rcs_window_f4 hc hf hg hG hR (rcs_first_index hc hf h6 hR) h2 h3
    rcases Nat.lt_or_ge g 2 with hg1 | hg2
    · obtain rfl : g = 1 := by omega
      obtain rfl : f = 4 := by omega
      exact absurd hmM (by decide)
    · rw [hfg] at hmM
      exact absurd hmM (rcs_f4_not_dvd hg2)
  ·
    obtain ⟨h2, h3, hG, hR⟩ := rcs_prelude hc hf (profile_ordTwistedE6 hg) hmM hRm
    exact (rcs_window_2e6 hc hf hg hG hR (rcs_first_index hc hf h6 hR) h2 h3).elim
  ·
    rcases Nat.lt_or_ge f 2 with hf1 | hf2
    · obtain rfl : f = 1 := by omega
      obtain rfl : c = 3 := by rcases hc with h | h <;> [exact h; exact absurd ⟨h, rfl⟩ hne]
      have hp21 : p ∣ 7 := by simpa [phiOrd] using hpΦ
      obtain rfl : p = 7 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).mp hp21
      have h49 : 7 ^ 2 ∣ 6048 := rcs_part_ge hp hM0 (by decide) hpm
      exact absurd h49 (by decide)
    · exact absurd (Nat.le_of_dvd (by norm_num) hRm) (not_le.mpr (rcs_rOrd_big hf2))

end CFSG.RankThree.PartOne.D4RC
