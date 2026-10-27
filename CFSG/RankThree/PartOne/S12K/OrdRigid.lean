module

public import CFSG.RankThree.PartOne.S12K.OrdRigidL
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.S12K

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Assembly.LowTwoRank

theorem ordTwistedA_ne_ordTwistedA_two {n f g : ℕ} (hn : 3 ≤ n) (hf : 1 ≤ f) (hg : 2 ≤ g) :
    ordTwistedA n (2 ^ f) ≠ ordTwistedA 2 (2 ^ g) := by
  intro hm
  obtain ⟨t, ht1, ht⟩ := exists_half (n := n) (by omega)
  have hX := profile_ordTwistedA (n := n) (by omega) hf
  have hf0 : 0 < f * (2 * t + 1) := Nat.mul_pos (by omega) (by omega)
  by_cases hw6 : 2 * (f * (2 * t + 1)) = 6
  · have hf1 : f = 1 := by
      have : f * 3 ≤ f * (2 * t + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    subst hf1
    have ht1' : t = 1 := by omega
    subst ht1'
    have hn3 : n = 3 := by omega
    subst hn3
    have hU := profile_ordTwistedA (n := 2) le_rfl (by omega : 1 ≤ g)
    rw [← hm] at hU
    have hN := (hX.transfer hU).1
    have hg2 : g = 2 := by norm_num at hN; omega
    subst hg2
    revert hm
    decide
  · obtain ⟨hw1, hN, -⟩ := top_eq hX (zU_top ht ht1 (by omega)) (by omega) hw6
      (fun k hk => zU_le ht (by omega) hk) (n := 2) (g := g) (t := 1) le_rfl (by omega) le_rfl
      (Or.inl rfl) (by omega) hm
    have h1 : f * (2 * t + 1) = f * (n * (n + 1) / 2) := by
      norm_num at hN hw1
      omega
    have h2 : 2 * t + 1 = n * (n + 1) / 2 := Nat.eq_of_mul_eq_mul_left (by omega) h1
    rcases ht with rfl | rfl
    · rw [tri_even] at h2
      nlinarith
    · rw [tri_odd] at h2
      nlinarith

theorem ordTwistedA_ne_ordBC_two {u f g : ℕ} (hu : 2 ≤ u) (hf : 1 ≤ f) (hg : 1 ≤ g) :
    ordTwistedA u (2 ^ f) ≠ ordBC 2 (2 ^ g) := by
  intro hm
  obtain ⟨t, ht1, ht⟩ := exists_half (n := u) hu
  have hX := profile_ordTwistedA (n := u) hu hf
  obtain ⟨hN, hZ⟩ := vsSp4 hX hg hm
  have hf0 : 0 < f * (2 * t + 1) := Nat.mul_pos (by omega) (by omega)
  have hw := zU_top (g := f) ht ht1 (by omega)
  by_cases hw6 : 2 * (f * (2 * t + 1)) = 6
  · have hf1 : f = 1 := by
      have : f * 3 ≤ f * (2 * t + 1) := Nat.mul_le_mul_left _ (by omega)
      omega
    subst hf1
    have ht1' : t = 1 := by omega
    subst ht1'
    rcases ht with rfl | rfl <;> norm_num at hN <;> omega
  · have hwd : 2 * (f * (2 * t + 1)) ∣ g * 4 := (hZ _ (by omega) hw6).mp hw
    have h4g : zU u f (g * 4) := (hZ (g * 4) (by omega) (by omega)).mpr dvd_rfl
    have hle := zU_le ht (by omega) h4g
    have hwle := Nat.le_of_dvd (by omega) hwd
    have hk : f * (2 * t + 1) ∣ g * 4 := (Dvd.intro_left 2 rfl).trans hwd
    have hk2 : 2 ≤ f * (2 * t + 1) := by omega
    by_cases hk6 : f * (2 * t + 1) = 6
    · have hf2 : f ≤ 2 := by
        have : f * 3 ≤ f * (2 * t + 1) := Nat.mul_le_mul_left _ (by omega)
        omega
      interval_cases f
      · omega
      · have ht1' : t = 1 := by omega
        subst ht1'
        have hg3 : g = 3 := by omega
        subst hg3
        rcases ht with rfl | rfl
        · norm_num at hN
        · revert hm
          decide
    · exact not_zU_mid ht ht1 (by omega) ((hZ _ hk2 hk6).mpr hk)

theorem ordA_one_inj {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : ordA 1 (2 ^ f) = ordA 1 (2 ^ g)) : f = g := by
  rw [ordA_one_eq hf, ordA_one_eq hg] at h
  exact eq_of_two_pow_mul_odd (odd_pow_sub_one (by omega) (by omega))
    (odd_pow_sub_one (by omega) (by omega)) h

theorem ordTwistedA_two_inj {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : ordTwistedA 2 (2 ^ f) = ordTwistedA 2 (2 ^ g)) : f = g := by
  have hX := profile_ordTwistedA (n := 2) le_rfl hf
  have hY := profile_ordTwistedA (n := 2) le_rfl hg
  rw [← h] at hY
  have := (hX.transfer hY).1
  norm_num at this
  omega

theorem ordBC_two_inj {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : ordBC 2 (2 ^ f) = ordBC 2 (2 ^ g)) : f = g := by
  have hX := profile_ordBC (n := 2) hf
  have hY := profile_ordBC (n := 2) hg
  rw [← h] at hY
  have := (hX.transfer hY).1
  omega

@[expose] def charTwoOrder : StatedLieTag → ℕ → ℕ → ℕ
  | .PSL, n, f => ordA (n - 1) (2 ^ f)
  | .PSU, n, f => ordTwistedA (n - 1) (2 ^ f)
  | .PSp, n, f => ordBC n (2 ^ f)
  | .POmegaOdd, n, f => ordBC n (2 ^ f)
  | .POmegaPlus, n, f => ordD n (2 ^ f)
  | .POmegaMinus, n, f => ordTwistedD n (2 ^ f)
  | .G2, _, f => ordG2 (2 ^ f)
  | .F4, _, f => ordF4 (2 ^ f)
  | .E6, _, f => ordE6 (2 ^ f)
  | .E7, _, f => ordE7 (2 ^ f)
  | .E8, _, f => ordE8 (2 ^ f)
  | .twistedE6, _, f => ordTwistedE6 (2 ^ f)
  | .trialityD4, _, f => ordTrialityD4 (2 ^ f)
  | .twistedB2, _, f => ordSuzuki (2 ^ f)
  | .twistedG2, _, _ => 0
  | .twistedF4, _, f => ordTwistedF4 (2 ^ f)
  | .Tits, _, _ => ordTits

theorem rigid_U {t : StatedLieTag} {n f g : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hg : 2 ≤ g)
    (h : charTwoOrder t n f = ordTwistedA 2 (2 ^ g)) : t = .PSU ∧ n = 3 ∧ f = g := by
  obtain ⟨-, hf, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := hrest
    exact absurd (h : ordA (n - 1) (2 ^ f) = _)
      (ordA_ne_ordTwistedA (by omega) hf le_rfl (by omega))
  case PSU =>
    obtain ⟨hn, -⟩ := hrest
    by_cases hn3 : n = 3
    · subst hn3
      exact ⟨rfl, rfl, ordTwistedA_two_inj hf (by omega) h⟩
    · exact absurd (h : ordTwistedA (n - 1) (2 ^ f) = _)
        (ordTwistedA_ne_ordTwistedA_two (by omega) hf hg)
  case PSp =>
    obtain ⟨hn, -⟩ := hrest
    by_cases hn2 : n = 2
    · subst hn2
      exact absurd (h : ordBC 2 (2 ^ f) = _).symm (ordTwistedA_ne_ordBC_two le_rfl (by omega) hf)
    · exact absurd (h : ordBC n (2 ^ f) = _) (ordBC_ne_ordTwistedA (by omega) hf le_rfl (by omega))
  case POmegaOdd => exact absurd rfl hrest.2
  case POmegaPlus =>
    exact absurd (h : ordD n (2 ^ f) = _) (ordD_ne_ordTwistedA hrest hf le_rfl (by omega))
  case POmegaMinus =>
    exact absurd (h : ordTwistedD n (2 ^ f) = _)
      (ordTwistedD_ne_ordTwistedA hrest hf le_rfl (by omega))
  case G2 =>
    have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact absurd hrest.2 (by norm_num)
    exact absurd (h : ordG2 (2 ^ f) = _) (ordG2_ne_ordTwistedA hf2 le_rfl (by omega))
  case F4 => exact absurd (h : ordF4 (2 ^ f) = _) (ordF4_ne_ordTwistedA hf le_rfl (by omega))
  case E6 => exact absurd (h : ordE6 (2 ^ f) = _) (ordE6_ne_ordTwistedA hf le_rfl (by omega))
  case E7 => exact absurd (h : ordE7 (2 ^ f) = _) (ordE7_ne_ordTwistedA hf le_rfl (by omega))
  case E8 => exact absurd (h : ordE8 (2 ^ f) = _) (ordE8_ne_ordTwistedA hf le_rfl (by omega))
  case twistedE6 =>
    exact absurd (h : ordTwistedE6 (2 ^ f) = _) (ordTwistedE6_ne_ordTwistedA hf le_rfl (by omega))
  case trialityD4 =>
    exact absurd (h : ordTrialityD4 (2 ^ f) = _)
      (ordTrialityD4_ne_ordTwistedA hf le_rfl (by omega))
  case twistedB2 =>
    obtain ⟨-, -, hodd, hf3⟩ := hrest
    exact absurd (h : ordSuzuki (2 ^ f) = _) (ordSuzuki_ne_ordTwistedA hodd hf3 le_rfl (by omega))
  case twistedG2 => exact absurd hrest.2.1 (by norm_num)
  case twistedF4 =>
    exact absurd (h : ordTwistedF4 (2 ^ f) = _) (ordTwistedF4_ne_ordTwistedA hf le_rfl (by omega))
  case Tits => exact absurd (h : ordTits = _) (ordTits_ne_ordTwistedA le_rfl (by omega))

theorem rigid_Sp {t : StatedLieTag} {n f g : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hg : 2 ≤ g)
    (h : charTwoOrder t n f = ordBC 2 (2 ^ g)) : t = .PSp ∧ n = 2 ∧ f = g := by
  obtain ⟨-, hf, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := hrest
    exact absurd (h : ordA (n - 1) (2 ^ f) = _) (ordA_ne_ordBC_two (by omega) hf (by omega))
  case PSU =>
    obtain ⟨hn, -⟩ := hrest
    exact absurd (h : ordTwistedA (n - 1) (2 ^ f) = _)
      (ordTwistedA_ne_ordBC_two (by omega) hf (by omega))
  case PSp =>
    obtain ⟨hn, -⟩ := hrest
    by_cases hn2 : n = 2
    · subst hn2
      exact ⟨rfl, rfl, ordBC_two_inj hf (by omega) h⟩
    · exact absurd (h : ordBC n (2 ^ f) = _) (ordBC_ne_ordBC_two (by omega) hf (by omega))
  case POmegaOdd => exact absurd rfl hrest.2
  case POmegaPlus =>
    exact absurd (h : ordD n (2 ^ f) = _) (ordD_ne_ordBC_two hrest hf (by omega))
  case POmegaMinus =>
    exact absurd (h : ordTwistedD n (2 ^ f) = _) (ordTwistedD_ne_ordBC_two hrest hf (by omega))
  case G2 =>
    have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact absurd hrest.2 (by norm_num)
    exact absurd (h : ordG2 (2 ^ f) = _) (ordG2_ne_ordBC_two hf2 (by omega))
  case F4 => exact absurd (h : ordF4 (2 ^ f) = _) (ordF4_ne_ordBC_two hf (by omega))
  case E6 => exact absurd (h : ordE6 (2 ^ f) = _) (ordE6_ne_ordBC_two hf (by omega))
  case E7 => exact absurd (h : ordE7 (2 ^ f) = _) (ordE7_ne_ordBC_two hf (by omega))
  case E8 => exact absurd (h : ordE8 (2 ^ f) = _) (ordE8_ne_ordBC_two hf (by omega))
  case twistedE6 =>
    exact absurd (h : ordTwistedE6 (2 ^ f) = _) (ordTwistedE6_ne_ordBC_two hf (by omega))
  case trialityD4 =>
    exact absurd (h : ordTrialityD4 (2 ^ f) = _) (ordTrialityD4_ne_ordBC_two hf (by omega))
  case twistedB2 =>
    obtain ⟨-, -, hodd, -⟩ := hrest
    exact absurd (h : ordSuzuki (2 ^ f) = _) (ordSuzuki_ne_ordBC_two hodd (by omega))
  case twistedG2 => exact absurd hrest.2.1 (by norm_num)
  case twistedF4 =>
    obtain ⟨-, -, -, hf3⟩ := hrest
    exact absurd (h : ordTwistedF4 (2 ^ f) = _) (ordTwistedF4_ne_ordBC_two hf3 (by omega))
  case Tits => exact absurd (h : ordTits = _) (ordTits_ne_ordBC_two (by omega))

theorem rigid_L {t : StatedLieTag} {n f g : ℕ} (hadm : StatedLieAdmissible t n 2 f) (hg : 1 ≤ g)
    (h : charTwoOrder t n f = ordA 1 (2 ^ g)) : t = .PSL ∧ n = 2 ∧ f = g := by
  obtain ⟨-, hf, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := hrest
    by_cases hn2 : n = 2
    · subst hn2
      exact ⟨rfl, rfl, ordA_one_inj hf hg h⟩
    · exact absurd (h : ordA (n - 1) (2 ^ f) = _) (ordA_ne_ordA_one (by omega) hf hg)
  case PSU =>
    obtain ⟨hn, -⟩ := hrest
    exact absurd (h : ordTwistedA (n - 1) (2 ^ f) = _).symm
      (ordA_ne_ordTwistedA le_rfl hg (by omega) hf)
  case PSp =>
    obtain ⟨hn, -⟩ := hrest
    exact absurd (h : ordBC n (2 ^ f) = _) (ordBC_ne_ordA_one hn hf hg)
  case POmegaOdd => exact absurd rfl hrest.2
  case POmegaPlus =>
    exact absurd (h : ordD n (2 ^ f) = _) (ordD_ne_ordA_one hrest hf hg)
  case POmegaMinus =>
    exact absurd (h : ordTwistedD n (2 ^ f) = _) (ordTwistedD_ne_ordA_one hrest hf hg)
  case G2 => exact absurd (h : ordG2 (2 ^ f) = _) (ordG2_ne_ordA_one hf hg)
  case F4 => exact absurd (h : ordF4 (2 ^ f) = _) (ordF4_ne_ordA_one hf hg)
  case E6 => exact absurd (h : ordE6 (2 ^ f) = _) (ordE6_ne_ordA_one hf hg)
  case E7 => exact absurd (h : ordE7 (2 ^ f) = _) (ordE7_ne_ordA_one hf hg)
  case E8 => exact absurd (h : ordE8 (2 ^ f) = _) (ordE8_ne_ordA_one hf hg)
  case twistedE6 => exact absurd (h : ordTwistedE6 (2 ^ f) = _) (ordTwistedE6_ne_ordA_one hf hg)
  case trialityD4 => exact absurd (h : ordTrialityD4 (2 ^ f) = _) (ordTrialityD4_ne_ordA_one hf hg)
  case twistedB2 =>
    obtain ⟨-, -, -, hf3⟩ := hrest
    exact absurd (h : ordSuzuki (2 ^ f) = _) (ordSuzuki_ne_ordA_one hf3 hg)
  case twistedG2 => exact absurd hrest.2.1 (by norm_num)
  case twistedF4 => exact absurd (h : ordTwistedF4 (2 ^ f) = _) (ordTwistedF4_ne_ordA_one hf hg)
  case Tits => exact absurd (h : ordTits = _) (ordTits_ne_ordA_one hg)

end CFSG.RankThree.PartOne.S12K
