module

public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionRestAltBound
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionSeitzExcOrder
public import CFSG.LocalAnalysis.StandardType.GGKGroupFusionAltFamily

public section

namespace CFSG.StandardType

open CFSG.Open CFSG.Timmesfeld CFSG.Timmesfeld.Orders CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.Blueprint
open CFSG.RankThree.PartOne.S12K (charTwoOrder card_of_lieModel_two)
open CFSG.RankThree.PartOne.FLM (profile_exp_eq ten_le_tri)
open scoped Nat

theorem ggTwo_pow_lt_factorial {M : ℕ} (hM : 13 ≤ M) : 2 ^ (3 * M + 1) < (M + 2)! := by
  induction M, hM using Nat.le_induction with
  | base => decide
  | succ M hM ih =>
    calc 2 ^ (3 * (M + 1) + 1) = 2 ^ (3 * M + 1) * 8 := by ring
      _ < (M + 2)! * 8 := Nat.mul_lt_mul_of_pos_right ih (by norm_num)
      _ ≤ (M + 2)! * (M + 2 + 1) := Nat.mul_le_mul_left _ (by omega)
      _ = (M + 1 + 2)! := by
        rw [mul_comm]
        exact (Nat.factorial_succ (M + 2)).symm

theorem ggFactorial_div_two_of_bound {m N r : ℕ} (hm7 : 7 ≤ m) (hm8 : m ≠ 8) (hr : Odd r)
    (he : m ! / 2 = 2 ^ N * r) (hle : m ! / 2 ≤ 2 ^ (3 * N)) :
    (m = 9 ∧ N = 6) ∨ (m = 10 ∧ N = 7) := by
  have hk! : m ! = 2 * (m ! / 2) :=
    (Nat.mul_div_cancel' (Nat.dvd_factorial (by norm_num) (by omega))).symm
  have hdvd2 : 2 ^ (N + 1) ∣ m ! := by
    rw [hk!, he, pow_succ]
    exact ⟨r, by ring⟩
  have hlt : N + 1 < m := by
    have h1 := Nat.emultiplicity_two_factorial_lt (show m ≠ 0 by omega)
    have h2 := le_emultiplicity_of_pow_dvd hdvd2
    exact_mod_cast lt_of_le_of_lt h2 h1
  have hfac : (N + 2)! ≤ m ! := Nat.factorial_le (by omega)
  have hkle : m ! ≤ 2 ^ (3 * N + 1) := by
    rw [hk!, pow_succ]
    omega
  have hN12 : N ≤ 12 := by
    by_contra h
    have := ggTwo_pow_lt_factorial (show 13 ≤ N by omega)
    omega
  have hm15 : m ≤ 15 := by
    by_contra h
    have h1 : (16 : ℕ)! ≤ m ! := Nat.factorial_le (by omega)
    have h2 : 2 ^ (3 * N + 1) ≤ 2 ^ 37 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 2 ^ 37 < (16 : ℕ)! := by decide
    omega
  have hval : ∀ a s : ℕ, Odd s → m ! / 2 = 2 ^ a * s → N = a := fun a s hs h =>
    eq_of_two_pow_mul_odd hr hs (he.symm.trans h)
  interval_cases m
  · obtain rfl := hval 3 315 (by decide) (by decide)
    exact absurd hle (by decide)
  · exact absurd rfl hm8
  · exact Or.inl ⟨rfl, hval 6 2835 (by decide) (by decide)⟩
  · exact Or.inr ⟨rfl, hval 7 14175 (by decide) (by decide)⟩
  · obtain rfl := hval 7 155925 (by decide) (by decide)
    exact absurd hle (by decide)
  · obtain rfl := hval 9 467775 (by decide) (by decide)
    exact absurd hle (by decide)
  · obtain rfl := hval 9 6081075 (by decide) (by decide)
    exact absurd hle (by decide)
  · obtain rfl := hval 10 42567525 (by decide) (by decide)
    exact absurd hle (by decide)
  · obtain rfl := hval 10 638512875 (by decide) (by decide)
    exact absurd hle (by decide)

theorem ggProfile_exp_alt {m N : ℕ} {Z : ℕ → Prop} (h : Profile m N Z) :
    (m = 181440 → N = 6) ∧ (m = 1814400 → N = 7) :=
  ⟨fun hm => profile_exp_eq h (r := 2835) (by decide) (by rw [hm]; norm_num),
    fun hm => profile_exp_eq h (r := 14175) (by decide) (by rw [hm]; norm_num)⟩

theorem ggCharTwoOrder_ne_alt {t : LowTwoRank.StatedLieTag} {n f : ℕ}
    (hadm : LowTwoRank.StatedLieAdmissible t n 2 f) :
    charTwoOrder t n f ≠ 181440 ∧ charTwoOrder t n f ≠ 1814400 := by
  obtain ⟨-, hf, hrest⟩ := hadm
  cases t
  case PSL =>
    obtain ⟨hn, -⟩ := hrest
    have hP := ggProfile_exp_alt (profile_ordA (n := n - 1) (by omega) hf)
    change ordA (n - 1) (2 ^ f) ≠ 181440 ∧ ordA (n - 1) (2 ^ f) ≠ 1814400
    have h10 : 5 ≤ n → 10 ≤ (n - 1) * (n - 1 + 1) / 2 := ten_le_tri
    have hmul : (n - 1) * (n - 1 + 1) / 2 ≤ f * ((n - 1) * (n - 1 + 1) / 2) :=
      Nat.le_mul_of_pos_left _ hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := hP.1 h
      rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | h5
      · obtain rfl : f = 6 := by norm_num at hN; omega
        revert h; decide
      · obtain rfl : f = 2 := by norm_num at hN; omega
        revert h; decide
      · obtain rfl : f = 1 := by norm_num at hN; omega
        revert h; decide
      · have := h10 h5; omega
    · have hN := hP.2 h
      rcases (show n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | rfl | h5
      · obtain rfl : f = 7 := by norm_num at hN; omega
        revert h; decide
      · norm_num at hN; omega
      · norm_num at hN; omega
      · have := h10 h5; omega
  case PSU =>
    obtain ⟨hn, -⟩ := hrest
    have hP := ggProfile_exp_alt (profile_ordTwistedA (n := n - 1) (by omega) hf)
    change ordTwistedA (n - 1) (2 ^ f) ≠ 181440 ∧ ordTwistedA (n - 1) (2 ^ f) ≠ 1814400
    have h10 : 5 ≤ n → 10 ≤ (n - 1) * (n - 1 + 1) / 2 := ten_le_tri
    have hmul : (n - 1) * (n - 1 + 1) / 2 ≤ f * ((n - 1) * (n - 1 + 1) / 2) :=
      Nat.le_mul_of_pos_left _ hf
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := hP.1 h
      rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
      · obtain rfl : f = 2 := by norm_num at hN; omega
        revert h; decide
      · obtain rfl : f = 1 := by norm_num at hN; omega
        revert h; decide
      · have := h10 h5; omega
    · have hN := hP.2 h
      rcases (show n = 3 ∨ n = 4 ∨ 5 ≤ n by omega) with rfl | rfl | h5
      · norm_num at hN; omega
      · norm_num at hN; omega
      · have := h10 h5; omega
  case PSp =>
    obtain ⟨hn, -⟩ := hrest
    have hP := ggProfile_exp_alt (profile_ordBC (n := n) hf)
    change ordBC n (2 ^ f) ≠ 181440 ∧ ordBC n (2 ^ f) ≠ 1814400
    have hmul : n * n ≤ f * (n * n) := Nat.le_mul_of_pos_left _ hf
    have hsq : n = 2 ∨ 9 ≤ n * n := by
      rcases (show n = 2 ∨ 3 ≤ n by omega) with h2 | h3
      · exact Or.inl h2
      · exact Or.inr (Nat.mul_le_mul h3 h3)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · have hN := hP.1 h
      rcases hsq with rfl | h9
      · omega
      · omega
    · have hN := hP.2 h
      rcases hsq with rfl | h9
      · omega
      · omega
  case POmegaOdd => exact absurd rfl hrest.2
  case POmegaPlus =>
    have hP := ggProfile_exp_alt (profile_ordD (n := n) (by omega) hf)
    change ordD n (2 ^ f) ≠ 181440 ∧ ordD n (2 ^ f) ≠ 1814400
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hrest (by omega)
    have hmul : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case POmegaMinus =>
    have hP := ggProfile_exp_alt (profile_ordTwistedD (n := n) (by omega) hf)
    change ordTwistedD n (2 ^ f) ≠ 181440 ∧ ordTwistedD n (2 ^ f) ≠ 1814400
    have h12 : 4 * 3 ≤ n * (n - 1) := Nat.mul_le_mul hrest (by omega)
    have hmul : n * (n - 1) ≤ f * (n * (n - 1)) := Nat.le_mul_of_pos_left _ hf
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case G2 =>
    have hP := ggProfile_exp_alt (profile_ordG2 hf)
    have hf2 : 2 ≤ f := by
      by_contra hlt
      obtain rfl : f = 1 := by omega
      exact absurd hrest.2 (by norm_num)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case F4 =>
    have hP := ggProfile_exp_alt (profile_ordF4 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case E6 =>
    have hP := ggProfile_exp_alt (profile_ordE6 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case E7 =>
    have hP := ggProfile_exp_alt (profile_ordE7 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case E8 =>
    have hP := ggProfile_exp_alt (profile_ordE8 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case twistedE6 =>
    have hP := ggProfile_exp_alt (profile_ordTwistedE6 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case trialityD4 =>
    have hP := ggProfile_exp_alt (profile_ordTrialityD4 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case twistedB2 =>
    obtain ⟨-, -, -, hf3⟩ := hrest
    have hP := ggProfile_exp_alt (profile_ordSuzuki hf)
    change ordSuzuki (2 ^ f) ≠ 181440 ∧ ordSuzuki (2 ^ f) ≠ 1814400
    refine ⟨fun h => ?_, fun h => by have := hP.2 h; omega⟩
    have hN := hP.1 h
    obtain rfl : f = 3 := by omega
    revert h; decide
  case twistedG2 => exact absurd hrest.2.1 (by norm_num)
  case twistedF4 =>
    have hP := ggProfile_exp_alt (profile_ordTwistedF4 hf)
    exact ⟨fun h => by have := hP.1 h; omega, fun h => by have := hP.2 h; omega⟩
  case Tits =>
    change ordTits ≠ 181440 ∧ ordTits ≠ 1814400
    decide

theorem ggCharTwoOrder_ne_factorial_div_two {t : LowTwoRank.StatedLieTag} {n f m : ℕ}
    (hadm : LowTwoRank.StatedLieAdmissible t n 2 f) (hm7 : 7 ≤ m) (hm8 : m ≠ 8) :
    charTwoOrder t n f ≠ m ! / 2 := by
  intro h
  obtain ⟨N, r, hr, he, hle⟩ := ggCharTwoOrder_bound hadm
  rw [h] at he hle
  rcases ggFactorial_div_two_of_bound hm7 hm8 hr he hle with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact (ggCharTwoOrder_ne_alt hadm).1 (h.trans (by decide))
  · exact (ggCharTwoOrder_ne_alt hadm).2 (h.trans (by decide))

section Marked


theorem ggMarkedModel_card_ne_factorial_div_two {lab : LargeEvenLabel} {R : Type} [Group R]
    (h : MarkedModel lab R) {m : ℕ} (hm7 : 7 ≤ m) (hm8 : m ≠ 8) : Nat.card R ≠ m ! / 2 := by
  have h7 : 7 ! / 2 ≤ m ! / 2 := Nat.div_le_div_right (Nat.factorial_le hm7)
  have h7' : (7 : ℕ)! / 2 = 2520 := by decide
  obtain ⟨t, l, n⟩ := lab
  cases t
  case B2der =>
    obtain ⟨e⟩ := nonempty_alternatingGroup_of_markedModel_b2der rfl h
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    have h6 : (6 : ℕ)! / 2 = 360 := by decide
    omega
  case G2der =>
    have hR : Nat.card R = 6048 := by
      dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
      rcases h with ⟨-, -, K, _, _, hK, ⟨e⟩⟩ | ⟨hn, -⟩ | ⟨hn, -⟩ | ⟨hn, -⟩
      · rw [Nat.card_congr e.toEquiv,
          CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_three le_rfl hK
            (by norm_num)]
        decide
      all_goals exact absurd hn (by norm_num)
    rw [hR]
    rcases (show m = 7 ∨ 8 ≤ m by omega) with rfl | h8
    · decide
    · have h8' : 8 ! / 2 ≤ m ! / 2 := Nat.div_le_div_right (Nat.factorial_le h8)
      have h8'' : (8 : ℕ)! / 2 = 20160 := by decide
      omega
  all_goals
    dsimp only [MarkedModel, markTag, markRank, markChar, markDeg] at h
    obtain ⟨hadm, hcard⟩ := card_of_lieModel_two h
    rw [hcard]
    exact ggCharTwoOrder_ne_factorial_div_two hadm hm7 hm8

theorem ggAltNotMarkedInput : GGAltNotMarkedInput := by
  intro m hm7 hm8 L _ ⟨e⟩ P hmark
  obtain ⟨lab, -, hM⟩ := largeEvenMarking_markedModel_centerQuot hmark
  apply ggMarkedModel_card_ne_factorial_div_two hM hm7 hm8
  have hZ : Subgroup.center L = ⊥ := by
    have h4 : 4 ≤ Nat.card (Fin m) := by rw [Nat.card_fin]; omega
    have hc := alternatingGroup.center_eq_bot h4
    rw [eq_bot_iff]
    intro z hz
    have hz' : e z ∈ Subgroup.center (alternatingGroup (Fin m)) :=
      (MulEquivClass.apply_mem_center_iff e).2 hz
    rw [hc, Subgroup.mem_bot] at hz'
    exact Subgroup.mem_bot.2 (e.injective (hz'.trans (map_one e).symm))
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZ).trans
      QuotientGroup.quotientBot).toEquiv, Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
    Nat.card_fin]

end Marked

end CFSG.StandardType
