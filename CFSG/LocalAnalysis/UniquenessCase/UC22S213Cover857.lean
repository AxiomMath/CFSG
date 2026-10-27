module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213L2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213TorusL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213U3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Torus4
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Char
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Small
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213U54
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.Adapters.LieModelTorusRank
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Arith
import CFSG.LocalAnalysis.UniquenessCase.UC22S213L3Cover
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P20e
import CFSG.Adapters.StatedPSLTwoSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {G : Type} [Group G] [Finite G]

private theorem uc22s213_generic_pos {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp) (hp : p.Prime) (hf : 1 ≤ f) :
    0 < (genericOrders t n p f).1 * (genericOrders t n p f).2 := by
  have h2 : 2 ≤ p ^ f := by
    calc 2 ≤ p := hp.two_le
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.one_le hf
  have hq : 0 < p ^ f - 1 := by omega
  have hq' : 0 < p ^ f + 1 := by omega
  rcases ht with rfl | rfl | rfl
  · simpa [genericOrders] using Nat.gcd_pos_of_pos_right n hq
  · simp [genericOrders]
  · simp [genericOrders]

private theorem uc22s213_card_center_dvd_generic (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {t : StatedLieTag} {n p f : ℕ}
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp)
    (hX : LieModel (BarInf L) t n p f) (he : exceptionalOrders t n p f = (1, 1)) :
    Nat.card (center (Bar2 L)) ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  have hrow := griessRow_of_lieModel_classical hGA hX
    (by rcases ht with rfl | rfl | rfl <;> decide)
  have hpos : 0 < ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
    rw [he]
    simpa using uc22s213_generic_pos ht hp hf
  have h := card_center_bar2_dvd_of_row hL hpos hrow
  simpa [he] using h

theorem uc22s213_not_dvd_card_center_of_char (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp) {n p f : ℕ}
    (hX : LieModel (BarInf L) t n p f) (he : exceptionalOrders t n p f = (1, 1)) :
    ¬ p ∣ Nat.card (center (Bar2 L)) := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  have hZ := uc22s213_card_center_dvd_generic hGA hL ht hX he
  intro hpZ
  have hpg : p ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 := hpZ.trans hZ
  have hpow : p ∣ p ^ f := dvd_pow_self p (by omega)
  rcases ht with rfl | rfl | rfl
  · have hd : p ∣ p ^ f - 1 := by
      exact hpg.trans (by simpa [genericOrders] using Nat.gcd_dvd_right n (p ^ f - 1))
    have h1 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpow hd
    rw [Nat.sub_sub_self (Nat.one_le_pow f p hp.pos)] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · have hd : p ∣ p ^ f + 1 := by
      exact hpg.trans (by simpa [genericOrders] using Nat.gcd_dvd_right n (p ^ f + 1))
    have h1 : p ∣ p ^ f + 1 - p ^ f := Nat.dvd_sub hd hpow
    rw [Nat.add_sub_cancel_left] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  · have hd : p ∣ p ^ f - 1 := by
      exact hpg.trans (by simpa [genericOrders] using Nat.gcd_dvd_right 2 (p ^ f - 1))
    have h1 : p ∣ p ^ f - (p ^ f - 1) := Nat.dvd_sub hpow hd
    rw [Nat.sub_sub_self (Nat.one_le_pow f p hp.pos)] at h1
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)

theorem uc22s213_not_dvd_card_center_of_not_dvd (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU)
    {n p f r : ℕ} (hX : LieModel (BarInf L) t n p f)
    (he : exceptionalOrders t n p f = (1, 1)) (hrn : ¬ r ∣ n) :
    ¬ r ∣ Nat.card (center (Bar2 L)) := by
  have ht3 : t = .PSL ∨ t = .PSU ∨ t = .PSp := by
    rcases ht with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hZ := uc22s213_card_center_dvd_generic hGA hL ht3 hX he
  intro hrZ
  have hrg : r ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 := hrZ.trans hZ
  apply hrn
  rcases ht with rfl | rfl
  · exact hrg.trans (by simpa [genericOrders] using Nat.gcd_dvd_left n (p ^ f - 1))
  · exact hrg.trans (by simpa [genericOrders] using Nat.gcd_dvd_left n (p ^ f + 1))

theorem uc22s213_not_threeCover_barInf {M L : Subgroup G} (hL : L ∈ calC M)
    (S : ∀ (Y : Type) [Group Y], Prop) : ¬ UCK.ThreeCover S (BarInf L) := by
  intro h
  obtain ⟨-, hcard, -⟩ := h
  have hbot : center (BarInf L) = ⊥ := by
    obtain ⟨hsimp, a, b, hab⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
    rcases hsimp.eq_bot_or_eq_top_of_normal (center (BarInf L)) with h | h
    · exact h
    · have hb : b ∈ center (BarInf L) := by
        rw [h]
        exact mem_top b
      exact absurd ((mem_center_iff.mp hb) a) hab
  rw [hbot, Subgroup.card_bot] at hcard
  norm_num at hcard

theorem uc22s213_closed_of_psl4 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {p f : ℕ} (hq : p ^ f % 3 = 2) (hX : LieModel (BarInf L) .PSL 4 p f) :
    S21_3ClosedZ L ∨ S21_3Closed2 L ∨ S21_3ClosedTorus4 L := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  rcases eq_or_lt_of_le hp.two_le with h2 | h3
  ·
    have hp2 : p = 2 := h2.symm
    subst hp2
    by_cases hf1 : f = 1
    · subst hf1
      exact Or.inl (Or.inl ⟨8, by norm_num,
        CFSG.GH74.Exceptional.nonempty_mulEquiv_alternating_eight_of_lieModel hX⟩)
    · have hf2 : 2 ≤ f := by omega
      have hf3 : 3 ≤ f := by
        rcases Nat.lt_or_ge f 3 with h | h
        · interval_cases f; norm_num at hq
        · exact h
      have hf6 : f ≠ 6 := by
        rintro rfl
        norm_num at hq
      obtain ⟨r, hr, hrd, hprim⟩ :=
        CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one f (by omega) hf6
      have hpp : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r f := ⟨hr, hrd, hprim⟩
      have hfr : f < r := uc22p22i_lt_of_primitive hpp (by omega)
      have hr2 : r ≠ 2 := hpp.ne_two (by omega)
      have hr3 : r ≠ 3 := by
        intro h3
        have hk2 : f = 2 := hpp.eq_two_of_dvd_three (by omega) (by rw [h3])
        omega
      have hr5 : 5 ≤ r := hr.five_le_of_ne_two_of_ne_three hr2 hr3
      refine Or.inr (Or.inr ⟨r, 2, f, hr, hr5, ?_, Or.inl ⟨hrd, hX⟩⟩)
      intro hrf
      have hle := Nat.le_of_dvd (by omega : 0 < f) hrf
      omega
  ·
    by_cases hp_eq : p = 3
    · subst hp_eq
      have h0 : 3 ^ f % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 3 (by omega))
      omega
    · have hp5 : 5 ≤ p := by
        rcases hp.eq_two_or_odd' with h2 | ho
        · omega
        · obtain ⟨k, hk⟩ := ho
          omega
      have he : exceptionalOrders .PSL 4 p f = (1, 1) := by
        unfold exceptionalOrders
        split <;> simp_all
      have hZ := uc22s213_not_dvd_card_center_of_char hGA hL (Or.inl rfl) hX he
      refine Or.inr (Or.inl (Or.inl ⟨p, hp, by omega, ?_⟩))
      have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
        obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by omega : p ≠ 2)
          (hX.statedClassicalModel_of_ne_zero (by omega : 4 ≠ 0))
        rcases hr with ⟨-, ⟨h2, h⟩ | ⟨h3, h⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
        · omega
        · omega
        · exact h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · exact h
      rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp (by omega) hZ]
      exact h4

theorem uc22s213_closed_of_psu4 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {p f : ℕ} (hq : p ^ f % 3 = 1) (hX : LieModel (BarInf L) .PSU 4 p f) :
    S21_3Closed2 L ∨ S21_3ClosedTorus4 L := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  rcases eq_or_lt_of_le hp.two_le with h2 | h3
  ·
    have hp2 : p = 2 := h2.symm
    subst hp2
    have hf1 : f ≠ 1 := by
      intro h
      rw [h] at hq
      norm_num at hq
    have hf2 : 2 ≤ f := by omega
    have hf3 : f ≠ 3 := by
      intro h
      rw [h] at hq
      norm_num at hq
    have hk2 : 2 ≤ 2 * f := by omega
    have hk6 : 2 * f ≠ 6 := by omega
    obtain ⟨r, hpp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor hk2 hk6
    have h2f : 0 < 2 * f := by omega
    have hr2 : r ≠ 2 := hpp.ne_two h2f
    have hr3 : r ≠ 3 := by
      intro h3
      have := hpp.eq_two_of_dvd_three h2f (by rw [h3])
      omega
    have hr5 : 5 ≤ r := hpp.prime.five_le_of_ne_two_of_ne_three hr2 hr3
    have hfr : f < r := by
      have := uc22p22i_lt_of_primitive hpp h2f
      omega
    have hq1 : r ∣ 2 ^ f + 1 := by
      have hfac := CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one f
      have hd : r ∣ (2 ^ f - 1) * (2 ^ f + 1) := by
        rw [← hfac]
        exact hpp.dvd
      rcases hpp.prime.dvd_mul.mp hd with h | h
      · have hdvd : 2 * f ∣ f := (hpp.dvd_sub_one_iff h2f f).mp h
        have := Nat.le_of_dvd (by omega : 0 < f) hdvd
        omega
      · exact h
    refine Or.inr ⟨r, 2, f, hpp.prime, hr5, ?_, Or.inr (Or.inl ⟨hq1, hX⟩)⟩
    intro hrf
    have hle := Nat.le_of_dvd (by omega : 0 < f) hrf
    omega
  ·
    by_cases hp_eq : p = 3
    · subst hp_eq
      have h0 : 3 ^ f % 3 = 0 := Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 3 (by omega))
      omega
    · have hp5 : 5 ≤ p := by
        rcases hp.eq_two_or_odd' with h2 | ho
        · omega
        · obtain ⟨k, hk⟩ := ho
          omega
      have he : exceptionalOrders .PSU 4 p f = (1, 1) := by
        unfold exceptionalOrders
        split <;> simp_all
      have hZ := uc22s213_not_dvd_card_center_of_char hGA hL (Or.inr (Or.inl rfl)) hX he
      refine Or.inl (Or.inl ⟨p, hp, by omega, ?_⟩)
      have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
        obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by omega : p ≠ 2)
          (hX.statedClassicalModel_of_ne_zero (by omega : 4 ≠ 0))
        rcases hr with ⟨h, -⟩ | ⟨-, ⟨h2, h⟩ | h⟩ | ⟨h, -⟩ | h
        · exact absurd h (by decide)
        · omega
        · exact h
        · exact absurd h (by decide)
        · exact h
      rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp (by omega) hZ]
      exact h4

theorem uc22s213_closed_of_psp4 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) (h3 : CFSG.Open.pRank 3 L ≤ 2) {p f : ℕ}
    (hX : LieModel (BarInf L) .PSp 2 p f) :
    S21_3Closed2 L ∨ S21_3ClosedTorus4 L ∨ S21_3ClosedChar M L := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  have hq2 : p ^ f ≠ 2 := fun h => (hX.admissible).2.2.2 (by rw [h])
  rcases eq_or_lt_of_le hp.two_le with h2 | h3p
  ·
    have hp2 : p = 2 := h2.symm
    subst hp2
    have hf1 : f ≠ 1 := by
      intro h
      exact hq2 (by rw [h]; norm_num)
    have hf2 : 2 ≤ f := by omega
    by_cases hf3 : f = 3
    · subst hf3
      exact Or.inr (Or.inl ⟨7, 2, 3, by norm_num, by norm_num, by norm_num,
        Or.inr (Or.inr ⟨Or.inl (by norm_num), hX⟩)⟩)
    · have hk2 : 2 ≤ 2 * f := by omega
      have hk6 : 2 * f ≠ 6 := by omega
      obtain ⟨r, hpp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor hk2 hk6
      have h2f : 0 < 2 * f := by omega
      have hr2 : r ≠ 2 := hpp.ne_two h2f
      have hr3 : r ≠ 3 := by
        intro h3
        have := hpp.eq_two_of_dvd_three h2f (by rw [h3])
        omega
      have hr5 : 5 ≤ r := hpp.prime.five_le_of_ne_two_of_ne_three hr2 hr3
      have hfr : f < r := by
        have := uc22p22i_lt_of_primitive hpp h2f
        omega
      have hq1 : r ∣ 2 ^ f + 1 := by
        have hfac := CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one f
        have hd : r ∣ (2 ^ f - 1) * (2 ^ f + 1) := by
          rw [← hfac]
          exact hpp.dvd
        rcases hpp.prime.dvd_mul.mp hd with h | h
        · have hdvd : 2 * f ∣ f := (hpp.dvd_sub_one_iff h2f f).mp h
          have := Nat.le_of_dvd (by omega : 0 < f) hdvd
          omega
        · exact h
      refine Or.inr (Or.inl ⟨r, 2, f, hpp.prime, hr5, ?_,
        Or.inr (Or.inr ⟨Or.inr hq1, hX⟩)⟩)
      intro hrf
      have hle := Nat.le_of_dvd (by omega : 0 < f) hrf
      omega
  ·
    by_cases hp_eq : p = 3
    ·
      exfalso
      subst hp_eq
      have he : exceptionalOrders .PSp 2 3 f = (1, 1) := by
        simp [exceptionalOrders]
      have hZ := uc22s213_not_dvd_card_center_of_char hGA hL (Or.inr (Or.inr rfl)) hX he
      have h3r : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) := by
        obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by norm_num : (3 : ℕ) ≠ 2)
          (hX.statedClassicalModel_of_ne_zero (by omega : 2 ≠ 0))
        rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | h
        · exact absurd h (by decide)
        · exact absurd h (by decide)
        · omega
        · omega
        · omega
      rw [uc22s213_pRank_barInf_of_prime hL.2.2 Nat.prime_three (by norm_num) hZ] at h3r
      omega
    · have hp5 : 5 ≤ p := by
        rcases hp.eq_two_or_odd' with h2 | ho
        · omega
        · obtain ⟨k, hk⟩ := ho
          omega
      by_cases hf1 : f = 1
      · subst hf1
        exact Or.inr (Or.inr ⟨p, hp5, Or.inl hX⟩)
      · have hf2 : 2 ≤ f := by omega
        have he : exceptionalOrders .PSp 2 p f = (1, 1) := by
          unfold exceptionalOrders
          split <;> simp_all
        have hZ := uc22s213_not_dvd_card_center_of_char hGA hL (Or.inr (Or.inr rfl)) hX he
        refine Or.inl (Or.inl ⟨p, hp, by omega, ?_⟩)
        have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
          obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank (by omega : p ≠ 2)
            (hX.statedClassicalModel_of_ne_zero (by omega : 2 ≠ 0))
          rcases hr with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, ⟨-, h⟩ | h⟩ | h
          · exact absurd h (by decide)
          · exact absurd h (by decide)
          · exact le_trans (by omega : 4 ≤ 3 * f) h
          · exact h
          · exact h
        rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp (by omega) hZ]
        exact h4

theorem uc22s213_closed_of_rank_three (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ}
    (hX : LieModel (BarInf L) t 3 p f) :
    S21_3Closed2 L ∨ S21_3ClosedL2 L ∨ S21_3ClosedTorusL3 L ∨ S21_3ClosedU3 L ∨
      S21_3ClosedChar M L ∨ S21_3ClosedSmall M L ∨
      (t = .PSL ∧ p = 2 ∧ f = 2) ∨ (t = .PSU ∧ p = 2 ∧ f = 3) ∨
      (p ≠ 2 ∧ f = 1 ∧ 3 ≤ CFSG.Open.pRank p M) := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  by_cases hp2 : p = 2
  · subst hp2
    rcases ht with rfl | rfl
    ·
      by_cases hf1 : f = 1
      · subst hf1
        refine Or.inr (Or.inl ⟨7, 1, by norm_num, by norm_num, ?_⟩)
        exact Or.inl ⟨by decide,
          CFSG.Open.StatedAPI.statedClassicalModel_psl_two_seven_of_psl_three_two
            (hX.statedClassicalModel_of_ne_zero (by norm_num))⟩
      · by_cases hf2 : f = 2
        · subst hf2
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨rfl, rfl, rfl⟩))))))
        · have hf3 : 3 ≤ f := by omega
          exact Or.inr (Or.inr (Or.inl (uc22s213_closedTorusL3_of_psl3_two hf3 hX)))
    ·
      by_cases hf1 : f = 1
      · exfalso
        subst hf1
        exact (hX.admissible).2.2.2 (by norm_num)
      · by_cases hf3 : f = 3
        · subst hf3
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inl ⟨rfl, rfl, rfl⟩)))))))
        · have hf2 : 2 ≤ f := by omega
          exact Or.inr (Or.inr (Or.inr (Or.inl
            (uc22s213_closedU3_of_psu3_two hf2 hf3 hX))))
  ·
    by_cases hf1 : f = 1
    · subst hf1
      by_cases hm : 3 ≤ CFSG.Open.pRank p M
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          ⟨hp2, rfl, hm⟩)))))))
      · have hm2 : CFSG.Open.pRank p M ≤ 2 := by omega
        have hp3 : 3 ≤ p := by
          have := hp.two_le
          omega
        rcases eq_or_lt_of_le hp3 with h3 | h5
        ·
          have hp_eq : p = 3 := h3.symm
          subst hp_eq
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_)))))
          refine ⟨?_, hm2⟩
          rcases ht with rfl | rfl
          · exact Or.inl hX
          · exact Or.inr (Or.inl hX)
        ·
          have hp5 : 5 ≤ p := by
            rcases hp.eq_two_or_odd' with h2 | ho
            · omega
            · obtain ⟨k, hk⟩ := ho
              omega
          refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
          refine ⟨p, hp5, ?_⟩
          rcases ht with rfl | rfl
          · exact Or.inr ⟨Or.inl hX, hm2⟩
          · exact Or.inr ⟨Or.inr hX, hm2⟩
    · have hf2 : 2 ≤ f := by omega
      exact Or.inl (uc22s213_closed2_of_rank_three_odd hGA hL ht hp2 hf2 hX)

theorem uc22s213_closed_of_psl5 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {p f : ℕ} (hX : LieModel (BarInf L) .PSL 5 p f) :
    S21_3ClosedZ L ∨ S21_3Closed2 L := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hf1 : f = 1
    · subst hf1
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hX)))))))
    ·
      have hf2 : 2 ≤ f := by omega
      have hpow : 4 ≤ 2 ^ f := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
      have hne1 : 2 ^ f - 1 ≠ 1 := by omega
      have hsprime : (2 ^ f - 1).minFac.Prime := Nat.minFac_prime hne1
      have hsdvd : (2 ^ f - 1).minFac ∣ 2 ^ f - 1 := Nat.minFac_dvd _
      have hev : Even (2 ^ f) := (Nat.even_pow' (by omega : f ≠ 0)).mpr even_two
      have hoddn : Odd (2 ^ f - 1) := Nat.Even.sub_odd Nat.one_le_two_pow hev odd_one
      have hs2 : (2 ^ f - 1).minFac ≠ 2 := by
        intro h2
        have h2d : 2 ∣ 2 ^ f - 1 := by rwa [h2] at hsdvd
        exact hoddn.not_two_dvd_nat h2d
      have hs5 : (2 ^ f - 1).minFac ≠ 5 := by
        by_cases hfe : Even f
        ·
          have h3d : 3 ∣ 2 ^ f - 1 := by
            have := Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.mp hfe)
            simpa using this
          have hle : (2 ^ f - 1).minFac ≤ 3 := Nat.minFac_le_of_dvd (by norm_num) h3d
          have hge : 3 ≤ (2 ^ f - 1).minFac := by
            have := hsprime.two_le
            omega
          omega
        ·
          have hfo : Odd f := Nat.not_even_iff_odd.mp hfe
          have h5d : ¬ 5 ∣ 2 ^ f - 1 := by
            have hmod := CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.two_pow_mod_five hfo
            intro h5
            have h1 : 2 ^ f % 5 = 1 := by
              have h0 : (2 ^ f - 1) % 5 = 0 := Nat.dvd_iff_mod_eq_zero.mp h5
              have hsplit : 2 ^ f = (2 ^ f - 1) + 1 := by omega
              rw [hsplit, Nat.add_mod, h0]
            rcases hmod with hmod | hmod <;> omega
          intro h5
          rw [h5] at hsdvd
          exact h5d hsdvd
      have hs5' : ¬ (2 ^ f - 1).minFac ∣ 5 := fun hd =>
        hs5 ((Nat.prime_dvd_prime_iff_eq hsprime Nat.prime_five).mp hd)
      have he : exceptionalOrders .PSL 5 2 f = (1, 1) := rfl
      have hZ := uc22s213_not_dvd_card_center_of_not_dvd hGA hL (Or.inl rfl) hX he hs5'
      refine Or.inr (Or.inl ⟨(2 ^ f - 1).minFac, hsprime, hs2, ?_⟩)
      rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hsprime hs2 hZ]
      exact CFSG.Blueprint.LieModel.le_pRank_psl_of_dvd hX hsprime hsdvd (by norm_num)
        (Or.inr hs5')
  ·
    have he : exceptionalOrders .PSL 5 p f = (1, 1) := rfl
    have hZ := uc22s213_not_dvd_card_center_of_char hGA hL (Or.inl rfl) hX he
    refine Or.inr (Or.inl ⟨p, hp, hp2, ?_⟩)
    have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
      obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
        (hX.statedClassicalModel_of_ne_zero (by omega : 5 ≠ 0))
      rcases hr with ⟨-, ⟨h2, h⟩ | ⟨h3, h⟩ | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
      · omega
      · omega
      · exact h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
      · exact h
    rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
    exact h4

theorem uc22s213_closed_of_psu5 (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {p f : ℕ} (hX : LieModel (BarInf L) .PSU 5 p f) :
    S21_3Closed2 L ∨ S21_3ClosedU54 L := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  by_cases hp2 : p = 2
  · subst hp2
    by_cases hf2 : f = 2
    · subst hf2
      exact Or.inr hX
    · by_cases hfe : Even f
      ·
        have hf4 : 4 ≤ f := by
          rcases hfe with ⟨k, hk⟩
          omega
        have hk2 : 2 ≤ 2 * f := by omega
        have hk6 : 2 * f ≠ 6 := by omega
        obtain ⟨r, hpp⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor hk2 hk6
        have h2f : 0 < 2 * f := by omega
        have hdvd : r ∣ 2 ^ f + 1 := by
          have hfac := CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one f
          have hd : r ∣ (2 ^ f - 1) * (2 ^ f + 1) := by
            rw [← hfac]
            exact hpp.dvd
          rcases hpp.prime.dvd_mul.mp hd with h | h
          · have hdvd' : 2 * f ∣ f := (hpp.dvd_sub_one_iff h2f f).mp h
            have := Nat.le_of_dvd (by omega : 0 < f) hdvd'
            omega
          · exact h
        have hr5 : r ≠ 5 := by
          intro h5
          exact hpp.2.2 4 (by norm_num) (by omega) (by rw [h5]; norm_num)
        have hr5' : ¬ r ∣ 5 := fun hd =>
          hr5 ((Nat.prime_dvd_prime_iff_eq hpp.prime Nat.prime_five).mp hd)
        have hev : Even (2 ^ f) := (Nat.even_pow' (by omega : f ≠ 0)).mpr even_two
        have hodd : Odd (2 ^ f + 1) := hev.add_one
        have hr2 : r ≠ 2 := by
          intro h2
          have h2d : 2 ∣ 2 ^ f + 1 := by rwa [h2] at hdvd
          exact hodd.not_two_dvd_nat h2d
        have he : exceptionalOrders .PSU 5 2 f = (1, 1) := rfl
        have hZ := uc22s213_not_dvd_card_center_of_not_dvd hGA hL (Or.inr rfl) hX he
          hr5'
        refine Or.inl (Or.inl ⟨r, hpp.prime, hr2, ?_⟩)
        rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hpp.prime hr2 hZ]
        exact CFSG.Blueprint.LieModel.le_pRank_psu_of_dvd hX hpp.prime hdvd (by norm_num)
          (Or.inr hr5')
      ·
        have hfo : Odd f := Nat.not_even_iff_odd.mp hfe
        have h3mod : 2 ^ f % 3 = 2 :=
          CFSG.SignalizerFunctorTheorem.McBride.NearSolvable.two_pow_mod_three hfo
        have h3d : 3 ∣ 2 ^ f + 1 := by
          rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h3mod]
        have he : exceptionalOrders .PSU 5 2 f = (1, 1) := rfl
        have hZ := uc22s213_not_dvd_card_center_of_not_dvd hGA hL (Or.inr rfl) hX he
          (by norm_num : ¬ (3 : ℕ) ∣ 5)
        refine Or.inl (Or.inl ⟨3, Nat.prime_three, by norm_num, ?_⟩)
        rw [← uc22s213_pRank_barInf_of_prime hL.2.2 Nat.prime_three (by norm_num) hZ]
        exact CFSG.Blueprint.LieModel.le_pRank_psu_of_dvd hX Nat.prime_three h3d (by norm_num)
          (Or.inr (by norm_num : ¬ (3 : ℕ) ∣ 5))
  ·
    have he : exceptionalOrders .PSU 5 p f = (1, 1) := rfl
    have hZ := uc22s213_not_dvd_card_center_of_char hGA hL (Or.inr (Or.inl rfl)) hX he
    refine Or.inl (Or.inl ⟨p, hp, hp2, ?_⟩)
    have h4 : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup (BarInf L)) := by
      obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
        (hX.statedClassicalModel_of_ne_zero (by omega : 5 ≠ 0))
      rcases hr with ⟨h, -⟩ | ⟨-, ⟨h2, h⟩ | h⟩ | ⟨h, -⟩ | h
      · exact absurd h (by decide)
      · omega
      · exact h
      · exact absurd h (by decide)
      · exact h
    rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
    exact h4

theorem uc22s213_closed_of_list857_lie (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) (h3 : CFSG.Open.pRank 3 L ≤ 2)
    (h : (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (BarInf L) .PSL 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (BarInf L) .PSU 4 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ (LieModel (BarInf L) .PSL 5 p f ∨
        UCK.ThreeCover (fun Y _ => LieModel Y .PSL 5 p f) (BarInf L))) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ (LieModel (BarInf L) .PSU 5 p f ∨
        UCK.ThreeCover (fun Y _ => LieModel Y .PSU 5 p f) (BarInf L))) ∨
      (∃ p f : ℕ, LieModel (BarInf L) .PSp 2 p f)) :
    S21_3ClosedZ L ∨ S21_3Closed2 L ∨ S21_3ClosedTorus4 L ∨ S21_3ClosedChar M L ∨
      S21_3ClosedU54 L := by
  rcases h with ⟨p, f, hmod, hX⟩ | ⟨p, f, hmod, hX⟩ |
    ⟨p, f, hmod, hX | hcov⟩ | ⟨p, f, hmod, hX | hcov⟩ | ⟨p, f, hX⟩
  · rcases uc22s213_closed_of_psl4 hGA hL hmod hX with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases uc22s213_closed_of_psu4 hGA hL hmod hX with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  · rcases uc22s213_closed_of_psl5 hGA hL hX with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact absurd hcov
      (uc22s213_not_threeCover_barInf hL (fun Y _ => LieModel Y .PSL 5 p f))
  · rcases uc22s213_closed_of_psu5 hGA hL hX with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact absurd hcov
      (uc22s213_not_threeCover_barInf hL (fun Y _ => LieModel Y .PSU 5 p f))
  · rcases uc22s213_closed_of_psp4 hGA hL h3 hX with h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
