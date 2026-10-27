module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213TorusL3
public import CFSG.LocalAnalysis.UniquenessCase.UC22S213U3
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.LocalAnalysis.UniquenessCase.UC22S213PrimeRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Assembly.LowTwoRank (StatedLieTag)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_not_dvd_card_center_of_rank_three_odd (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ}
    (hp2 : p ≠ 2) (hX : LieModel (BarInf L) t 3 p f) : ¬ p ∣ Nat.card (center (Bar2 L)) := by
  obtain ⟨hp, hf, -⟩ := hX.admissible
  have hrow := griessRow_of_lieModel_classical hGA hX (by rcases ht with rfl | rfl <;> decide)
  have hg : (genericOrders t 3 p f).1 * (genericOrders t 3 p f).2 ∣ 3 := by
    rcases ht with rfl | rfl <;>
      simpa [genericOrders] using Nat.gcd_dvd_left 3 _
  have he : (exceptionalOrders t 3 p f).1 * (exceptionalOrders t 3 p f).2 = 1 := by
    rcases ht with rfl | rfl
    · unfold exceptionalOrders
      split <;> simp_all
    · rfl
  have hpos : 0 < ((genericOrders t 3 p f).1 * (genericOrders t 3 p f).2) *
      ((exceptionalOrders t 3 p f).1 * (exceptionalOrders t 3 p f).2) := by
    rw [he, mul_one]
    obtain ⟨k, hk⟩ := hg
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, zero_mul] at hk; omega
  have hdvd := card_center_bar2_dvd_of_row hL hpos hrow
  rw [he, mul_one] at hdvd
  intro hpZ
  have hp3 : p ∣ 3 := hpZ.trans (hdvd.trans hg)
  have hp_eq : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp hp3
  subst hp_eq
  rcases ht with rfl | rfl
  · have h3d : 3 ∣ 3 ^ f - 1 := by
      have := hpZ.trans hdvd
      simp only [genericOrders, mul_one] at this
      exact this.trans (Nat.gcd_dvd_right 3 _)
    have h1 : 3 ∣ 3 ^ f - (3 ^ f - 1) :=
      Nat.dvd_sub (dvd_pow_self 3 (by omega)) h3d
    rw [Nat.sub_sub_self (Nat.one_le_pow f 3 (by norm_num))] at h1
    exact absurd h1 (by norm_num)
  · have h3d : 3 ∣ 3 ^ f + 1 := by
      have := hpZ.trans hdvd
      simp only [genericOrders, mul_one] at this
      exact this.trans (Nat.gcd_dvd_right 3 _)
    have h1 : 3 ∣ 3 ^ f + 1 - 3 ^ f :=
      Nat.dvd_sub h3d (dvd_pow_self 3 (by omega))
    rw [Nat.add_sub_cancel_left] at h1
    exact absurd h1 (by norm_num)

private theorem uc22s213_four_le_pRank_of_lieModel_three {X : Type} [Group X] [Finite X]
    {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ} (hp2 : p ≠ 2) (hf : 2 ≤ f)
    (hX : LieModel X t 3 p f) : 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨-, -, hr⟩ := CFSG.SectionRank.classical_model_rank hp2
    (hX.statedClassicalModel_of_ne_zero (by norm_num))
  rcases ht with rfl | rfl
  · rcases hr with ⟨-, h | h | h⟩ | ⟨h, -⟩ | ⟨h, -⟩ | h
    · omega
    · omega
    · exact h
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  · rcases hr with ⟨h, -⟩ | ⟨-, h | h⟩ | ⟨h, -⟩ | h
    · exact absurd h (by decide)
    · omega
    · exact h
    · exact absurd h (by decide)
    · exact h

theorem uc22s213_closed2_of_rank_three_odd (hGA : GriessAllModelsStatement) {M L : Subgroup G}
    (hL : L ∈ calC M) {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU) {p f : ℕ} (hp2 : p ≠ 2)
    (hf : 2 ≤ f) (hX : LieModel (BarInf L) t 3 p f) : S21_3Closed2 L := by
  obtain ⟨hp, -, -⟩ := hX.admissible
  have hZ := uc22s213_not_dvd_card_center_of_rank_three_odd hGA hL ht hp2 hX
  have h4 := uc22s213_four_le_pRank_of_lieModel_three ht hp2 hf hX
  refine Or.inl ⟨p, hp, hp2, ?_⟩
  rw [← uc22s213_pRank_barInf_of_prime hL.2.2 hp hp2 hZ]
  exact h4

theorem uc22s213_closedTorusL3_of_psl3_two {L : Subgroup G} {n : ℕ} (hn : 3 ≤ n)
    (hX : LieModel (BarInf L) .PSL 3 2 n) : S21_3ClosedTorusL3 L := by
  rcases eq_or_ne n 6 with rfl | hn6
  · exact ⟨7, 2, 6, by norm_num, by norm_num, by norm_num, Or.inl ⟨by norm_num, hX⟩⟩
  · obtain ⟨r, hr, hrd, hprim⟩ :=
      CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one n (by omega) hn6
    have hpp : CFSG.Timmesfeld.IsPrimitivePrimeDivisor r n := ⟨hr, hrd, hprim⟩
    have hnr : n < r := uc22p22i_lt_of_primitive hpp (by omega)
    have hr5 : 5 ≤ r := by
      refine hr.five_le_of_ne_two_of_ne_three (hpp.ne_two (by omega)) ?_
      intro h3
      have := hpp.eq_two_of_dvd_three (by omega) (by rw [h3])
      omega
    refine ⟨r, 2, n, hr, hr5, ?_, Or.inl ⟨hrd, hX⟩⟩
    intro hrn
    have := Nat.le_of_dvd (by omega : 0 < n) hrn
    omega

theorem uc22s213_closedU3_of_psu3_two {L : Subgroup G} {n : ℕ} (hn : 2 ≤ n) (hn3 : n ≠ 3)
    (hX : LieModel (BarInf L) .PSU 3 2 n) : S21_3ClosedU3 L := by
  obtain ⟨r, hpp⟩ :=
    CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 2 * n) (by omega) (by omega)
  have hk : 0 < 2 * n := by omega
  have hr3 : 3 < r := by
    have h2 := hpp.ne_two hk
    have h3 : r ≠ 3 := by
      intro h3
      have := hpp.eq_two_of_dvd_three hk (by rw [h3])
      omega
    have := hpp.prime.two_le
    omega
  have hq : r ∣ 2 ^ n + 1 := by
    have hfac := CFSG.Timmesfeld.IsPrimitivePrimeDivisor.two_pow_two_mul_sub_one n
    have hd : r ∣ (2 ^ n - 1) * (2 ^ n + 1) := by
      rw [← hfac]
      exact hpp.dvd
    rcases hpp.prime.dvd_mul.mp hd with h | h
    · have hdvd : 2 * n ∣ n := (hpp.dvd_sub_one_iff hk n).mp h
      have := Nat.le_of_dvd (by omega : 0 < n) hdvd
      omega
    · exact h
  exact ⟨n, r, hX, hpp.prime, hr3, hq⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
