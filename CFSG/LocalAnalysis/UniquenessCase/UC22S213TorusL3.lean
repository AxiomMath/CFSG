module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Prime
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.Adapters.LieModelL3U3Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedTorusL3 (L : Subgroup G) : Prop :=
  ∃ r p f : ℕ, r.Prime ∧ 5 ≤ r ∧ ¬ r ∣ f ∧
    ((r ∣ p ^ f - 1 ∧ LieModel (BarInf L) .PSL 3 p f) ∨
      (r ∣ p ^ f + 1 ∧ LieModel (BarInf L) .PSU 3 p f))

private theorem uc22s213_not_dvd_card_center_of_rank_three (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {t : StatedLieTag} (ht : t = .PSL ∨ t = .PSU)
    {p f r : ℕ} (hX : LieModel (BarInf L) t 3 p f) (hr : r.Prime) (hr5 : 5 ≤ r) :
    ¬ r ∣ Nat.card (center (Bar2 L)) := by
  have hrow := griessRow_of_lieModel_classical hGA hX (by rcases ht with rfl | rfl <;> decide)
  have hg : (genericOrders t 3 p f).1 * (genericOrders t 3 p f).2 ∣ 3 := by
    rcases ht with rfl | rfl <;>
      simpa [genericOrders] using Nat.gcd_dvd_left 3 _
  have he : (exceptionalOrders t 3 p f).1 * (exceptionalOrders t 3 p f).2 ∣ 16 := by
    rcases ht with rfl | rfl <;> unfold exceptionalOrders <;> split <;> simp_all
  have hpos : 0 < ((genericOrders t 3 p f).1 * (genericOrders t 3 p f).2) *
      ((exceptionalOrders t 3 p f).1 * (exceptionalOrders t 3 p f).2) := by
    have h1 : 0 < (genericOrders t 3 p f).1 * (genericOrders t 3 p f).2 :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at hg; omega
    have h2 : 0 < (exceptionalOrders t 3 p f).1 * (exceptionalOrders t 3 p f).2 :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at he; omega
    positivity
  intro hd
  have h48 : r ∣ 3 * 2 ^ 4 :=
    (hd.trans (card_center_bar2_dvd_of_row hL hpos hrow)).trans (Nat.mul_dvd_mul hg he)
  rcases (Nat.Prime.dvd_mul hr).1 h48 with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)
    omega

theorem uc22s213_not_centralizesBar_of_torusL3 (hGA : GriessAllModelsStatement)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable)
    (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hT : S21_3ClosedTorusL3 L) {a : G} (ha : a ∈ c.B)
    (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  obtain ⟨r, p, f, hr, hr5, hrf, ⟨hrd, hX⟩ | ⟨hrd, hX⟩⟩ := hT
  ·
    obtain ⟨hp, hf, -⟩ := hX.admissible
    have hq2 : 2 ≤ p ^ f := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    have hrq : r ≤ p ^ f - 1 := Nat.le_of_dvd (by omega) hrd
    have hrp : r ≠ p := by
      intro hrp
      have h1 : r ∣ p ^ f - (p ^ f - 1) :=
        Nat.dvd_sub (by rw [hrp]; exact dvd_pow_self p (by omega)) hrd
      rw [Nat.sub_sub_self (by omega)] at h1
      exact hr.one_lt.ne' (Nat.dvd_one.1 h1)
    exact uc22s213_not_centralizesBar_of_prime hS hU S hσ hPart hSE hSS hK3 hB hOut Ch hH c hL hr
      hr5 (uc22s213_not_dvd_card_center_of_rank_three hGA hL (.inl rfl) hX hr hr5)
      (hX.two_le_pRank_psl3_of_dvd hr hrd) (hX.isMulCommutative_sylow_psl3 hr hr5 hrp)
      (hX.not_dvd_card_outer_psl3 hr hr5 hrf)
      (hX.three_thousand_six_hundred_lt_card_psl3 (by omega)) ha hpr hN
  ·
    obtain ⟨hp, hf, -⟩ := hX.admissible
    have hrq : r ≤ p ^ f + 1 := Nat.le_of_dvd (by omega) hrd
    have hrp : r ≠ p := by
      intro hrp
      have h1 : r ∣ p ^ f + 1 - p ^ f :=
        Nat.dvd_sub hrd (by rw [hrp]; exact dvd_pow_self p (by omega))
      rw [Nat.add_sub_cancel_left] at h1
      exact hr.one_lt.ne' (Nat.dvd_one.1 h1)
    exact uc22s213_not_centralizesBar_of_prime hS hU S hσ hPart hSE hSS hK3 hB hOut Ch hH c hL hr
      hr5 (uc22s213_not_dvd_card_center_of_rank_three hGA hL (.inr rfl) hX hr hr5)
      (hX.two_le_pRank_psu3_of_dvd hr hrd) (hX.isMulCommutative_sylow_psu3 hr hr5 hrp)
      (hX.not_dvd_card_outer_psu3 hr hr5 hrf)
      (hX.three_thousand_six_hundred_lt_card_psu3 (by omega)) ha hpr hN

end CFSG.LocalAnalysis.UniquenessCase.UC22
