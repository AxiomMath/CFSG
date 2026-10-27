module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Prime
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Center
import CFSG.Adapters.LieModelL4U4Sp4Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.Assembly.LowTwoRank (StatedLieTag)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable StronglyEmbeddedThree BadNoStrongThree)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3ClosedTorus4 (L : Subgroup G) : Prop :=
  ∃ r p f : ℕ, r.Prime ∧ 5 ≤ r ∧ ¬ r ∣ f ∧
    ((r ∣ p ^ f - 1 ∧ LieModel (BarInf L) .PSL 4 p f) ∨
      (r ∣ p ^ f + 1 ∧ LieModel (BarInf L) .PSU 4 p f) ∨
      ((r ∣ p ^ f - 1 ∨ r ∣ p ^ f + 1) ∧ LieModel (BarInf L) .PSp 2 p f))

theorem uc22s213_not_dvd_card_center_of_four (hGA : GriessAllModelsStatement)
    {M L : Subgroup G} (hL : L ∈ calC M) {t : StatedLieTag} {n : ℕ}
    (ht : (t = .PSL ∧ n = 4) ∨ (t = .PSU ∧ n = 4) ∨ (t = .PSp ∧ n = 2))
    {p f r : ℕ} (hX : LieModel (BarInf L) t n p f) (hr : r.Prime) (hr5 : 5 ≤ r) :
    ¬ r ∣ Nat.card (center (Bar2 L)) := by
  have hrow := griessRow_of_lieModel_classical hGA hX
    (by rcases ht with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide)
  have hg : (genericOrders t n p f).1 * (genericOrders t n p f).2 ∣ 4 := by
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simpa [genericOrders] using Nat.gcd_dvd_left 4 _
    · simpa [genericOrders] using Nat.gcd_dvd_left 4 _
    · simpa [genericOrders] using (Nat.gcd_dvd_left 2 _).trans (by norm_num : 2 ∣ 4)
  have he : (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2 ∣ 36 := by
    rcases ht with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> unfold exceptionalOrders <;>
      split <;> simp_all
  have hpos : 0 < ((genericOrders t n p f).1 * (genericOrders t n p f).2) *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
    have h1 : 0 < (genericOrders t n p f).1 * (genericOrders t n p f).2 :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at hg; omega
    have h2 : 0 < (exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2 :=
      Nat.pos_of_ne_zero fun h0 => by rw [h0] at he; omega
    positivity
  intro hd
  have h144 : r ∣ 4 * 36 :=
    (hd.trans (card_center_bar2_dvd_of_row hL hpos hrow)).trans (Nat.mul_dvd_mul hg he)
  rw [show (4 * 36 : ℕ) = 2 ^ 4 * 3 ^ 2 by norm_num] at h144
  rcases (Nat.Prime.dvd_mul hr).1 h144 with h | h
  · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)
    omega
  · have := Nat.le_of_dvd (by norm_num) (hr.dvd_of_dvd_pow h)
    omega

private theorem uc22s213_ne_of_dvd_pow_sub_or_add {r p f : ℕ} (hr : r.Prime) (hp : p.Prime)
    (hf : 1 ≤ f) (hrd : r ∣ p ^ f - 1 ∨ r ∣ p ^ f + 1) : r ≠ p := by
  intro hrp
  have hq : r ∣ p ^ f := by rw [hrp]; exact dvd_pow_self p (by omega)
  have hq1 : 1 ≤ p ^ f := Nat.one_le_pow _ _ hp.pos
  have h1 : r ∣ 1 := by
    rcases hrd with h | h
    · have h' := Nat.dvd_sub hq h
      rwa [Nat.sub_sub_self hq1] at h'
    · have h' := Nat.dvd_sub h hq
      rwa [Nat.add_sub_cancel_left] at h'
  exact hr.one_lt.ne' (Nat.dvd_one.1 h1)

theorem uc22s213_not_centralizesBar_of_torus4 (hGA : GriessAllModelsStatement)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (hσ : S.InMSigma)
    (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive) (hSS : StronglyEmbeddedSolvable)
    (hK3 : StronglyEmbeddedThree) (hB : BadNoStrongThree)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) (Ch : Choice2011 G)
    (hH : H1930 (UC6.dataOfSetup4 hS hU S)) (c : Ctx21 (UC6.dataOfSetup4 hS hU S) Ch)
    {L : Subgroup G} (hL : L ∈ calC S.M) (hT : S21_3ClosedTorus4 L) {a : G} (ha : a ∈ c.B)
    (hpr : (orderOf a).Prime)
    (hN : ∀ p ∈ uniqueFourSigma S.M,
      CFSG.Open.pRank p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  have key : ∀ {r : ℕ}, r.Prime → 5 ≤ r → ¬ r ∣ Nat.card (center (Bar2 L)) →
      2 ≤ CFSG.Open.pRank r (⊤ : Subgroup (BarInf L)) →
      (∀ P : Sylow r (BarInf L), IsMulCommutative (P : Subgroup (BarInf L))) →
      ¬ r ∣ Nat.card (Outer (BarInf L)) → 3600 < Nat.card (BarInf L) →
      ¬ CentralizesBar a L := fun hr hr5 hZ h2 hab hout h3600 =>
    uc22s213_not_centralizesBar_of_prime hS hU S hσ hPart hSE hSS hK3 hB hOut Ch hH c hL hr hr5
      hZ h2 hab hout h3600 ha hpr hN
  obtain ⟨r, p, f, hr, hr5, hrf, ⟨hrd, hX⟩ | ⟨hrd, hX⟩ | ⟨hrd, hX⟩⟩ := hT
  ·
    obtain ⟨hp, hf, -⟩ := hX.admissible
    exact key hr hr5 (uc22s213_not_dvd_card_center_of_four hGA hL (.inl ⟨rfl, rfl⟩) hX hr hr5)
      (hX.two_le_pRank_psl4_of_dvd hr (by omega) hrd)
      (hX.isMulCommutative_sylow_psl4 hr hr5
        (uc22s213_ne_of_dvd_pow_sub_or_add hr hp hf (.inl hrd)))
      (hX.not_dvd_card_outer_psl4 hr hr5 hrf) hX.three_thousand_six_hundred_lt_card_psl4
  ·
    obtain ⟨hp, hf, -⟩ := hX.admissible
    exact key hr hr5
      (uc22s213_not_dvd_card_center_of_four hGA hL (.inr (.inl ⟨rfl, rfl⟩)) hX hr hr5)
      (hX.two_le_pRank_psu4_of_dvd hr (by omega) hrd)
      (hX.isMulCommutative_sylow_psu4 hr hr5
        (uc22s213_ne_of_dvd_pow_sub_or_add hr hp hf (.inr hrd)))
      (hX.not_dvd_card_outer_psu4 hr hr5 hrf) hX.three_thousand_six_hundred_lt_card_psu4
  ·
    obtain ⟨hp, hf, -⟩ := hX.admissible
    exact key hr hr5
      (uc22s213_not_dvd_card_center_of_four hGA hL (.inr (.inr ⟨rfl, rfl⟩)) hX hr hr5)
      (hX.two_le_pRank_psp4_of_dvd hr (by omega) hrd)
      (hX.isMulCommutative_sylow_psp4 hr hr5 (uc22s213_ne_of_dvd_pow_sub_or_add hr hp hf hrd))
      (hX.not_dvd_card_outer_psp4 hr hr5 hrf) hX.three_thousand_six_hundred_lt_card_psp4

end CFSG.LocalAnalysis.UniquenessCase.UC22
