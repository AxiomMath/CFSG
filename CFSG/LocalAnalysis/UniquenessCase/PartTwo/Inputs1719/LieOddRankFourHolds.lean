module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieCover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFunRank
public import CFSG.HardMathSupport.Timmesfeld.FieldBonus.TFAbMainExc
public import CFSG.HardMathSupport.Timmesfeld.Tables.T1b.CoverSplit
public import CFSG.LieType.Steinberg.CentralExt.GriessClassicalSmall
public import CFSG.LieType.Steinberg.CentralExt.GriessOmegaSevenThree
public import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.ABGLocalTools (IsSylowOf)
open scoped commutatorElement

section RankTable

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)


theorem three_le_pRank_of_lieModel_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {L : Type}
    [Group L] [Finite L] {t : StatedLieTag} {n f : ℕ} (h : CFSG.Blueprint.LieModel L t n p f)
    (hA1 : ¬ (t = .PSL ∧ n = 2)) (hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ f = 1))
    (hRee : t ≠ .twistedG2) :
    3 ≤ CFSG.Open.pRank p (⊤ : Subgroup L) ∧
      (((t = .PSp ∧ n = 2) ∨ t = .G2) ∧ f = 1 ∨ 4 ≤ CFSG.Open.pRank p (⊤ : Subgroup L)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hadm := h.admissible
  have hf : 1 ≤ f := hadm.2.1
  rcases h with ⟨-, hcl⟩ | ⟨-, ht, hmod⟩ | ⟨-, ht, hmod⟩ | ⟨-, rfl, -⟩
  · obtain ⟨-, -, hcases⟩ := CFSG.SectionRank.classical_model_rank hp2 hcl
    rcases hcases with ⟨rfl, ⟨rfl, -⟩ | ⟨rfl, h1⟩ | h1⟩ | ⟨rfl, ⟨rfl, h1⟩ | h1⟩ |
      ⟨rfl, ⟨rfl, h1⟩ | h1⟩ | h1
    · exact absurd ⟨rfl, rfl⟩ hA1
    · have hf2 : f ≠ 1 := fun hf1 => hA2 ⟨Or.inl rfl, rfl, hf1⟩
      exact ⟨by omega, Or.inr (by omega)⟩
    · exact ⟨by omega, Or.inr h1⟩
    · have hf2 : f ≠ 1 := fun hf1 => hA2 ⟨Or.inr rfl, rfl, hf1⟩
      exact ⟨by omega, Or.inr (by omega)⟩
    · exact ⟨by omega, Or.inr h1⟩
    · by_cases hf1 : f = 1
      · exact ⟨by omega, Or.inl ⟨Or.inl ⟨rfl, rfl⟩, hf1⟩⟩
      · exact ⟨by omega, Or.inr (by omega)⟩
    · exact ⟨by omega, Or.inr h1⟩
    · exact ⟨by omega, Or.inr h1⟩
  · have hcases : t = .G2 ∨ t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6 ∨
        t = .trialityD4 := by
      revert ht; cases t <;> decide
    obtain ⟨-, hm⟩ := hmod
    rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .G2 (p ^ f) := hm
      have := CFSG.SectionRank.three_mul_le_pRank_of_G2Model h2
      by_cases hf1 : f = 1
      · exact ⟨by omega, Or.inl ⟨Or.inr rfl, hf1⟩⟩
      · exact ⟨by omega, Or.inr (by omega)⟩
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .F4 (p ^ f) := hm
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (by simp) h2
      exact ⟨by omega, Or.inr (by omega)⟩
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .E6 (p ^ f) := hm
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (by simp) h2
      exact ⟨by omega, Or.inr (by omega)⟩
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .E7 (p ^ f) := hm
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (by simp) h2
      exact ⟨by omega, Or.inr (by omega)⟩
    · have h2 : CFSG.Blueprint.UntwistedChevalleyModel L .E8 (p ^ f) := hm
      have := CFSG.SectionRank.four_mul_le_pRank_of_untwistedModel (by simp) h2
      exact ⟨by omega, Or.inr (by omega)⟩
    · have h2 : CFSG.Blueprint.TwistedChevalleyModel L .E6 (p ^ f) := hm
      have := CFSG.SectionRank.four_le_pRank_of_twistedE6Model hf h2
      exact ⟨by omega, Or.inr this⟩
    · have h2 : CFSG.Blueprint.TwistedChevalleyModel L .D4 (p ^ f) := hm
      have := CFSG.SectionRank.four_le_pRank_of_trialityD4Model hf h2
      exact ⟨by omega, Or.inr this⟩
  · exfalso
    have hcases : t = .twistedG2 ∨ t = .twistedF4 ∨ t = .Tits := by
      revert ht; cases t <;> decide
    rcases hcases with rfl | rfl | rfl
    · exact hRee rfl
    · obtain ⟨-, -, -, hp2', -, -⟩ := hadm
      exact hp2 hp2'
    · obtain ⟨-, -, -, hp2', -⟩ := hadm
      exact hp2 hp2'
  · exfalso
    obtain ⟨-, -, -, hp2', -, -⟩ := hadm
    exact hp2 hp2'

end RankTable

open CFSG.Blueprint.Multiplier in
open CFSG.RankThree.PerfectCover (hopfMultiplier hopfMultiplierEquivGriess) in
theorem center_dvd_of_row {K Y : Type} [Group K] [Finite K] [Group Y] (hq : CFSG.IsQuasisimple K)
    (e : K ⧸ Subgroup.center K ≃* Y) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hrow : commutator Y = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier Y ≃* generic t n p f × exceptional t n p f)) :
    Nat.card (Subgroup.center K) ∣ (genericOrders t n p f).1 * (genericOrders t n p f).2 *
      ((exceptionalOrders t n p f).1 * (exceptionalOrders t n p f).2) := by
  obtain ⟨-, ⟨eg⟩⟩ := hrow
  let e' : hopfMultiplier Y ≃* generic t n p f × exceptional t n p f :=
    (hopfMultiplierEquivGriess Y).symm.trans eg
  have h1 := CFSG.GH74.Generic.card_center_dvd_hopfMultiplier hq e
  rw [Nat.card_congr e'.toEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod] at h1
  simpa [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod] using h1

section GriessRows

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)


theorem card_center_dvd_two_psp43 {X : Type} [Group X] [Finite X]
    (hqs : CFSG.Open.IsQuasisimple X) (hX : LieModel (X ⧸ Subgroup.center X) .PSp 2 3 1) :
    Nat.card (Subgroup.center X) ∣ 2 := by
  have h := center_dvd_of_row
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.isQuasisimple_of_open' hqs)
    (MulEquiv.refl _) (CFSG.LieType.Steinberg.CentralExt.GriessClassical.psp_four_three_row
      (CFSG.Models.LieModel.of_blueprint_of_ne_zero (by norm_num) hX))
  simpa [genericOrders, exceptionalOrders] using h

theorem card_center_dvd_six_o73 {K Y : Type} [Group K] [Finite K] [Group Y]
    (hqs : CFSG.Open.IsQuasisimple K) (e : K ⧸ Subgroup.center K ≃* Y)
    (hY : LieModel Y .POmegaOdd 3 3 1) : Nat.card (Subgroup.center K) ∣ 6 := by
  have h := center_dvd_of_row
    (CFSG.HardMathSupport.Timmesfeld.Tables.T1b.isQuasisimple_of_open' hqs)
    e (CFSG.LieType.Steinberg.CentralExt.GriessClassical.pomegaOdd_three_three_row
      (CFSG.Models.LieModel.of_blueprint_of_ne_zero (by norm_num) hY))
  simpa [genericOrders, exceptionalOrders] using h

end GriessRows

section RankFour

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL2Over17 IsL3EpsOdd17 IsReeOver17)


theorem small_three_of_dvd {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n r f : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t)
    (hadm : StatedLieAdmissible t n r f) (hqs : CFSG.Open.IsQuasisimple X)
    (hX : LieModel (X ⧸ Subgroup.center X) t n r f) (hA1 : ¬ (t = .PSL ∧ n = 2))
    (hZ : r ∣ Nat.card (Subgroup.center X)) :
    r = 3 ∧ f = 1 ∧ IsSmallThreeTag t n := by
  by_contra hcon
  apply not_dvd_card_center_of_lieModel hr hr2 hfund hadm hqs hX _ hZ
  by_cases h5 : 5 ≤ r ^ f
  · exact Or.inl ⟨h5, hA1⟩
  · right
    have hf : 1 ≤ f := hadm.2.1
    have hrf : r ≤ r ^ f := Nat.le_self_pow (by omega) r
    obtain ⟨k, hk⟩ : Odd r := hr.eq_two_or_odd'.resolve_left hr2
    have h2 := hr.two_le
    have hr3 : r = 3 := by omega
    subst hr3
    have hf1 : f = 1 := by
      by_contra hne
      have h9 : 9 ≤ 3 ^ f :=
        calc 9 = 3 ^ 2 := by norm_num
          _ ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact ⟨rfl, hf1, fun h => hcon ⟨rfl, hf1, h⟩⟩

end RankFour

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLie

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL2Over17 IsL3EpsOdd17 IsReeOver17)
open OddLie



theorem k_LieOddRankFour_holds : K_LieOddRankFour := by
  intro X _ _ r q hr hr2 ⟨t, n, f, hadm, hq, hX⟩ hqs hodd hL2 hL3 hRee
  have : Fact r.Prime := ⟨hr⟩
  have hf : 1 ≤ f := hadm.2.1
  have hfund := isFundTag_of_not_ree hr2 hadm hq hqs hX hRee
  have hRee' : t ≠ .twistedG2 := by
    rintro rfl
    exact hfund
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hL2 ⟨r, f, hr, hr2, hq, hf, hX⟩
  have hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ f = 1) := by
    rintro ⟨rfl | rfl, rfl, rfl⟩
    · exact hL3 (Or.inl hX)
    · exact hL3 (Or.inr hX)
  obtain ⟨-, h4⟩ := three_le_pRank_of_lieModel_odd hr hr2 hX hA1 hA2 hRee'
  by_cases hZ : r ∣ Nat.card (Subgroup.center X)
  · left
    obtain ⟨rfl, rfl, hex⟩ := small_three_of_dvd hr hr2 hfund hadm hqs hX hA1 hZ
    rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | ⟨rfl, rfl⟩
    · exfalso
      have h3 := Nat.le_of_dvd (by norm_num) (hZ.trans (card_center_dvd_two_psp43 hqs hX))
      omega
    · have h6 := card_center_dvd_six_o73 hqs (MulEquiv.refl _) hX
      have hZ3 : Nat.card (Subgroup.center X) = 3 := by
        have hle := Nat.le_of_dvd (by norm_num) h6
        obtain ⟨k, hk⟩ := hodd
        obtain ⟨m, hm⟩ := hZ
        omega
      exact le_trans (by norm_num)
        (CFSG.HardMathSupport.Timmesfeld.FieldBonus.six_le_pRank_of_lieModel_O7 hqs
          (MulEquiv.refl _) hX hZ3)
    · obtain ⟨-, -, rfl, -⟩ := hadm
      exact CFSG.HardMathSupport.Timmesfeld.FieldBonus.four_le_pRank_of_lieModel_G2
        (MulEquiv.refl _) hX hZ
    · exact le_trans (by norm_num)
        (CFSG.HardMathSupport.Timmesfeld.FieldBonus.five_le_pRank_of_lieModel_U43
          (MulEquiv.refl _) hX hZ)
  · rw [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd hr
      hZ]
    rcases h4 with ⟨hexc, rfl⟩ | h4
    · right
      refine ⟨by rw [hq, pow_one], ?_, hZ⟩
      rcases hexc with ⟨rfl, rfl⟩ | rfl
      · exact Or.inr hX
      · obtain ⟨-, -, rfl, -⟩ := hadm
        exact Or.inl hX
    · exact Or.inl h4

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
