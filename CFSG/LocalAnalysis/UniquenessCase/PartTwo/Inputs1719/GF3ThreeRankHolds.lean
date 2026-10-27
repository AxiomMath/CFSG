module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieOddRankFourHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3Lie
public import CFSG.LocalAnalysis.GL83PartI.I_24_3.CoverCentre
public import CFSG.ClassicalInvolution.Q3.TL4SecIdLieE

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible)
open CFSG.Blueprint (LieModel)
open OddLie



theorem k_GF3_three_rank_qs_holds : K_GF3_three_rank_qs := by
  intro X _ _ t n hadm hqs hX hrank
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA1 : ¬ (t = .PSL ∧ n = 2) := by
    rintro ⟨rfl, rfl⟩
    exact hadm.2.2.2.2 rfl
  have hRee : t ≠ .twistedG2 := by
    rintro rfl
    obtain ⟨-, -, -, -, -, hf3⟩ := hadm
    omega
  have hfund : CFSG.ClassicalInvolution.Generic.IsFundTag t := by
    cases t
    case twistedB2 => exact absurd hadm.2.2.2.1 (by norm_num)
    case twistedF4 => exact absurd hadm.2.2.2.1 (by norm_num)
    case Tits => exact absurd hadm.2.2.2.1 (by norm_num)
    case twistedG2 => exact absurd rfl hRee
    all_goals trivial
  by_cases hL3 : (t = .PSL ∨ t = .PSU) ∧ n = 3
  · obtain ⟨ht, rfl⟩ := hL3
    have hZ : Subgroup.center X = ⊥ := by
      obtain ⟨ψ, hψs, hψk⟩ := exists_cover_of_lieModel_three_full hfund hadm hqs hX
        (by rcases ht with rfl | rfl <;> decide)
      have hZU : Subgroup.center
          (CFSG.ClassicalInvolution.Generic.modelUniv t 3 3 1 Nat.prime_three).K = ⊥ := by
        rcases ht with rfl | rfl
        · exact CFSG.ClassicalInvolution.Q3.TL4.center_modelUniv_psl_three _
        · exact CFSG.ClassicalInvolution.Q3.TL4.center_modelUniv_psu_three _
      have hUq := (CFSG.ClassicalInvolution.ModelFacts.modelClauseZero t 3 3 1 Nat.prime_three
        hfund hadm).1
      have : Group.IsPerfect
          (CFSG.ClassicalInvolution.Generic.modelUniv t 3 3 1 Nat.prime_three).K := ⟨hUq.1⟩
      rw [← CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel ψ hψs hψk, hZU,
        Subgroup.map_bot]
    have hXm := CFSG.Blueprint.LieModel.of_quotient_center hZ hX
    rcases ht with rfl | rfl
    · exact Or.inl hXm
    · exact Or.inr hXm
  · exfalso
    have hA2 : ¬ ((t = .PSL ∨ t = .PSU) ∧ n = 3 ∧ 1 = 1) := fun h => hL3 ⟨h.1, h.2.1⟩
    obtain ⟨h3, h4⟩ := three_le_pRank_of_lieModel_odd Nat.prime_three (by norm_num) hX hA1 hA2
      hRee
    by_cases hZ : 3 ∣ Nat.card (Subgroup.center X)
    · obtain ⟨-, -, hex⟩ := small_three_of_dvd Nat.prime_three (by norm_num) hfund hadm hqs hX
        hA1 hZ
      rcases hex with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | rfl | ⟨rfl, rfl⟩
      · have h3' := Nat.le_of_dvd (by norm_num) (hZ.trans (card_center_dvd_two_psp43 hqs hX))
        omega
      ·
        have hqK := GL83.I243.Cover.isQuasisimple_quotient (p := 3) hqs
        obtain ⟨eK⟩ := GL83.I243.Cover.nonempty_equiv_center_quotient (p := 3) hqs
        have hN : ¬ 3 ∣ Nat.card (GL83.I243.Cover.primeCentre 3 X) :=
          (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
            GL83.I243.Cover.coprime_card_primeCentre
        have hrk := CFSG.SectionRank.pRank_quotient_eq (p := 3) (GL83.I243.Cover.primeCentre 3 X) hN
        have h6 := card_center_dvd_six_o73 hqK eK hX
        obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1
          (GL83.I243.Cover.isPGroup_center_quotient (p := 3) hqs)
        have hk1 : k ≤ 1 := by
          by_contra hk2
          have h9 : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 (by omega)
          rw [← hk] at h9
          have := Nat.le_of_dvd (by norm_num) (h9.trans h6)
          norm_num at this
        interval_cases k
        · have hZK : ¬ 3 ∣ Nat.card (Subgroup.center (X ⧸ GL83.I243.Cover.primeCentre 3 X)) := by
            rw [hk]
            norm_num
          have e1 :=
            CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
              Nat.prime_three hZK
          have e2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) eK
          rcases h4 with ⟨h, -⟩ | h4
          · simp at h
          · omega
        · have := CFSG.HardMathSupport.Timmesfeld.FieldBonus.six_le_pRank_of_lieModel_O7 hqK eK hX
            (by rw [hk]; norm_num)
          omega
      · obtain ⟨-, -, rfl, -⟩ := hadm
        have := CFSG.HardMathSupport.Timmesfeld.FieldBonus.four_le_pRank_of_lieModel_G2
          (MulEquiv.refl _) hX hZ
        omega
      · have := CFSG.HardMathSupport.Timmesfeld.FieldBonus.five_le_pRank_of_lieModel_U43
          (MulEquiv.refl _) hX hZ
        omega
    · rw [← CFSG.HardMathSupport.Timmesfeld.ComponentBalance.pRank_quotient_center_eq_of_not_dvd
        Nat.prime_three hZ] at hrank
      omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
