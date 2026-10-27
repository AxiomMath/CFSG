module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicLocal17
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicRankData
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2HoldsSpor
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

section Certificates



theorem k_SporadicCoverThreeRank_holds :
    K_SporadicCoverThreeRank := by
  intro X _ _ s hq hodd hF h2
  obtain ⟨e⟩ := hF
  have hperf : Group.IsPerfect X := (Group.isPerfect_def).2 hq.1
  have hdvd := CFSG.Quasithin.B69K.OddCovers.card_center_dvd_hopfMultiplier hperf e
  rw [CFSG.OddStandard.HigherRank.YamadaG23.l2Sporadic_holds s] at hdvd
  have h12 : Nat.card (Subgroup.center X) ∣ 12 :=
    hdvd.trans (sporadicMultiplierOrder_dvd_twelve s)
  by_cases hZ : Subgroup.center X = ⊥
  ·
    have htop : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) =
        CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
        (QuotientGroup.quotientMulEquivOfEq (G := X) hZ)]
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num)
        (QuotientGroup.quotientBot (G := X))]
    omega
  ·
    have hodd' : Odd (Nat.card (Subgroup.center X)) := hodd
    have hcop : Nat.Coprime (Nat.card (Subgroup.center X)) 2 :=
      (Nat.coprime_two_right).mpr hodd'
    have hdvd3 : Nat.card (Subgroup.center X) ∣ 3 := by
      have hd12 : Nat.card (Subgroup.center X) ∣ 2 * (2 * 3) := by simpa using h12
      exact hcop.dvd_of_dvd_mul_left (hcop.dvd_of_dvd_mul_left hd12)
    have hZcard : Nat.card (Subgroup.center X) = 3 := by
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
      · exact absurd h1 fun h => hZ (Subgroup.card_eq_one.mp h)
      · exact h3
    have h3dvd : 3 ∣ Nat.card (Subgroup.center X) := by rw [hZcard]
    have h9 : ¬ 9 ∣ Nat.card (Subgroup.center X) := by rw [hZcard]; norm_num
    have hbound :=
      CFSG.HardMathSupport.Timmesfeld.Coordinator.pRank_centerQuotient_le_of_center
        Nat.prime_three (by norm_num) h3dvd h9
    have hs : s = .M22 ∨ s = .J3 ∨ s = .McL ∨ s = .Suz ∨ s = .ONan ∨ s = .Fi22 ∨
        s = .Fi24Prime := by
      apply CFSG.HardMathSupport.Timmesfeld.Coordinator.eq_of_three_dvd_sporadicMultiplierOrder
      have hfun : CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder s =
          CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.sporadicMultiplierOrder s := by
        cases s <;> rfl
      rw [hfun, hZcard] at hdvd
      exact hdvd
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    ·
      have : Finite (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
        Finite.of_equiv _ e.toEquiv
      have hle2 : CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) ≤ 2 := by
        rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
        exact CFSG.HardMathSupport.Timmesfeld.SporadicRank.pRank_le_of_not_dvd
          (p := 3) (k := 2) Nat.prime_three (by
            have hc : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M22) = 443520 :=
              CFSG.HardMathSupport.Timmesfeld.Coordinator.card_nativeM22
            rw [hc]; norm_num)
      omega
    ·
      have hJ3 : 3 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup X) := by
        obtain ⟨b⟩ := CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
        exact CFSG.HardMathSupport.Timmesfeld.Coordinator.j3CoverRank_holds X hq ⟨e.trans b⟩
          hZcard
      omega
    ·
      have hge : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
        obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.McL_elementary_three_rank_four
        exact CFSG.HardMathSupport.Timmesfeld.Coordinator.le_pRank_of_mulEquiv
          (p := 3) (k := 4) (by norm_num) e.symm hE hcard
      have h2le : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) / 2 := by
        have := Nat.div_le_div_right (c := 2) hge
        norm_num at this ⊢
        exact this
      omega
    ·
      have hge : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
        obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Suz_elementary_three_rank_four
        exact CFSG.HardMathSupport.Timmesfeld.Coordinator.le_pRank_of_mulEquiv
          (p := 3) (k := 4) (by norm_num) e.symm hE hcard
      have h2le : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) / 2 := by
        have := Nat.div_le_div_right (c := 2) hge
        norm_num at this ⊢
        exact this
      omega
    ·
      have hge : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
        obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.ON_elementary_three_rank_four
        exact CFSG.HardMathSupport.Timmesfeld.Coordinator.le_pRank_of_mulEquiv
          (p := 3) (k := 4) (by norm_num) e.symm hE hcard
      have h2le : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) / 2 := by
        have := Nat.div_le_div_right (c := 2) hge
        norm_num at this ⊢
        exact this
      omega
    ·
      have hge : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
        obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Fi22_elementary_three_rank_four
        exact CFSG.HardMathSupport.Timmesfeld.Coordinator.le_pRank_of_mulEquiv
          (p := 3) (k := 4) (by norm_num) e.symm hE hcard
      have h2le : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) / 2 := by
        have := Nat.div_le_div_right (c := 2) hge
        norm_num at this ⊢
        exact this
      omega
    ·
      have hge : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) := by
        obtain ⟨E, hE, hcard⟩ := CFSG.SectionRank.Fi24prime_elementary_three_rank_four
        exact CFSG.HardMathSupport.Timmesfeld.Coordinator.le_pRank_of_mulEquiv
          (p := 3) (k := 4) (by norm_num) e.symm hE hcard
      have h2le : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (X ⧸ Subgroup.center X)) / 2 := by
        have := Nat.div_le_div_right (c := 2) hge
        norm_num at this ⊢
        exact this
      omega

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
