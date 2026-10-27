module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KGroupSporadic
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Lit2.L2HoldsSpor
public import CFSG.ClassicalGroups.SpecialLinear.ComponentCartanRank
public import CFSG.GroupTheory.CentralQuotientPRank
public import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.B69K.OddCoversLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator


theorem pRank_three_le_three_of_small_sporadic
    {K : Type} [Group K] [Finite K] (hQ : CFSG.Open.IsQuasisimple K)
    (hOdd : Odd (Nat.card (Subgroup.center K))) {s : TauCeti.SporadicName}
    (hs : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor (K ⧸ Subgroup.center K) s)
    (hsmall : s = .J1 ∨ s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨
      s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4) :
    CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
  obtain ⟨e⟩ := hs
  have hsp : CFSG.LocalAnalysis.UniquenessCase.UC22.IsSpor (K ⧸ Subgroup.center K) s := ⟨e⟩
  have hperf : Group.IsPerfect K := Group.isPerfect_def.mpr hQ.1
  have hdvd := CFSG.Quasithin.B69K.OddCovers.card_center_dvd_hopfMultiplier hperf e
  rw [CFSG.OddStandard.HigherRank.YamadaG23.l2Sporadic_holds s] at hdvd
  have h12 : Nat.card (Subgroup.center K) ∣ 12 :=
    hdvd.trans (sporadicMultiplierOrder_dvd_twelve s)
  have hQuotTwo (hmem : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
      s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4) :
      CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) = 2 := by
    have hr := (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.kSporadicThreeRank_holds
      (K ⧸ Subgroup.center K) s hsp).2.mp hmem
    rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hr
  have hLe (hZ : ¬ 3 ∣ Nat.card (Subgroup.center K))
      (hmem : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
        s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4) :
      CFSG.Open.pRank 3 (⊤ : Subgroup K) ≤ 3 := by
    have heq := CFSG.ClassicalGroups.SpecialLinear.pRank_top_eq_of_mulEquiv_center_quotient
      (G := K) (T := K ⧸ Subgroup.center K) Nat.prime_three
      (MulEquiv.refl (K ⧸ Subgroup.center K)) hZ
    rw [heq, hQuotTwo hmem]
    norm_num
  by_cases hJ : s = .J1
  · rcases hJ with rfl
    have hZ1 : Nat.card (Subgroup.center K) = 1 := Nat.dvd_one.mp hdvd
    have hZ : ¬ 3 ∣ Nat.card (Subgroup.center K) := by rw [hZ1]; norm_num
    have hq1 : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) = 1 := by
      have hr := (CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.kSporadicThreeRank_holds
        (K ⧸ Subgroup.center K) .J1 hsp).1.mp rfl
      rwa [CFSG.SectionRank.pRank_coe_eq_openPRank] at hr
    have heq := CFSG.ClassicalGroups.SpecialLinear.pRank_top_eq_of_mulEquiv_center_quotient
      (G := K) (T := K ⧸ Subgroup.center K) Nat.prime_three
      (MulEquiv.refl (K ⧸ Subgroup.center K)) hZ
    rw [heq, hq1]
    norm_num
  · have hmem : s = .M11 ∨ s = .M12 ∨ s = .M22 ∨ s = .M23 ∨ s = .M24 ∨
        s = .J2 ∨ s = .HS ∨ s = .He ∨ s = .Ru ∨ s = .J4 := by
      rcases hsmall with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hJ rfl).elim
      all_goals simp
    by_cases h3 : 3 ∣ Nat.card (Subgroup.center K)
    · have hZcard : Nat.card (Subgroup.center K) = 3 := by
        have hle : Nat.card (Subgroup.center K) ≤ 12 := Nat.le_of_dvd (by norm_num) h12
        have hge : 3 ≤ Nat.card (Subgroup.center K) := Nat.le_of_dvd Nat.card_pos h3
        obtain ⟨k, hk⟩ := hOdd
        interval_cases h : Nat.card (Subgroup.center K)
        · rfl
        all_goals norm_num at h12
        all_goals omega
      have hM22 : s = .M22 := by
        rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals
          first
            | rfl
            | rw [hZcard] at hdvd
              exact absurd hdvd (by decide)
      rcases hM22 with rfl
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hbound := CFSG.GroupTheory.CentralQuotient.pRank_le_pRank_map_mk_add_one
        (p := 3) (N := Subgroup.center K) (by rw [hZcard]) (⊤ : Subgroup K)
      have hmap : (⊤ : Subgroup K).map (QuotientGroup.mk' (Subgroup.center K)) = ⊤ :=
        Subgroup.map_top_of_surjective (QuotientGroup.mk' (Subgroup.center K))
          (QuotientGroup.mk'_surjective (Subgroup.center K))
      rw [hmap] at hbound
      have hq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ Subgroup.center K)) = 2 :=
        hQuotTwo (by simp)
      omega
    · exact hLe h3 hmem

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
