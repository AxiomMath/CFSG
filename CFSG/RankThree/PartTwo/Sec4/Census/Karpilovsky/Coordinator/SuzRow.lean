module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverList
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoSuz.Model

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator

open Subgroup CFSG.RankThree.PerfectCover CFSG.Blueprint
open CFSG.Sporadic.Recognition.SuzMultiplier CFSG.EvenSporadicStandard.TwoSuz
open CFSG.Sporadic.SuzOddCore (suzM)

theorem orderOf_neg_one_GL12 : orderOf (-1 : GL12) = 2 :=
  orderOf_eq_prime (by
    refine Units.ext ?_
    simp) neg_one_ne_one_GL

theorem two_dvd_card_griessHopfMultiplier_suzM
    (hTab : suzTabCheck = true) :
    2 ∣ Nat.card (CFSG.Open.griessHopfMultiplier suzM) := by
  rw [card_griessHopfMultiplier_eq_card_ker hTab]
  have hdπ : (PresentedGroup.of suzD : SuzCover) ^ 2 ∈ (suzπ hTab).ker := by
    rw [MonoidHom.mem_ker, map_pow, suzπ_of hTab]
    exact suzGen_d_sq hTab
  have h1 := orderOf_map_dvd rho ((PresentedGroup.of suzD : SuzCover) ^ 2)
  rw [rho_sq_d, orderOf_neg_one_GL12] at h1
  have h2 := orderOf_dvd_natCard (⟨_, hdπ⟩ : (suzπ hTab).ker)
  rw [← Subgroup.orderOf_coe] at h2
  exact h1.trans h2

theorem two_dvd_card_griessHopfMultiplier_Suz :
    2 ∣ Nat.card (CFSG.Open.griessHopfMultiplier NativeSporadic.Suz) := by
  have e := CFSG.Sporadic.SuzOddCore.suzEquivM
  have h : Nat.card (CFSG.Open.griessHopfMultiplier NativeSporadic.Suz) =
      Nat.card (CFSG.Open.griessHopfMultiplier suzM) :=
    card_griessHopfMultiplier_of_mulEquiv Certificates.certificate15030 e
      Certificates.certificate15033
    Certificates.certificate15034 Certificates.certificate15035
  rw [h]
  exact two_dvd_card_griessHopfMultiplier_suzM Certificates.certificate15030

theorem nativeRow_Suz :
    Nat.card (hopfMultiplier (NativeSporadic.Carrier .Suz)) =
      CFSG.RankThree.PartTwo.Sec4.Census.sporadicMultiplierOrder .Suz := by
  have h6 : Nat.card (CFSG.Open.griessHopfMultiplier NativeSporadic.Suz) = 6 := by
    have h2 := two_dvd_card_griessHopfMultiplier_Suz
    rcases card_griessHopfMultiplier_Suz Certificates.certificate15030
      Certificates.certificate15031 Certificates.certificate15033
      Certificates.certificate15034 Certificates.certificate15035 with h | h
    · rw [h] at h2
      omega
    · exact h
  rw [← Nat.card_congr (hopfMultiplierEquivGriess _).toEquiv]
  exact h6

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator
