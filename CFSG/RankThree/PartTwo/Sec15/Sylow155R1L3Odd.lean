module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L3OddInputs
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1L3OddU35Alt
import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLeLeK
import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLeMeets
import CFSG.RankThree.PartTwo.Sec15.Lempken155L3NotLeO2
import CFSG.RankThree.PartTwo.Sec16.Item16Tail13
public import CFSG.RankThree.PartTwo.Sec15.Praeger155R1Item1730Final

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

section Closed


theorem res1L112InPt_l3Odd_of_316
    (h316 : Sec19.Item316) {P : ∀ (Y : Type) [Group Y], Prop} :
    Sylow155R1.Res1L112InPt LempkenL3.Res1L3OddPt P := by
  intro G _ _ A c L hR hPt hWH _ _ K _ _ _ _ hC _ _ _ _ _ _ _ _ _ _ _ _ _ hfield _
  have hPt' := hPt
  obtain ⟨⟨hL3, hnPGL⟩, p, e, hp, hp2, he, hiso⟩ := hPt'
  have hK0 : K ∈ scriptY0 A (lB A) := hC.mem_k.prop
  have hΩ : omegaA A = {Subgroup.zpowers c} :=
    Res1Omega1513.omegaA_eq_of_lThreePi h316 hR hL3 hnPGL hWH ⟨K, hK0⟩
  have hMP : Step1513MeetsPoint := Sec16.step1513MeetsPoint_of_steps148
    Sec14.Ronan148C.step148Core_holds Sec14.Ronan148M.step148Point_holds
    Sec14.Ronan148M.step148KType_holds
  have hm : MeetsY4 A (lB A) L K := LempkenL3.meetsY4_of_omegaA_eq hMP hR hΩ hiso hK0
  have hLΔ : L ≤ delta A (lB A) L := le_delta_at_l3Odd hR hPt
  rcases item1514_iff.mp (item1514_at_l3Odd h316 hR hPt hWH) K hC.mem_k hm with h1 | h2 | h3
  ·
    obtain ⟨hKcov, hLcov, -, -, -⟩ := h1
    have h3L : 3 ∣ Nat.card L := Sec16.Proof1613.three_dvd_card_L hR.toSec14Std
    have hO2N : CFSG.Open.pCoreOf 2 L ≤ Subgroup.normalizer (K : Set G) :=
      Sec15.pCoreOf_two_le_normalizer_of_mem_scriptY0Star_at h316 hR hL3 hC.mem_k hWH h3L
    have hLK : L ≤ K :=
      LempkenL3.le_of_eq_inf_sup_of_pCoreOf_two_le_normalizer hR hK0.1 hLcov hO2N
    have hKL : K = L ⊔ CFSG.Open.pCoreOf 2 K := by
      rw [inf_eq_right.mpr hLK] at hKcov
      exact hKcov
    have h44T : Item4_4Types135 :=
      item4_4Types135_of_item4_4 Sec4.Census.rank3II_4_4_of_griess_noItem41
    have hKT : KS135TwoRank := ks135TwoRank_of_cover ks135TwoRankCover
      Sec4.Sporadic.rank3II_4_14_local Sec4.Sporadic.rank3II_4_15
    have hRd : Item135SimpleReduce := item135SimpleReduce_narrow h44T hKT
      sporadicModels131 Sec4.Sporadic.rank3II_4_14_local Sec4.Sporadic.rank3II_4_15
    have h135 : Item135Simple := item135Simple_of_steps hRd item135SimpleL3
    have hθ : aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L :=
      Sec16.Proof169Theta.theta_eq_pCore_two_of_item135Simple h135 hR.toSec13Data (Or.inl hL3)
    have hKiso := LempkenL3.isoLThreePi_quot_pCore_two_of_cover hLK hKL hθ hiso
    have h154 : Item154R := item154R_of_item159R (item159R_of_h316 h316)
    exact ⟨hLΔ, hLK, hKL, LempkenL3.l3_pCoreOf_le_of_ctx155 h154 hR hΩ he hC hLK hKL hKiso⟩
  ·
    obtain ⟨⟨φ⟩, -⟩ := h2
    exact (Sec14.not_isoLThreePi_alternating_seven p e
      (Proof1511.isoLThreePi_of_mulEquiv φ hiso)).elim
  ·
    obtain ⟨⟨h5, ⟨φU⟩⟩, -, -, -, -, hsimpL, hodd⟩ := h3
    have h9 := card_inf_eq_nine_of_meets hR (Res1H1.item1511R_of_item316 h316 G A c L hR) he hiso
      hK0 hm
    exact (false_of_u35_of_field hR φU hsimpL hodd h9 hfield).elim

end Closed

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1.L3Odd
