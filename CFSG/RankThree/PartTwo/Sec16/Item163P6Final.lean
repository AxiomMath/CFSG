module

public import CFSG.RankThree.PartTwo.Sec16.Item163P6Conf
public import CFSG.RankThree.PartTwo.KFacts.KS163P6
public import CFSG.RankThree.PartTwo.Sec15.Item1514StepsRoute
public import CFSG.RankThree.PartTwo.Sec17.RouteWire14
public import CFSG.RankThree.PartTwo.Sec17.RouteProvers142
import CFSG.RankThree.PartTwo.Sec16.Item163P6Shape
import CFSG.RankThree.PartTwo.Sec16.Item163P6Hyper
import CFSG.RankThree.PartTwo.Sec16.Item163P6Delta
import CFSG.RankThree.PartTwo.Sec16.Item163P6Inn
import CFSG.RankThree.PartTwo.Sec16.Item163P6Alt
import CFSG.RankThree.PartTwo.KFacts.KS163P6A10Proof
import CFSG.RankThree.PartTwo.KFacts.KS163P6L3Norm
import CFSG.RankThree.PartTwo.KFacts.KS163P6L3Cent
import CFSG.RankThree.PartTwo.Sec16.Item16Res7ProofTwoPow

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163P6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Sec17

variable {G : Type} [Group G] [Finite G]

namespace Conf685

variable {A : Subgroup G} {c : G} {L Y S : Subgroup G}

theorem exists_mem_scriptY0Star_le_normalizer (h : Conf685 A c L Y S) {R : Subgroup G}
    (hR : R ∈ scriptQPi A (lB A) ⊤ (piOf 2)) :
    ∃ Y' ∈ scriptY0Star A (lB A), R ≤ Subgroup.normalizer (Y' : Set G) := by
  obtain ⟨S₀, hS₀, hS₀Y⟩ := exists_qStar_le_normalizer h.item153 h.obs h.mem_y
  obtain ⟨w, hw, hRw⟩ := exists_conj_le_normalizer h.item1411 hS₀ hS₀Y hR
  exact ⟨Y.map (MulAut.conj w).toMonoidHom, map_conj_mem_scriptY0Star hw h.mem_y, hRw⟩

theorem center_quot_pCore_eq_bot
    (h : Conf685 A c L Y S) {Y₀ : Subgroup G} (hY₀ : Y₀ ∈ scriptY0Star A (lB A)) :
    Subgroup.center (↥Y₀ ⧸ CFSG.pCore 2 ↥Y₀) = ⊥ := by
  rcases shape h hY₀ with hY | ⟨hK, -, -⟩
  · have hZL : Subgroup.center ↥L = ⊥ := by
      have hD := h.sec15R.toSec13Data
      have htypes := (h.sec15R.chosen136.2 c h.sec15R.zpowers_mem_omegaA L h.sec15R.mem_lA).1
      have hZ : Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) = ⊥ :=
        Sec15.center_eq_bot_of_types hD.mem_thetaComponentsAt htypes
      let eθ : (↥L ⧸ aschbacherSolvableCore 3 ↥L) ≃* ↥L :=
        (QuotientGroup.quotientMulEquivOfEq (theta_eq_bot h)).trans QuotientGroup.quotientBot
      rw [← Subgroup.map_center_eq eθ, hZ, Subgroup.map_bot]
    exact center_quot_eq_bot (h.le_y Y₀ hY₀) hY (inf_pCoreOf_eq_bot h hY₀) hZL
  · exact center_quot_eq_bot_of_alternating hK

theorem exists_goodR163
    (h : Conf685 A c L Y S) (hN : KFacts.KS163P6Norm)
    (hC : KFacts.KS163P6Cent) : ∃ R : Subgroup G, GoodR163 A L R := by
  have hLQ : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥ := inf_pCoreOf_eq_bot h h.mem_y
  obtain ⟨H, U, hH, hU, hU1, -, hUH, hUD, hUD'⟩ :=
    exists_hyperplane_scriptQZero h hLQ (cover h h.mem_y)
  obtain ⟨R, hR, hXR, hDR, hRC⟩ :=
    exists_delta h (xA_le_normalizer h hN) hH hU hU1 hUH hUD hUD'
  obtain ⟨Y', hY', hRY⟩ := exists_mem_scriptY0Star_le_normalizer h hR
  have hR2 : IsPGroup 2 R := (isPiSubgroup_piOf_iff Nat.prime_two R).mp hR.2
  obtain ⟨r, hrR, hr1, hrN, hρ⟩ : ∃ r ∈ R, r ≠ 1 ∧ ∃ hr : r ∈ Subgroup.normalizer
      (Y' : Set G), actQ Y' ⟨r, hr⟩ = 1 := by
    rcases shape h hY' with hY | ⟨hK, hAY, -⟩
    · exact exists_actQ_eq_one_of_eq_sup h hC hY' hR hRY hDR hRC hY
    · exact exists_actQ_eq_one_of_alternating h KFacts.ks163P6A10 hY' hR hRY hDR hK hAY
  exact ⟨R, hR, hXR, pCoreOf_sup_ne_bot_of_actQ_eq_one hR2 hRY (h.le_y Y' hY')
    (center_quot_pCore_eq_bot h hY') hrR hr1 hrN hρ⟩

end Conf685

end CFSG.RankThree.PartTwo.Sec16.Proof163P6

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec17

theorem step163VR_of_kfacts (h142 : Concl142R) (h146 : Item146R)
    (h1444 : Item1444S14) (hbot : Item145BotS14) (h153 : Item153MainR)
    (hobs : Claim153ObsR) (h1411 : Item1411_1R) (h1514 : Item1514R) (hMeets : Step163Meets)
    (hL4 : Step163L4A7) (h131 : Item131) (h138 : Item138N) : Step163VR := by
  intro G _ _ A c L h hL hO hL3 Y hY S hS hSL hSL1
  let conf : Proof163P6.Conf685 A c L Y S :=
    { sec15R := h
      le_y := hL
      pCoreOf_eq_bot := hO
      not_isL3TwoPow := hL3
      mem_y := hY
      mem_s := hS
      mem_d := hSL
      d_ne_bot := hSL1
      item1514 := h1514 G A c L h
      meets := hMeets
      l4a7 := hL4
      item131 := h131
      item138 := h138
      item153 := h153 G A c L h
      obs := hobs G A c L h
      item1411 := h1411 G A c L h
      concl142 := h142 G A c L h
      item1444 := h1444 G A c L h.toSec14Std
      item146 := h146 G A c L h
      bot := hbot G A c L h.toSec14Std }
  exact Proof163P6.Conf685.exists_goodR163 conf KFacts.ks163P6Norm KFacts.ks163P6Cent

theorem item163R_of_named_kfacts (h1514 : Item1514R) (h162 : Item162R)
    (h153 : Item153MainR) (hobs : Claim153ObsR) (h1411 : Item1411_1R) (h142 : Concl142R)
    (h143 : Concl143S14) (h155 : Item155R) (h1424 : Item14_24R) (hloc : Claim1411LocalR)
    (h131 : Item131) (hU35 : Step163U35) (hPt : Step163Pt) (hYa : Step163Ya)
    (hMeets : Step163Meets) (hA7 : Step163A7) (hA10 : Step163A10) (hL3 : KS163QLInvL3)
    (hShape : Step163TwoPowShape) (hXT : Step163XTransH) (hL4 : Step163L4A7)
    (hDY : Step163DeltaY) (h146 : Item146R) (h1444 : Item1444S14) (hbot : Item145BotS14)
    (h138 : Item138N) : Item163R := by
  have hQL := step163QLNE_of h142 h1514 hMeets (ks163QLInv_of h131 hL3)
  have hTwo := step163TwoPowNE_of_res7 h142 h143 h153 hobs h1411 h1514 hMeets h1424 hShape h138
  have hΔ := step163Delta_of h155 h142 h1514 hMeets hL4 hDY
  have hVR := step163VR_of_kfacts h142 h146 h1444 hbot h153 hobs h1411 h1514 hMeets hL4 h131 h138
  exact item163R_of_NE h1514 h162 h153 hobs h1411 h142 hU35 hPt hYa hMeets hA7 hA10 hQL
    (step163Q2TwoPow_of hTwo hΔ h153 hobs h1411 (step163XTransTwoPow_of hloc h1514 hMeets hXT))
    hΔ hTwo (step163VNE_of hQL hVR)

end CFSG.RankThree.PartTwo.Sec16

end
