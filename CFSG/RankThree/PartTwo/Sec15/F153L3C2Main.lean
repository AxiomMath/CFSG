module

public import CFSG.RankThree.PartTwo.Sec15.F153L3
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Core
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Inn
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2HJ
public import CFSG.RankThree.PartTwo.Sec15.F153L3C2Order
public import CFSG.RankThree.PartTwo.Sec14.Item143Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3C2

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec15.F153

section Main


theorem step153PushL3Char2R_of_inputs (h134 : Item134) (h48 : Sec4.Item4_8)
    (h149 : Sec16.Item149S14) (htwin : Claim153TwinR) (h148 : Item148HJS14)
    (hOut : KFactL3NoOuterOffender) (hCent : KFactL3CentOdd) :
    Step153PushL3Char2R := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY f hf hε
  exfalso
  by_cases hHJ : AllPointsHJ A
  · exact false_of_hj_stage h134 h48 h148 kL3Char2NotList148_holds hR hHJ
      (scriptY0Star_subset A (lB A) hY) hf hε
  · have hh := hR.toSec14Std
    have hLB : ∀ B, IsHyperplane A B → lB A B = ⊥ := fun B hB =>
      lB_eq_bot_of_not_allPointsHJ' h134 h48 hh hHJ hB
    have hF : generalizedFitting ↥Y = CFSG.pCore 2 ↥Y :=
      Push153.generalizedFitting_eq_of_mem_scriptY0Star hh (h149 G A c L hh) (htwin G A c L hR) hY
    have hY3 : Y = oPrimeResidualOf 3 Y := hY.prop.1.2.1
    have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
    have hS2 : IsPGroup 2 S := isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop
    have hO2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥ := hY.prop.2.2
    have hKP : CFSG.Open.IsKProper G := hh.toTheoremFourHyp.kProper
    have hKH : CFSG.Open.IsKGroup ↥(Y ⊔ S) :=
      hKP.isKGroup (Y ⊔ S) (sup_ne_top_of_pCoreOf_ne_bot hh.toTheoremFourHyp hSY hO2)
    have hInn := inner_trivial_153 hCent hf hh.isE27 hLB hS.prop.1.1 hS2 hY.prop.1.1.2 hSY hYq hε
    exact leaf_false_of_noOuterFFOffender hKH hF hY3 hYq hS2 hSY hFF hno hInn
      (hOut _ f hf hε) (MulEquiv.refl _)

end Main

end CFSG.RankThree.PartTwo.Sec15.F153L3C2
