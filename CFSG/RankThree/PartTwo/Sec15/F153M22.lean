module

public import CFSG.RankThree.PartTwo.Sec15.F153Leaf
public import CFSG.HardMathSupport.Cooperstein.Proving.SporadicNoIrrFF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Proving (noIrrFFOffender_M22)
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic (noIrrFFOffender_transfer)

theorem step153PushM22R_of_inputs
    (h149 : Sec16.Item149S14) (htwin : Claim153TwinR) : Step153PushM22R := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY hT
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  have hirr : NoIrrFFOffender CFSG.Blueprint.NativeSporadic.M22 :=
    noIrrFFOffender_transfer noIrrFFOffender_M22
      ⟨(CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv.some).symm⟩
  have hNo := noFFModule_of_noIrrFFOffender hirr
  rcases hT with hT | hT
  · obtain ⟨e⟩ := hT
    obtain ⟨e'⟩ := nonempty_centerQuotient_equiv_of_simple hYq
      (CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2) e
    exact concl153Push_of_noFFModule h149 htwin hR hY hS hno hFF hSY hNo e'
  · obtain ⟨-, ⟨e⟩⟩ := hT
    exact concl153Push_of_noFFModule h149 htwin hR hY hS hno hFF hSY hNo e

end CFSG.RankThree.PartTwo.Sec15.F153
