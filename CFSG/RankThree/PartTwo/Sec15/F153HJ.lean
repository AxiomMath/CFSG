module

public import CFSG.RankThree.PartTwo.Sec15.F153Leaf
public import CFSG.HardMathSupport.Cooperstein.Proving.SporadicNoIrrFF
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.RouteBGlue
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFReduction

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open CFSG.HardMathSupport.Cooperstein.Coordinator
open CFSG.HardMathSupport.Cooperstein.Proving (noIrrFFOffender_J2)
open CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic (noIrrFFOffender_transfer)

theorem step153PushHJR_of_inputs
    (h149 : Sec16.Item149S14) (htwin : Claim153TwinR) : Step153PushHJR := by
  intro G _ _ A c L hR Y hY S hS hno hFF hSY ⟨e⟩
  have hYq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) := hY.prop.1.2.2.2
  obtain ⟨e'⟩ := nonempty_centerQuotient_equiv_of_simple hYq CFSG.Sporadic.J2.isSimpleGroup_J2 e
  have hirr : NoIrrFFOffender CFSG.Blueprint.NativeSporadic.J2 :=
    noIrrFFOffender_transfer noIrrFFOffender_J2
      ⟨(CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv.some).symm⟩
  exact concl153Push_of_noFFModule h149 htwin hR hY hS hno hFF hSY
    (noFFModule_of_noIrrFFOffender hirr) e'

end CFSG.RankThree.PartTwo.Sec15.F153
