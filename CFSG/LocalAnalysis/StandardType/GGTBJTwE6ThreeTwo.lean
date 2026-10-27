module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoCell
public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6ThreeTwoInst

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley TableBExc
  TableBExc.E6Three CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTwE6Three_oddInstOne_holds
    : GGTwE6ThreeOddInstOne :=
  fun {K₁} [Field K₁] [Finite K₁] hK {L₁} [Group L₁] [Finite L₁] {ψ₁} {A₁} hodd hTB =>
    ggTwE6Three_frameClass_of_tb_one hK hodd hTB

theorem ggTwE6Three_compInvOne_holds
    : GGTwE6ThreeCompInvOne :=
  fun {K₁} [Field K₁] [Finite K₁] hK {L₁} [Group L₁] [Finite L₁] {ψ₁} {A₁} hodd hTB =>
    ggTwE6Three_comp_invariant_one hK hodd hTB

theorem ggTBJTwE6LeviL_threeOne
    (hRig : GGLabelRigidInput) (hRL : GGTwE6ThreeBstarRankInput) :
    GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1) :=
  ggTBJTwE6LeviL_threeOne_of_inst ggTwE6Three_oddInstOne_holds ggTwE6Three_compInvOne_holds hRig
    hRL

theorem ggTBJTwE6LeviL_threeOne_holds
    (hRig : GGLabelRigidInput) :
    GGTBJETypeLeviL .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1) :=
  ggTBJTwE6LeviL_threeOne hRig ggTwE6ThreeBstarRankInput_holds

theorem ggTBJTwE6LeviK_threeOne
    (hRig : GGLabelRigidInput) (hRK : GGTwE6ThreeNbrRankInput) :
    GGTBJETypeLeviK .twE6 fun p n labJ => ggTBJTwE6RowCand p n labJ ∨ ¬ (p = 3 ∧ n = 1) :=
  ggTBJTwE6LeviK_threeOne_of_inst ggTwE6Three_oddInstOne_holds ggTwE6Three_compInvOne_holds hRig
    hRK

end CFSG.StandardType

end
