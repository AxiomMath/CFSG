module

public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviThreeAssembly
public import CFSG.LocalAnalysis.StandardType.GGTBJE6LeviTwo

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGTBJOrdinaryOutside.of_E6_of_T
    {E : ℕ → LargeEvenLabel → Prop} (hTCJ : GGTCJKnown) (hI3 : GGNbrSubcomponentInput)
    (hRig : GGLabelRigidInput)
    (hTL : GGTBJETypeLeviL .E6 fun p n labJ =>
      ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1))
    (hTK : GGTBJETypeLeviK .E6 fun p n labJ =>
      ggTBJE6RowCand p n labJ ∨ ¬ (p = 3 ∧ 3 ∣ 2 ^ n - 1))
    (h : GGTBJOrdinaryOutside fun p lab => E p lab ∨ ggTBJE6Label p lab) :
    GGTBJOrdinaryOutside E :=
  GGTBJOrdinaryOutside.of_E6 hTCJ hI3 ggTBJE6RowL_holds ggTBJE6RowK_holds
    (ggTBJE6LeviL_of_TQ hRig hTL (ggTBJE6LeviL_Q hRig))
    (ggTBJE6LeviK_of_TQ hRig hTK (ggTBJE6LeviK_Q hRig)) h

end CFSG.StandardType

end
