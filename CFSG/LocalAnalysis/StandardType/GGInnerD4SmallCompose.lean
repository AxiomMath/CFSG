module

public import CFSG.LocalAnalysis.StandardType.GGInnerD4SmallContracts
public import CFSG.LocalAnalysis.StandardType.GGInnerD4RAContracts

public section

namespace CFSG.StandardType.S2MathAs51600SmallCompose

open CFSG CFSG.Assembly
open CFSG.StandardType.S2MathAs51600Small
open CFSG.StandardType.S2MathAs51600

@[expose] def SmallComposition : Prop :=
  SmallTableInput → SmallInnerActorsInput → SuzukiOrderInput → DerivedOrderInput →
    D4OrderLowerInput → GGLabelRigidInput → CentralFixedComponentTransfer → SmallVacuity

theorem smallVacuity_of_composition (h : SmallComposition)
    (hTable : SmallTableInput) (hActors : SmallInnerActorsInput)
    (hSuz : SuzukiOrderInput) (hDer : DerivedOrderInput)
    (hD4 : D4OrderLowerInput) (hRig : GGLabelRigidInput)
    (hTransfer : CentralFixedComponentTransfer) : SmallVacuity :=
  h hTable hActors hSuz hDer hD4 hRig hTransfer

end CFSG.StandardType.S2MathAs51600SmallCompose

end
