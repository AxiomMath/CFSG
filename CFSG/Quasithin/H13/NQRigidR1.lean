module

public import CFSG.Quasithin.H13.NQRigidWMMain
public import CFSG.Quasithin.H13.NQRigidThompson
public import CFSG.Quasithin.H13.NQRigidObl

public section

namespace CFSG.Quasithin.H13.NQRigid

open CFSG.Quasithin

theorem oblRigidWholeModule_of_inputs
    (h56 : AsB56) (h317 : Theorem317Statement)
    (hAnother : StmtAnotherMaximalTwoLocal) (hS : NQBlock.OriginalKEscapingSourceY)
    (hE : NQBlock.OriginalNoNormalSourceYEscapes) (hNK : StmtOverlapNormalizesOriginalK) :
    OblRigidWholeModule := fun _ _ _ _ _ _ h =>
  oblRigidWholeModule_of_thompson h56 h (thompson_generation_of_inputs h317 hAnother hS hE hNK h)

end CFSG.Quasithin.H13.NQRigid
