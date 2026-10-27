module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherAutomorphismData
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherFormZero
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesAlt
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup Equiv CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher (spSemilinearAutGroup)
open CFSG.QuasithinUnique.Setup.SL2Modules (evenWeight permAct)

@[expose] noncomputable def cpuSAut {H : Type*} [Group H] (K : Subgroup H) (hK : K.Normal) :
    H →* MulAut ((K ⧸ CFSG.pCore 2 K) ⧸ center (K ⧸ CFSG.pCore 2 K)) :=
  haveI := hK
  ((CFSG.SectionRank.Ccomm.autQuotient (center (K ⧸ CFSG.pCore 2 K))).comp
    (CFSG.SectionRank.Ccomm.autQuotient (CFSG.pCore 2 K))).comp MulAut.conjNormal

end CFSG.Quasithin.H13.NQRigid
