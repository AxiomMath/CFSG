module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HSCheckInputs
import Certificates.Kernel.LocalQT.Base.C4133

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG.Sporadic.Th.Native (ap) in
open CFSG.Sporadic.HS.Native (hsData) in
theorem certificate4133 : (slpValidAux hsProg2 2 = true)
    ∧ (slpValidAux hsWprog 2 = true)
    ∧ (qpOK hsData.n hsNT2 hsQp)
    ∧ (BaseEnumOK hsData.n (List.range hsData.n) hsGens2 hsGensI2 hsEnum2.1
          hsEnum2.2.1 hsEnum2.2.2)
    ∧ (hsEnum2.1.size = 2 ^ 9)
    ∧ (hsGn < hsNT2.size ∧ hsGin < hsNT2.size ∧ hsHn < hsNT2.size ∧
          hsHin < hsNT2.size ∧ hsAn < hsWNT.size ∧ hsBn < hsWNT.size)
    ∧ (invPairOK (Array.range hsData.n) hsNT2[hsGn]! hsNT2[hsGin]! = true)
    ∧ (invPairOK (Array.range hsData.n) hsNT2[hsHn]! hsNT2[hsHin]! = true)
    ∧ (normOK hsZ1 hsNT2[hsGn]! hsNT2[hsGin]! = true)
    ∧ (normOK hsQc hsNT2[hsHn]! hsNT2[hsHin]! = true)
    ∧ (notNormOK hsQc hsNT2[hsGn]! hsNT2[hsGin]! = true)
    ∧ (notNormOK hsZ1 hsNT2[hsHn]! hsNT2[hsHin]! = true)
    ∧ (hsWNT[hsAn]! = hsTa')
    ∧ (hsWNT[hsBn]! = hsTb') :=
  CFSG.KD.LQT.C4133.cert

end Certificates
