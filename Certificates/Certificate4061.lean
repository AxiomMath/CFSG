module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1CharNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RowNative
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PipeNative
public import CFSG.LocalAnalysis.QuasithinUnique.K1.SporadicRu
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1RuCheckInputs
import Certificates.Kernel.LocalQT.Base.C4061
import Certificates.Kernel.LocalQT.Base.C4061H
import Certificates.Kernel.LocalQT.Base.C4061M
import Certificates.Kernel.LocalQT.Base.C4061Z
import Certificates.Data.Kernel.LocalQT.BaseT
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.QuasithinUnique.K1.SporadicPerm in
open CFSG.Sporadic.Th.Native (ap) in
open CFSG.Sporadic.Ru.Native (ruData) in
theorem certificate4061 : (slpValidAux ruProg2 2 = true)
    ∧ (slpValidAux ruWprog 2 = true)
    ∧ (qpOK ruData.n ruNT2 ruQp)
    ∧ (BaseEnumOK ruData.n ruB' ruGens2 ruGensI2 ruEnum2.1 ruEnum2.2.1
          ruEnum2.2.2)
    ∧ (ruEnum2.1.size = 2 ^ 14)
    ∧ (ruGn < ruNT2.size ∧ ruGin < ruNT2.size ∧ ruHn < ruNT2.size ∧
          ruHin < ruNT2.size ∧ ruAn < ruWNT.size ∧ ruBn < ruWNT.size)
    ∧ (nodesLt ruNT2.size ruNodes1 = true ∧ nodesLt ruNT2.size ruNodes2 = true ∧
          nodesLt ruNT2.size ruNodes3 = true)
    ∧ (zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 [Array.range ruData.n] ruL1 = true)
    ∧ (zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 ruL1 ruL2 = true)
    ∧ (zClaimOK ruB'.length ruGens2 ruP ruEnum2.1 ruL2 ruL3 = true)
    ∧ (invPairOK (Array.range ruData.n) ruNT2[ruGn]! ruNT2[ruGin]! = true)
    ∧ (invPairOK (Array.range ruData.n) ruNT2[ruHn]! ruNT2[ruHin]! = true)
    ∧ (normOK ruL1 ruNT2[ruGn]! ruNT2[ruGin]! = true)
    ∧ (normOK ruL3 ruNT2[ruHn]! ruNT2[ruHin]! = true)
    ∧ (notNormOK ruL3 ruNT2[ruGn]! ruNT2[ruGin]! = true)
    ∧ (notNormOK ruL1 ruNT2[ruHn]! ruNT2[ruHin]! = true)
    ∧ (ruWNT[ruAn]! = ruTa')
    ∧ (ruWNT[ruBn]! = ruTb') :=
  CFSG.KD.LQT.C4061.cert

end Certificates
