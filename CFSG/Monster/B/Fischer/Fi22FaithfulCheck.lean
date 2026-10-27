
module

public import CFSG.Monster.B.Fischer.Fi22FaithfulCheckBase

public import CFSG.Monster.B.Fischer.Fi22Cert
public import CFSG.Monster.B.Fischer.Fi22SepData
public import Certificates.Data.CFSGNative.Fi22.Certificate
public meta import CFSG.Monster.B.Fischer.Fi22Cert
public meta import CFSG.Monster.B.Fischer.Fi22SepData
public meta import Certificates.Data.CFSGNative.Fi22.Certificate
public meta import Certificates.Data.CFSGNative.Fi22Pinned.Forms
public import CFSG.Monster.B.Fischer.Fi22FaithfulCheckInputs
public import Certificates.Certificate3152
public import Certificates.Certificate3152Base

public section

namespace CFSG.Monster.B.Fischer

open CFSG.F3.Native CFSG.Monster.B.Fischer.Native

theorem fi22Faithful_check :
    distinctOK fi22FormsBytes 4 = true ∧
    actionOK fi22FormsBytes (fi22ChainGen 0) CFSG.Sporadic.Fi22.Native.matA 4 = true ∧
    actionOK fi22FormsBytes (fi22ChainGen 1) CFSG.Sporadic.Fi22.Native.matB 4 = true ∧
    pullbackOK fi22InvFormBytes 0 fi22InvFormBytes 0 CFSG.Sporadic.Fi22.Native.matA
      (transpose 77 CFSG.Sporadic.Fi22.Native.matA) = true ∧
    pullbackOK fi22InvFormBytes 0 fi22InvFormBytes 0 CFSG.Sporadic.Fi22.Native.matB
      (transpose 77 CFSG.Sporadic.Fi22.Native.matB) = true ∧
    wfM fi22Bi = true ∧ fi22Bi.size = 77 ∧
    eqM 77 (mul 77 (polarRows fi22InvFormBytes 0) fi22Bi) (idM 77) = true ∧
    sepOK 77 fi22SepMats fi22SepTerms fi22SepVec fi22SepK fi22SepP fi22SepTinv
      fi22SepTree = true :=
  Certificates.certificate3152

end CFSG.Monster.B.Fischer
