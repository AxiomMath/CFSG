module

public import CFSG.CGT.PushingUpLit.SolKNA.QuatLieNegPSp4Inputs
public meta import CFSG.GH74.KGroups.NativeChecks2
public meta import CFSG.Fischer.Classification.PartIII.Beta.Data
import Certificates.Kernel.Misc.PSp4.Twin77001
public meta import Mathlib

public section

namespace Certificates

open CertificateChecks

open CFSG.CGT.PushingUpLit.SolKNA CFSG.CGT.PushingUpLit.SolKNA.PSp4Twin
  CFSG.GH74.KGroups.NativeChecks CFSG.ComponentClassification.CatFactsSmall.PSp43 in
theorem certificate77001 : (twinCheckA 45 (enumA QP45) (toA tw1) = true)
    ∧ (twinCheckA 45 (enumA QP45) (toA tw2) = true)
    ∧ (invCoverCheckA 45 (enumA QP45) (tws.map toA) = true) := KernelMisc.Twin77001.c77001

end Certificates
