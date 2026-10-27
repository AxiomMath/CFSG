
module

public import Certificates.Certificate2061Base
public meta import CFSG.Sporadic.Co2Schreier.SylowCheckBase
public meta import CFSG.Sporadic.Co2Schreier.CoreCheckBase
import Certificates.Kernel.SporSch.Co2M.ThirdFinalBase
import CFSG.Sporadic.Co2Schreier.ThirdOrderBase
import CFSG.Sporadic.Co2Schreier.CoresBase
import CFSG.Sporadic.Co2Schreier.KernelBase

public import CFSG.Sporadic.Co2Schreier.ThirdCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.SylowCheck
public meta import CFSG.Sporadic.Co2Schreier.CoreCheck
public meta import CFSG.Sporadic.Co2Cert.FaithfulCheck
import Certificates.Kernel.SporSch.Co2M.ThirdFinal
import Certificates.Kernel.SporSch.Co2M.ThE
import Certificates.Kernel.SporSch.Co2M.Neg2061
import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
meta import CFSG.Sporadic.Co2Schreier.Arrays
meta import Certificates.Data.CFSGNative.Schreier.Check
import CFSG.Sporadic.Co2Schreier.TextCheckInputs
meta import CFSG.Sporadic.Co2Schreier.Text
import CFSG.Sporadic.Co2Schreier.ThirdOrderBase1
import CFSG.Sporadic.Co2Schreier.Action
import CFSG.Sporadic.Co2Schreier.Cores
import CFSG.Sporadic.Co2Schreier.Kernel
import CFSG.Sporadic.Co2Schreier.SylowLemmas
import CFSG.Sporadic.Schreier.RuSylowB
import CFSG.Sporadic.Co2Cert.CheckInputs
import CFSG.Sporadic.Co2Cert.OrderCheckInputs
public import CFSG.Assembly.Defs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Monster.B.Mathieu CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2.Native in
theorem certificate2061 : (thirdCheck (thirdLevels witRec) witRec.third.baseIndices.toArray uArr
      (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr = true
    )
    ∧ (eCheck co2PosTable witRec (rawLevels 2300 co2StrongArrs co2BaseArr) co2BaseArr
      uArr = true
    ) :=
  ⟨KernelSporSch.Co2M.thirdCheckK KernelSporSch.Co2M.thirdE_check,
    KernelSporSch.Co2M.thirdE_check⟩

end Certificates
