
module

public import Certificates.Certificate2049Base

public import CFSG.Sporadic.Co2Schreier.ChainCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Arrays
public meta import Certificates.Data.CFSGNative.Schreier.Check
public import Certificates.Kernel.SporSch.Co2M.Chains2049Base
import Certificates.Kernel.SporSch.Co2M.Chains2049
import Certificates.Kernel.SporSch.Co2M.Neg2049
public import CFSG.Sporadic.Co2Schreier.OrbitCheck
public meta import CFSG.Sporadic.Co2Schreier.OrbitCheck
public import CFSG.Sporadic.Co2Schreier.TextCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.Text
public import CFSG.Sporadic.Co2Cert.CheckInputs
public import CFSG.Sporadic.Co2Cert.OrderCheckInputs

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Monster.B.Mathieu in
theorem certificate2049 : (recordOK 2300 localRec.chains.C 4 = true ∧
      recordOrbits 2300 localRec.chains.C = [256, 1260, 18, 32, 2, 2]
    )
    ∧ (recordOK 2300 localRec.chains.D 4 = true ∧
      recordOrbits 2300 localRec.chains.D = [1920, 56, 96, 4]
    )
    ∧ (recordOK 2300 localRec.chains.S 4 = true ∧
      recordOrbits 2300 localRec.chains.S = [256, 256, 4]
    )
    ∧ (recordOK 2300 localRec.chains.join 4 = true ∧
      recordOrbits 2300 localRec.chains.join = [2300, 1408, 567, 192, 10, 12]
    )
    ∧ (wordsCheck localRec levelsS = true) := KernelSporSch.Co2M.facts2049

end Certificates
