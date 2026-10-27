
module

public import Certificates.Certificate2051Base

public import CFSG.Sporadic.Co2Schreier.CoreCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.ChainCheckBase
public meta import Std.Data.HashMap
import Certificates.Kernel.SporSch.Co2M.EnumR
import Certificates.Kernel.SporSch.Co2M.ChainQ
import Certificates.Kernel.SporSch.Co2M.ChainR

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Monster.B.Mathieu in
theorem certificate2051 : (coreOK qArrs cArrs localRec.chains.qAction.origArrs 512 [0, 23] enumQ = true ∧
      eqA 2300 enumQ.elems[23]! zArr = true
    )
    ∧ (coreOK rArrs dArrs localRec.chains.rAction.origArrs 2048 centerIdxR enumR = true ∧
      eqA 2300 enumR.elems[617]! zArr = true ∧ eqA 2300 enumR.elems[434]! tArr = true
    )
    ∧ (recordOK 512 localRec.chains.qAction 4 = true ∧
      recordOrbits 512 localRec.chains.qAction = [270, 28, 64, 24, 4, 2, 2, 2]
    )
    ∧ (recordOK 2048 localRec.chains.rAction 4 = true ∧
      recordOrbits 2048 localRec.chains.rAction = [840, 8, 6, 4, 2, 2, 2]
    ) :=
  ⟨KernelSporSch.Co2M.coreQ, KernelSporSch.Co2M.coreR,
    ⟨KernelSporSch.Co2QA.record_ok, KernelSporSch.Co2QA.orbits_ok⟩,
    ⟨KernelSporSch.Co2RA.record_ok, KernelSporSch.Co2RA.orbits_ok⟩⟩

end Certificates
