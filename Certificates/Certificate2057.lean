module

public import CFSG.Sporadic.Co2Schreier.SixCheckInputs
public meta import CFSG.Sporadic.Co2Schreier.WitCheck
public meta import CFSG.Sporadic.Co2Schreier.ChainCheck
public meta import CFSG.Sporadic.Co2Schreier.Lin
import Certificates.Kernel.SporSch.Co2M.Six

public section

open CFSG.Sporadic.Co2Schreier

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Co2Schreier CFSG.Monster.B.Co2.Native CFSG.Certificates.Native in
open CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu in
theorem certificate2057 : (sixCheck witRec = true)
    ∧ (witRec.wLocal.sixRows = [[59, 52, 53, 56, 22, 16], [4, 15, 28, 21, 16, 50]])
    ∧ (witRec.wLocal.sixBasisIndices = [516, 1588, 1809, 1630, 312, 1801] ∧
      witRec.wLocal.sixAnchor = 29 ∧ witRec.wLocal.sixGramRows = [54, 21, 59, 52, 47, 29]
    ) :=
  ⟨KernelSporSch.Co2M.six_check, by decide +kernel, by decide +kernel⟩

end Certificates
