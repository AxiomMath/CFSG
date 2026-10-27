
module


public import CFSG.Sporadic.Co1.Module.InvFamInputs
import Certificates.Kernel.Co1M.T10070
import Certificates.Kernel.Co1M.C10070
import Certificates.Kernel.Co1M.R10070

public section

open CFSG.Sporadic.Co1.Module CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.SmallF2.Native
open CertificateChecks.KernelCo1M

namespace Certificates

theorem certificate10070 :
    (repOK kGens kGensInv rowsSA code3 = true)
    ∧ (repOK nGens nGensInv rowsSB code4 = true)
    ∧ (repOK nGens nGensInv rowsSC code4 = true)
    ∧ (countsOK rowsSA 65536 30720 = true)
    ∧ (countsOK rowsSB 4096 0 = true)
    ∧ (countsOK rowsSC 4096 2048 = true)
    ∧ (∃ W : InvFamW, InvFamOK W)
    ∧ (q0N (transposeRows 24 qRows) code3 = true)
    ∧ (witOK [false, false, false, false] rowsSA rowsSA 3 = true)
    ∧ (witOK [false] rowsSA rowsSB 10 = true)
    ∧ (witOK [true, true, true, false] rowsSA rowsSC 12 = true)
    ∧ (q0N (transposeRows 24 qRows) code4 = false)
    ∧ (vecMulN 24 (transposeRows 24 (wordRows code4Word)) 1 = code4) :=
  ⟨repOK_A70, repOK_B70, repOK_C70, counts_A70, counts_B70, counts_C70, ⟨w70, ok70⟩, q0_code3_70,
    wit_A70, wit_B70, wit_C70, q0_code4_70, code4_word70⟩

end Certificates
