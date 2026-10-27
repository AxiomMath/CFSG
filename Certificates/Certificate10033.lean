module

public import CFSG.Monster.GMS.Griess13.ChecksGlueInputs
public import CFSG.Monster.GMS.Griess13.GlueCertData
import Certificates.Kernel.Griess13.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.GMS.Griess13.Co1Data in
open scoped Matrix in
open CFSG.Sporadic.SmallF2.Native (mulRows idRows powRows rowsOfPayload ofBits) in
theorem certificate10033 :
    (gCheck = true)
    ∧ (freeCheck = true)
    ∧ (∀ j : Fin 8, freePos.getD j.val 0 < 576)
    ∧ (oneCheck = true)
    ∧ (commuteCheck = true)
    ∧ (spanCheckWith (eqsOf xRows) (fmaskOf freePos) certTab = true)
    ∧ (∀ a ∈ freePos, ∃ j : Fin 8, freePos.getD j.val 0 = a)
    ∧ (∀ c : Fin 8 → ZMod 2,
      eqRows (powRows 24 (mulRows 24 prG.r (comboRows c)) 7) (idRows 24) = true →
        eqRows (comboRows c) (idRows 24) = true)
    ∧ (abCheck = true) := KernelG13.facts10033

end Certificates
