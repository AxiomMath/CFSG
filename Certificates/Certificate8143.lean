module

public import CFSG.RankThree.Native.ONTripleMatSound
public import CFSG.RankThree.Native.ONTriplePresInputs
import Certificates.Kernel.Misc.ON.Rels

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelMisc.ON CFSG.RankThree.Native.ONTriple

open CFSG CFSG.RankThree CFSG.RankThree.Native CFSG.RankThree.Native.ONTriple in
theorem certificate8143 : (∀ r ∈ coverRels 1 1 1, FreeGroup.lift gM (FreeGroup.mk r) = 1) ∧
    gM 0 * gM 1 ≠ gM 1 * gM 0 ∧ gM 7 ≠ 1 := by
  refine ⟨fun r hr => ?_, (chkNontrivM_spec gensB nontrivB).1, (chkNontrivM_spec gensB nontrivB).2⟩
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr
  have h := relsB j (by rw [show (coverRels 1 1 1).length = 37 by decide] at hj; exact hj)
  rw [List.getD_eq_getElem _ _ hj] at h
  exact relOKM_spec gensB h

end Certificates
