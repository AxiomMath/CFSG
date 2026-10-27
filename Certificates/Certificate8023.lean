module

public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4ActionInputs
import Certificates.Kernel.LocalComp.J4Rows

public section

open CFSG.SectionRank.J4Order CFSG.Sporadic.J3.Native

namespace Certificates

open CertificateChecks

open CFSG CFSG.SectionRank CFSG.SectionRank.J4Order CFSG.Blueprint CFSG.SectionRank.LocalWitness
  CFSG.Sporadic.J3 CFSG.Sporadic.J3.Native in
open scoped Matrix in
theorem certificate8023 : (powRows 112 rowsA 2 = idRows 112)
    ∧ (powRows 112 rowsB 4 = idRows 112) := by
  rw [KernelLC.J4R.rowsA_eq, KernelLC.J4R.rowsB_eq]
  exact ⟨by decide +kernel, by decide +kernel⟩

end Certificates
