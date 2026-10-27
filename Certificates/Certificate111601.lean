module

public import Certificates.Data.J2C4725
import Certificates.Kernel.J2Cover.C4725K

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelJ2Cover.C4725K in
open CFSG.RankThree.PartTwo.J2Residue.C4725 in
theorem certificate111601 :
    (psiCheck () = true)
    ∧ (orbitCheck () = true)
    ∧ (CFSG.RankThree.PartTwo.J2Residue.C4725.basisCheck () = true)
    ∧ (keptCheck () = true)
    ∧ (targetCheck () = true)
    ∧ (conjCheck () = true) :=
  ⟨psiC, orbitC, basisC, keptC, targetC, conjC⟩

end Certificates
