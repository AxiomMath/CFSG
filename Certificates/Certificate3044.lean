module

public import Certificates.Kernel.BabyMonster.CTIB.CosetSq

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelBM.CTIB

open CFSG.Monster.B.GSide CFSG.Monster.B.CTIB in
theorem certificate3044 : (cosetSqOK innerTab = true)
    ∧ (fusionWitnessOK innerTab = true) :=
  ⟨CosetSq.cosetSq KernelBM.census_orbitLists, CosetSq.fusionWitness KernelBM.census_orbitLists⟩

end Certificates
