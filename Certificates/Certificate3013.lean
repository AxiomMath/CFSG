module

public import Certificates.Kernel.BabyMonster.CTIB.Inner3013
public import Certificates.Kernel.BabyMonster.Census

public section

namespace Certificates

open CertificateChecks

open CertificateChecks.KernelBM.CTIB

open CFSG.Monster.B.CTIB in
theorem certificate3013 : (innerTabOK innerTab = true)
    ∧ (innerHist innerTab = #[4194304, 1783, 1783, 49896, 49896, 1995840, 2095104, 1, 1, 0])
    ∧ (innerRepsOK innerTab = true)
    ∧ (innerOrbOK () = true) :=
  ⟨Hist.tabOK KernelBM.census_orbitLists, Hist.hist KernelBM.census_orbitLists,
    Hist.repsOK KernelBM.census_orbitLists, Hist.orbOK KernelBM.census_orbitLists⟩

end Certificates
