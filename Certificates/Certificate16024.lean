module

public import CFSG.Monster.B.Co2.KstabMaximal
public import CFSG.Monster.Tri.LeechData

public section

open CFSG CFSG.Monster CFSG.Monster.Tri CFSG.Monster.Tri.Leech CFSG.Monster.SpinLattice
  CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.B.Short CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.KstabMaximal

namespace CertificateChecks.Batch16024

open CFSG CFSG.Monster CFSG.Monster.Tri CFSG.Monster.Tri.Leech CFSG.Monster.SpinLattice
  CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.B.Short CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.KstabMaximal

private theorem leechIdx3_size_0 : leechIdx3.size = 275 := by
  decide +kernel

private theorem leechIdx4_size_1 : leechIdx4.size = 88 := by
  decide +kernel

end CertificateChecks.Batch16024

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Tri CFSG.Monster.Tri.Leech CFSG.Monster.SpinLattice
  CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.B.Short CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.KstabMaximal in
theorem certificate16024 : (
    leechIdx3.size = 275
  ) ∧ (
    leechIdx4.size = 88
  ) := by
  exact ⟨CertificateChecks.Batch16024.leechIdx3_size_0, CertificateChecks.Batch16024.leechIdx4_size_1⟩

end Certificates
