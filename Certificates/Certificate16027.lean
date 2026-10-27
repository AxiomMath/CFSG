module

public import CFSG.Monster.B.Pinned.Primes.FiveSubgroupInputs
public import CFSG.RankThree.Native.DerivedGenerators
public import Certificates.Certificate3027
public import Certificates.Certificate3106

public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Blueprint

namespace CertificateChecks.Batch16027

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Blueprint

private theorem MFive_mul_inv_0 : MFive * rowsMat 5 4 fiveCommInvRows = 1 := by
  decide +kernel

private theorem xFive_not_mem_1 : MFive 0 ≠ MFive 2 := by
  decide +kernel

end CertificateChecks.Batch16027

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.Pinned CFSG.Blueprint in
theorem certificate16027 : (
    MFive * rowsMat 5 4 fiveCommInvRows = 1
  ) ∧ (
    MFive 0 ≠ MFive 2
  ) := by
  exact ⟨CertificateChecks.Batch16027.MFive_mul_inv_0, CertificateChecks.Batch16027.xFive_not_mem_1⟩

end Certificates
