module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Kc3J

public section

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3J

namespace CertificateChecks.Batch17029

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3J

private theorem a0_pow_0 :  Delta5.a0 ^ 5 = 1  := by
  decide +kernel

private theorem b0_pow_1 :  Delta5.b0 ^ 3 = 1  := by
  decide +kernel

end CertificateChecks.Batch17029

namespace Certificates

open CertificateChecks

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.A5 CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique.A5.Kc3J in
theorem certificate17029 : (
 Delta5.a0 ^ 5 = 1 
)
    ∧ (
 Delta5.b0 ^ 3 = 1 
) := by
  exact ⟨@CertificateChecks.Batch17029.a0_pow_0, @CertificateChecks.Batch17029.b0_pow_1⟩

end Certificates
