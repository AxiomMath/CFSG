module

public import CFSG.Quasithin.Recognition.RuTypeJ27eInputs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsBasic
public import Certificates.Certificate17033

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma CFSG.QuasithinUnique

namespace CertificateChecks.Batch17010

open CFSG CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma CFSG.QuasithinUnique

private theorem no_order_fifteen_0 :  ∀ g : SigmaL2F4, g ^ 15 = 1 → g ^ 3 = 1 ∨ g ^ 5 = 1  := by
  decide +kernel

private theorem m10_check_1 :  ∀ c ∈ A6Facts.Core.pslLit, ∀ r ∈ [A6Facts.code 1,
    A6Facts.code A6Models.tMulFrob],
    cpow (A6Facts.Core.cmul c r) 15 = A6Facts.Core.cid →
      cpow (A6Facts.Core.cmul c r) 3 = A6Facts.Core.cid ∨
        cpow (A6Facts.Core.cmul c r) 5 = A6Facts.Core.cid  := by
  decide +kernel

private theorem x5_pow_five_2 :  x5 ^ 5 = 1  := by
  decide +kernel

private theorem x5_ne_one_3 :  x5 ≠ 1  := by
  decide +kernel

end CertificateChecks.Batch17010

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.RuType CFSG.Quasithin.RuType.Sigma CFSG.QuasithinUnique in
theorem certificate17010 : (
 ∀ g : SigmaL2F4, g ^ 15 = 1 → g ^ 3 = 1 ∨ g ^ 5 = 1 
)
    ∧ (
 ∀ c ∈ A6Facts.Core.pslLit, ∀ r ∈ [A6Facts.code 1,
    A6Facts.code A6Models.tMulFrob],
    cpow (A6Facts.Core.cmul c r) 15 = A6Facts.Core.cid →
      cpow (A6Facts.Core.cmul c r) 3 = A6Facts.Core.cid ∨
        cpow (A6Facts.Core.cmul c r) 5 = A6Facts.Core.cid 
)
    ∧ (
 x5 ^ 5 = 1 
)
    ∧ (
 x5 ≠ 1 
) := by
  exact ⟨@CertificateChecks.Batch17010.no_order_fifteen_0, @CertificateChecks.Batch17010.m10_check_1, @CertificateChecks.Batch17010.x5_pow_five_2, @CertificateChecks.Batch17010.x5_ne_one_3⟩

end Certificates
