
module

public import Certificates.Certificate3075Base


public section

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Sp8

namespace CertificateChecks.Batch3075

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Sp8

end CertificateChecks.Batch3075

namespace Certificates

open CertificateChecks

open CFSG.Monster.Code CFSG.Monster.B.TwoA.Sp8 in
theorem certificate3075 : ∀ k : Fin 45, ∀ i j : Fin 8,
      ∑ a : Fin 8, ∑ b : Fin 8, bvec 8 (genRow k i) a * bvec 8 (gramRows.getD a 0) b *
        bvec 8 (genRow k j) b = bvec 8 (gramRows.getD i 0) j := by
  intro k i j
  rw [CertificateChecks.Batch3075.sum_eq _ _ (fun a => gramRows.getD a 0)]
  exact CertificateChecks.Batch3075.kGram k i j

end Certificates
