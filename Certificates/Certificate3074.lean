
module

public import Certificates.Certificate3074Base
import all Certificates.Certificate3074Base

public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
meta import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
meta import CFSG.Monster.B.TwoA.Sp8.GenActionDiffBase

public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

namespace CertificateChecks.Batch3074

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

end CertificateChecks.Batch3074

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code in
theorem certificate3074 : (∀ k : Fin 44, ∀ j : Fin 7, genRow k j < 128 ∧
       (h1ConjN k (liftP j.castSucc) = foldP (bvec 8 (genRow k j)) ∨
         h1ConjN k (liftP j.castSucc) = foldP (bvec 8 (genRow k j) + Pi.single 7 1)))
    ∧ (∀ k : Fin 44, 128 ≤ genRow k 7 ∧ genRow k 7 < 256 ∧
       (gDiff k = foldP (bvec 8 (genRow k 7)) ∨
         gDiff k = foldP (bvec 8 (genRow k 7) + Pi.single 7 1))) := by
  exact ⟨CertificateChecks.Batch3074.liftRowCheck_0, CertificateChecks.Batch3074.liftDiffCheck_1⟩

end Certificates
