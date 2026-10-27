
module

public import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
meta import CFSG.Monster.B.TwoA.Sp8.GenActionConjInputs
meta import CFSG.Monster.B.TwoA.Sp8.GenActionDiffBase

@[expose] public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.Code

namespace CertificateChecks.Batch3074

private theorem liftRowCheck_0 :
    ∀ k : Fin 44, ∀ j : Fin 7, genRow k j < 128 ∧
    (h1ConjN k (liftP j.castSucc) = foldP (bvec 8 (genRow k j)) ∨
      h1ConjN k (liftP j.castSucc) = foldP (bvec 8 (genRow k j) + Pi.single 7 1)) := by
  decide +kernel

private theorem liftDiffCheck_1 :
    ∀ k : Fin 44, 128 ≤ genRow k 7 ∧ genRow k 7 < 256 ∧
    (gDiff k = foldP (bvec 8 (genRow k 7)) ∨
      gDiff k = foldP (bvec 8 (genRow k 7) + Pi.single 7 1)) := by
  decide +kernel

end CertificateChecks.Batch3074

namespace Certificates

end Certificates
