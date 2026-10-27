module

public import CFSG.Monster.B.GSide.EdgeQCertP2Inputs
public import CFSG.Certificates.Kernel.Common.BvecLoop

public section

open CFSG.Monster.B.GSide CFSG.Monster.B CFSG.Monster.Code CFSG.KC.BvecLoop

namespace CertificateChecks.Batch3043

open CFSG.Monster.B.GSide CFSG.Monster.B CFSG.Monster.Code CFSG.KC.BvecLoop

theorem arr_checks_0 :
    p2Arr (wordA ++ wordA ++ wordA ++ wordA) = arrId ∧
    p2Arr (wordB ++ wordB ++ wordB ++ wordB) = arrId ∧
    p2Arr (wordB ++ wordA) = p2Arr (wordA ++ wordB) := by
  decide +kernel

theorem fixed_codes : ∀ x < 2 ^ 10,
    (Model.permWordN (p2Arr wordA) (coeffMask (bvec 10 x)) ^^^ coeffMask (bvec 10 x) = 0 ∨
      Model.permWordN (p2Arr wordA) (coeffMask (bvec 10 x)) ^^^ coeffMask (bvec 10 x) =
        2 ^ 24 - 1) →
    (Model.permWordN (p2Arr wordB) (coeffMask (bvec 10 x)) ^^^ coeffMask (bvec 10 x) = 0 ∨
      Model.permWordN (p2Arr wordB) (coeffMask (bvec 10 x)) ^^^ coeffMask (bvec 10 x) =
        2 ^ 24 - 1) →
    (coeffMask (bvec 10 x) ^^^ 0 = 0 ∨ coeffMask (bvec 10 x) ^^^ 0 = 2 ^ 24 - 1 ∨
      coeffMask (bvec 10 x) ^^^ vStar = 0 ∨ coeffMask (bvec 10 x) ^^^ vStar = 2 ^ 24 - 1) := by
  decide +kernel

end CertificateChecks.Batch3043

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.GSide CFSG.Monster.B in
theorem certificate3043 : (p2Arr (wordA ++ wordA ++ wordA ++ wordA) = arrId ∧
       p2Arr (wordB ++ wordB ++ wordB ++ wordB) = arrId ∧
       p2Arr (wordB ++ wordA) = p2Arr (wordA ++ wordB))
    ∧ (∀ c : Fin 10 → ZMod 2,
       (Model.permWordN (p2Arr wordA) (coeffMask c) ^^^ coeffMask c = 0 ∨
         Model.permWordN (p2Arr wordA) (coeffMask c) ^^^ coeffMask c = 2 ^ 24 - 1) →
       (Model.permWordN (p2Arr wordB) (coeffMask c) ^^^ coeffMask c = 0 ∨
         Model.permWordN (p2Arr wordB) (coeffMask c) ^^^ coeffMask c = 2 ^ 24 - 1) →
       (coeffMask c ^^^ 0 = 0 ∨ coeffMask c ^^^ 0 = 2 ^ 24 - 1 ∨ coeffMask c ^^^ vStar = 0 ∨
         coeffMask c ^^^ vStar = 2 ^ 24 - 1)) :=
  ⟨CertificateChecks.Batch3043.arr_checks_0, forall_bvec.2 CertificateChecks.Batch3043.fixed_codes⟩

end Certificates
