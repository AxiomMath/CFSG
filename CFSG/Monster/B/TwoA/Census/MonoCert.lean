module

public import CFSG.Monster.B.TwoA.Census.MonoData
public import CFSG.Monster.B.TwoA.Census.SignCls
public import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.MonoData
public meta import CFSG.Monster.B.TwoA.Census.SignCls
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public import CFSG.Monster.B.TwoA.Census.MonoCertInputs
public import Certificates.Certificate3016

public section

namespace CFSG.Monster.B.TwoA.Census

open CFSG.Monster.Code

theorem monoCert_ok :
    ∀ i < 7, natCertOK (actJ (monoSeed.getD i 0)) (ngenJ (monoSeed.getD i 0))
    (validB (monoSeed.getD i 0)) (monoSign.getD i 0) (monoCert i) = true :=
  Certificates.certificate3016.1

theorem monoCert_size :
    ∀ i < 7, (monoCert i).pts.size = [1, 759, 1288, 16, 112, 32, 32].getD i 0 :=
  Certificates.certificate3016.2.1

theorem eligList_length :
    ∀ j < 3, (eligList j).length = [2048, 128, 64].getD j 0 :=
  Certificates.certificate3016.2.2.1

theorem monoCert_partition : ∀ j < 3,
    (((List.range 7).filter (fun i => monoSeed.getD i 0 == j)).flatMap
      (fun i => (monoCert i).pts.toList)).mergeSort (fun a b => decide (a ≤ b)) =
    (eligList j).mergeSort (fun a b => decide (a ≤ b)) :=
  Certificates.certificate3016.2.2.2.1

theorem permI_spec_seed : ∀ j < 3, ∀ n ∈ validList,
    bvec 24 (permI (seedA j) n) = bvec 24 n ∘ arrFun (ainv (seedA j)) :=
  Certificates.certificate3016.2.2.2.2.1

theorem permI_spec_seed_basis : ∀ j < 3, ∀ k < 12,
    bvec 24 (permI (seedA j) (Bmask k)) = bvec 24 (Bmask k) ∘ arrFun (ainv (seedA j)) :=
  Certificates.certificate3016.2.2.2.2.2.1

theorem permI_spec_cent :
    ∀ j < 3, ∀ a ∈ centGenArrs j, ∀ n ∈ validList,
    bvec 24 (permI a n) = bvec 24 n ∘ arrFun (ainv a) :=
  Certificates.certificate3016.2.2.2.2.2.2.1

theorem permI_seed_lt :
    ∀ j < 3, ∀ n ∈ validList, permI (seedA j) n < 2 ^ 24 :=
  Certificates.certificate3016.2.2.2.2.2.2.2

end CFSG.Monster.B.TwoA.Census
