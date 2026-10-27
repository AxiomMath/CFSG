module

public import Certificates.Kernel.XiFusion.Arr
public import Certificates.Kernel.XiFusion.Perm
public import Certificates.Kernel.XiFusion.Target

public section

namespace Certificates

open CertificateChecks.KernelXiFusion

open CFSG.Monster.B.TwoA.Census CFSG.Monster.Code in
theorem certificate3020 : (∀ e ∈ xiEdges,
       mulArr (xiArrA e) (xiArrM e) = mulArr (xiArrM e) (xiArrR e))
    ∧ (∀ e ∈ xiEdges, bvec 24 e.conjSign ∈ C ∧ bvec 24 e.afterSign ∈ C)
    ∧ (∀ e ∈ xiEdges, AutArr e.afterPerm ∧ AutArr e.normalizer)
    ∧ (∀ e ∈ xiEdges, e.target < 7 ∧
       amul (amul e.normalizer e.afterPerm) (ainv e.normalizer) =
         seedA (monoSeed.getD e.target 0))
    ∧ (∀ e ∈ xiEdges,
       bvec 24 (permI e.afterPerm e.afterSign) = bvec 24 e.afterSign ∘ arrFun (ainv e.afterPerm) ∧
       bvec 24 (permI e.normalizer (permI e.afterPerm e.afterSign)) =
         bvec 24 (permI e.afterPerm e.afterSign) ∘ arrFun (ainv e.normalizer))
    ∧ (∀ e ∈ xiEdges,
       canI (permI e.normalizer (permI e.afterPerm e.afterSign)) ∈ (monoCert e.target).pts.toList) :=
  ⟨arr_check, code_check, aut_check, seed_check, spec_check, target_mem⟩

end Certificates
