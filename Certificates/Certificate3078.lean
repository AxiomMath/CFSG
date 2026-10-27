
module


public import CFSG.Monster.B.TwoA.Sp8.QuadCosetCInputs
import Certificates.Kernel.MonsterB.Quad3078.Glue

public section

open CFSG.Monster.B.TwoA.Sp8 CertificateChecks.KernelMonB.Quad3078

namespace Certificates

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.Code in
theorem certificate3078 : (∀ k < 44,
       (h1ConjN k (false, 0, 127) = Model.Pauli.mul (false, 0, 127) (foldP (cImg k)) ∨
         h1ConjN k (false, 0, 127) = Model.Pauli.mul (false, 0, 127)
           (foldP (cImg k + Pi.single 7 1))) ∧
       cImg k 7 = 0)
    ∧ (∀ k < 45, ∀ n < 256,
       bvec 8 (affN k n) = affM k (bvec 8 n) ∧ affN k n < 256)
    ∧ (∀ n < 256, qPoly (bvec 8 n) = if qN n then 1 else 0)
    ∧ (∀ k < 45, ∀ n < 256, qN (affN k n) = qN n)
    ∧ (∀ k < 45, ∀ n < 256, (affTab[k]!)[n]! = affN k n)
    ∧ (∀ n < 256, zeroTab[n]! = !qN n)
    ∧ (affTab.size = 45)
    ∧ (CFSG.Monster.B.Sp8.Native.pairCheck affTab zeroTab 1 = true) :=
  ⟨cImg_ok, fun _ hk n hn => affN_spec' hk n hn, qPoly_ok, fun _ hk _ hn => qN_affN' hk hn,
    fun _ hk _ hn => affTab_get' hk hn, fun _ hn => zeroTab_get' hn, affTab_size', pairCheck_ok⟩

end Certificates
