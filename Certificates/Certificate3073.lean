
module

public import Certificates.Certificate3073Base

public import CFSG.Certificates.Kernel.MonsterB.Sp8XiClifford

public section

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Co2Inv
open CFSG.KC.KDense CFSG.KC.Rep4371Row CFSG.KC.Sp8Span

namespace CertificateChecks.Batch3073

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Co2Inv
open CFSG.KC.KDense CFSG.KC.Rep4371Row CFSG.KC.Sp8Span

open CertificateChecks.Sp8Rows3073 CertificateChecks.Sp8Xi3073

theorem xiKeyCheck_3 : Native.Sp8.xiKeyCheck (gDiff 43) = true :=
  CFSG.KC.Sp8Xi.xiKeyCheck_of_checks (false, 60, 60) (by decide) xi_labels xi_key

end CertificateChecks.Batch3073

namespace Certificates

open CertificateChecks

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B.Rep4371 in
theorem certificate3073 : (∀ k < 23,
       Model.conjYN 3 (pauliGen k) = Model.Pauli.mul (pauliGen k) (gDiff k))
    ∧ (∀ j < 9,
       Native.Sp8.rowChainEq (Native.eYN 3 :: permFs Native.ePermN Native.ePauliN Native.kappaN j)
         (permFs Native.ePermN Native.ePauliN Native.kappaN j ++
           [Native.ePauliN (gDiff (23 + j)), Native.eYN 3]) = true)
    ∧ (∀ j < 11,
       Native.Sp8.rowChainEq (Native.eYN 3 :: signFs Native.eYN j)
         (signFs Native.eYN j ++ [Native.ePauliN (gDiff (32 + j)), Native.eYN 3]) = true)
    ∧ (Native.Sp8.xiKeyCheck (gDiff 43) = true) :=
  ⟨CertificateChecks.Batch3073.pauliDiff_check_0, CertificateChecks.Batch3073.permRows_1, CertificateChecks.Batch3073.signRows_2,
    CertificateChecks.Batch3073.xiKeyCheck_3⟩

end Certificates
