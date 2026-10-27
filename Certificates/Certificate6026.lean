module

public import CFSG.Monster.Existence.EbCheck
import Certificates.Kernel.MonsterExist.Eb.Check

public section

namespace Certificates

open CertificateChecks.MonsterExist.Eb in
open CFSG CFSG.Monster CFSG.Monster.Existence in
theorem certificate6026 : (case1OK = true)
    ∧ (class0OK = true)
    ∧ (isShortX (packP (false, 3, 60)) = true ∧ isShortX (packP (false, 60, 60)) = false ∧
      isShortX (packP (false, 3, 48)) = false ∧ isShortX (packP (false, 734, 0)) = false) :=
  ⟨case1OK_true, class0OK_true, witness_shortness⟩

end Certificates
