
module

public import Certificates.Certificate3060Base


public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Code CertificateChecks.Sp8Fold

namespace CertificateChecks.Batch3060

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Code CertificateChecks.Sp8Fold

end CertificateChecks.Batch3060

namespace Certificates

open CertificateChecks

open CFSG.Monster.B CFSG.Monster.B.TwoA.Sp8 in
theorem certificate3060 : (∀ v : Fin 8 → ZMod 2, Model.Pauli.mul (false, 0, 127) (foldP v) =
        Model.Pauli.mul (foldP v) (false, 0, 127)) ∧
      (∀ v : Fin 8 → ZMod 2, Model.Pauli.mul (false, 0, 127) (foldP v) ≠ (false, 0, 0) ∧
        Model.Pauli.mul (false, 0, 127) (foldP v) ≠ (false, 0, 191)) ∧
      (∀ v : Fin 8 → ZMod 2, (Model.Pauli.mul (false, 0, 127) (foldP v)).2.1 < 2 ^ 12 ∧
        (Model.Pauli.mul (false, 0, 127) (foldP v)).2.2 < 2 ^ 12) ∧
      Model.Pauli.mul (false, 0, 127) (false, 0, 127) = (false, 0, 0) ∧
      Model.conjYN 3 (false, 0, 127) = (false, 0, 127) :=
  ⟨CertificateChecks.Batch3060.comm_foldP, CertificateChecks.Batch3060.ne_foldP, fun v => CertificateChecks.Batch3060.c_lt _ (Sp8Fold.foldP_lt v),
    CertificateChecks.Batch3060.closed.1, CertificateChecks.Batch3060.closed.2⟩

end Certificates
