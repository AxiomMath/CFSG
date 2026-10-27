
module

public import Certificates.Certificate3057Base


public section

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Code CertificateChecks.Sp8Fold

namespace CertificateChecks.Batch3057

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B CFSG.Monster.B.Rep4371 CFSG.Monster.B.TwoA.Census
  CFSG.Monster.Code CertificateChecks.Sp8Fold

end CertificateChecks.Batch3057

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.TwoA.Sp8 CFSG.Monster.B in
theorem certificate3057 : (∀ v w : Fin 8 → ZMod 2, foldP (v + w) = Model.Pauli.mul (foldP v) (foldP w)) ∧
      (∀ k : Fin 8, foldP (Pi.single k 1) = liftP k) ∧
      (∀ v : Fin 8 → ZMod 2, foldP v = (false, 0, 0) → v = 0) ∧
      (∀ v : Fin 8 → ZMod 2, foldP v = (false, 0, 191) → v = Pi.single 7 1) ∧
      (∀ v : Fin 8 → ZMod 2, (foldP v).2.1 < 2 ^ 12 ∧ (foldP v).2.2 < 2 ^ 12) ∧
      (∀ v : Fin 8 → ZMod 2, Model.conjYN 3 (foldP v) = foldP v) :=
  ⟨CertificateChecks.Batch3057.foldP_add, CertificateChecks.Batch3057.foldP_single, CertificateChecks.Batch3057.foldP_eq_one, CertificateChecks.Batch3057.foldP_eq_r,
    Sp8Fold.foldP_lt, CertificateChecks.Batch3057.conjYN_foldP⟩

end Certificates
