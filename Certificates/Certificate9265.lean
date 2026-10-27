module

public import CFSG.Monster.Schur.CentralEps
public import CFSG.Monster.Schur.M24.Twist
import Certificates.Kernel.Schur.Twisted

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.Schur CFSG.Monster.Schur.M24 in
open CFSG.CosetTable in
theorem certificate9265 : ∀ c : Bool, Finite (PG (2 + 1) (epsRels U CFSG.Monster.Schur.M24.T5 ![true, c, true, true, true])) ∧
    Nat.card (PG (2 + 1) (epsRels U CFSG.Monster.Schur.M24.T5 ![true, c, true, true, true])) ≤ 244823040 :=
  fun _ => KernelSchur.bound_twisted _ _ _ _ _ (by simp)

end Certificates
