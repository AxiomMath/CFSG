module

public import Certificates.Data.TabFi22Cent
import Certificates.Kernel.Sporadic.Fi22.Cent17336G

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabFi22Cent in
open CFSG.Monster.B.Fischer (fi22P) in
theorem certificate17336 : ∃ d x : Equiv.Perm (Fin 3510),
    (∀ v : Fin 3510, (dArr ())[(v : ℕ)]! = d v) ∧ (∀ v : Fin 3510, (CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.xArr ())[(v : ℕ)]! = x v) ∧
    d ∈ fi22P ∧ x ∈ fi22P ∧ d * d = 1 ∧ x ^ 3 = 1 ∧ x ≠ 1 ∧ (d * x) * (d * x) = 1 ∧
    x 0 = 1 ∧ x 1 ≠ 0 ∧ x 1 ≠ 1 ∧ Nat.card {v : Fin 3510 // x v = v} = 126 ∧
    (∀ g ∈ fi22P, g 0 = 0 → g * d = d * g) ∧
    (∀ g ∈ fi22P, g 0 = 0 → g 1 = 1 → g * x = x * g) ∧
    (∀ g ∈ fi22P, g * x = x * g → g 0 = 0 ∨ g 0 = 1 ∨ g 0 = x 1) :=
  KernelSpor.Cent17336.facts

end Certificates
