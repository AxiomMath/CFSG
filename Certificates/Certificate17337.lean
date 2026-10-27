module

public import Certificates.Data.TabFi22Cent
import Certificates.Kernel.Sporadic.Fi22.L17337G

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Dickson.I271.TabFi22Cent in
open CFSG.Monster.B.Fischer (fi22P) in
theorem certificate17337 : ∃ a b : Equiv.Perm (Fin 3510),
    (∀ v : Fin 3510, ((lArrs ())[0]!)[(v : ℕ)]! = a v) ∧
    (∀ v : Fin 3510, ((lArrs ())[1]!)[(v : ℕ)]! = b v) ∧
    Nat.card (Subgroup.closure {a, b}) = 3265920 ∧ a ∈ fi22P ∧ b ∈ fi22P ∧
    a 0 = 0 ∧ a 1 = 1 ∧ b 0 = 0 ∧ b 1 = 1 ∧
    (∀ x : Equiv.Perm (Fin 3510), (∀ v : Fin 3510, (CFSG.HardMathSupport.Dickson.I271.TabFi22Cent.xArr ())[(v : ℕ)]! = x v) →
      a * x = x * a ∧ b * x = x * b) ∧
    ∀ w ∈ relsU43, (w.map fun l => cond l.2 (![a, b] l.1) (![a, b] l.1)⁻¹).prod = 1 :=
  KernelSpor.L17337.facts

end Certificates
