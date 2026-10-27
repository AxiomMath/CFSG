module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
import Certificates.Kernel.Fi23Q.SubClsPure

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 in
theorem certificate101703 : 
    ∃ S : Subgroup J, S ≤ Subgroup.centralizer ({conjPt 770} : Set J) ∧ Nat.card S = 3 ^ 9 ∧
      ∀ D ≤ S, CFSG.Open.IsElemAbelian 3 D → Nat.card D = 3 ^ 4 →
        ∃ x ∈ D, x ≠ 1 ∧ (IsConj x (t3 0) ∨ IsConj x (t3 2)) :=
  KernelFi23Q.sub_pure

end Certificates
