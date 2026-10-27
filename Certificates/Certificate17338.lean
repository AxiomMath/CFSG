module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
import Certificates.Kernel.Fi23Cls.Glue

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Fi23 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 in
theorem certificate17338 : 
    (orderOf (t3 0) = 3 ∧ ∃ p : Fin 31671, t3 0 • p = p ∧
      Nat.card {r : Fin 31671 // t3 0 • r = r} = 351 ∧
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ t3 0 • r = r} = 126 ∧
      ∀ r : Fin 31671, t3 0 • r = r →
        ∃ g ∈ Subgroup.centralizer ({t3 0} : Set J), g • p = r) ∧
    (orderOf (t3 1) = 3 ∧ ∃ p : Fin 31671, t3 1 • p = p ∧
      Nat.card {r : Fin 31671 // t3 1 • r = r} = 324 ∧
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ t3 1 • r = r} = 27 ∧
      ∀ r : Fin 31671, t3 1 • r = r →
        ∃ g ∈ Subgroup.centralizer ({t3 1} : Set J), g • p = r) ∧
    (orderOf (t3 2) = 3 ∧ ∃ p : Fin 31671, t3 2 • p = p ∧
      Nat.card {r : Fin 31671 // t3 2 • r = r} = 135 ∧
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ t3 2 • r = r} = 36 ∧
      ∀ r : Fin 31671, t3 2 • r = r →
        ∃ g ∈ Subgroup.centralizer ({t3 2} : Set J), g • p = r) ∧
    (orderOf (t3 3) = 3 ∧ ∃ p : Fin 31671, t3 3 • p = p ∧
      Nat.card {r : Fin 31671 // t3 3 • r = r} = 27 ∧
      Nat.card {r : Fin 31671 // r ≠ p ∧
        conjPt r.val * conjPt p.val = conjPt p.val * conjPt r.val ∧ t3 3 • r = r} = 0 ∧
      ∀ r : Fin 31671, t3 3 • r = r →
        ∃ g ∈ Subgroup.centralizer ({t3 3} : Set J), g • p = r) :=
  KernelFi23Cls.classFacts

end Certificates
