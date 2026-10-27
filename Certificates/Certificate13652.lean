module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23Reps
import Certificates.Kernel.Fi23Q.RestateGlue

public section

namespace Certificates

open CertificateChecks

open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23 in
theorem certificate13652 : 
    (∀ s : CFSG.Sporadic.Fi23.J, orderOf s = 3 → ∃ c : Fin 4, IsConj s (t3 c)) ∧
      (∃ P : Sylow 3 CFSG.Sporadic.Fi23.J,
        (P : Subgroup CFSG.Sporadic.Fi23.J) ≤ Subgroup.centralizer {zJ}) ∧
      IsConj CFSG.Sporadic.Fi23.d (CFSG.Sporadic.Bridge.Fi23.img 2) :=
  KernelFi23Q.three_classes_J

end Certificates
