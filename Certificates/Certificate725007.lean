module

public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.Sporadic.SmallOddCore.J2Data
import Certificates.Kernel.W4Row.J2Cent
import Certificates.Kernel.W4Row.J2CentK
import CFSG.Certificates.Kernel.Common.Harness
import CFSG.Certificates.Kernel.Common.StrLits
import CFSG.Certificates.Kernel.Spor.RawOrbGrp
import CFSG.GroupTheory.LocalCores.Fitting
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeDim
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeTrans
import CFSG.Sporadic.M23.M23Group
import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
theorem certificate725007 : ∀ B : Subgroup (Equiv.Perm (Fin 315)), B ≤ j2R →
    (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) → Nat.card B = 16 →
    ∃ d ∈ B, ∃ e ∈ B, d ≠ 1 ∧ e ≠ 1 ∧ j2P ≤ Subgroup.closure
      (((j2P ⊓ Subgroup.centralizer {d} : Subgroup (Equiv.Perm (Fin 315))) :
        Set (Equiv.Perm (Fin 315))) ∪ (j2P ⊓ Subgroup.centralizer {e} :
          Subgroup (Equiv.Perm (Fin 315)))) :=
  CFSG.KD.W4C.J2Cent.holds

end Certificates
