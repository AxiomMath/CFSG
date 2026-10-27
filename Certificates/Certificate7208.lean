module

public import CFSG.Sporadic.SmallOddCore.HSLocal
import Certificates.Kernel.SporSch.PairHS.HS7208Facts
import Certificates.Kernel.SporSch.PairHS.HS7208Fns
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Certificate2218
import Certificates.Certificate2219
import Certificates.Certificate2272
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.Certificates.Kernel.Spor.ONKSound
import CFSG.Certificates.Kernel.SporSch.PairClTSound

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier Subgroup in
theorem certificate7208 :
    (∀ S : Subgroup (Equiv.Perm (Fin 3850)), S ≤ hsC2 → Nat.card S = 64 →
        Nat.card ↥(hsR ⊓ centralizer (S : Set (Equiv.Perm (Fin 3850)))) ≤ 4) ∧
    (∀ b c, b ∈ hsC2 → c ∈ hsC2 → b * c = c * b → b ≠ 1 → c ≠ 1 → b * b = 1 → c * c = 1 →
        b ≠ hsT2 → c ≠ hsT2 → c ≠ b → c ≠ hsT2 * b →
        (∀ x ∈ ({b, c, b * c, hsT2 * b, hsT2 * c, hsT2 * (b * c)} : Set (Equiv.Perm (Fin 3850))),
          ∃ g ∈ hsP, x = g * hsT2 * g⁻¹) →
        False) := KernelSporSch.HS78.facts7208

end Certificates
