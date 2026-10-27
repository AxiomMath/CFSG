module

public import CFSG.Monster.B.Fischer.Fi22Graph
public import CFSG.Sporadic.FischerOddCore.Fi22Ext
public import CFSG.LocalAnalysis.ComponentClassification.M12CoverAutCentralizers
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
import Certificates.Certificate2067
import Certificates.Certificate3037
import Certificates.Certificate3039
import Certificates.Certificate3147
import Certificates.Certificate3154
import Certificates.Kernel.Sporadic.Fi22.HypCBGlue
import Certificates.Kernel.Sporadic.Fi22.HypWSound
import CFSG.Monster.B.Fischer.Fi22Model
import Certificates.Kernel.Sporadic.Fi22.C2068

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.B.Fischer CFSG.Sporadic.FischerOddCore CFSG.ComponentClassification.M12Cover in
open CFSG.Sporadic.Schreier in
theorem certificate25640 : (∀ k < 6, ∃ c ∈ fi22R, c ∉ fi22P ∧ c * fi22ExtRep k = fi22ExtRep k * c) ∧
    (∀ k, 3 ≤ k → k < 6 →
      ∃ l ∈ fi22P, orderOf (l * fi22ExtRep k * l⁻¹ * (fi22ExtRep k)⁻¹) = 2) ∧
    FourClassesLarge ↥(CFSG.Sporadic.Schreier.centralizerIn fi22R (fi22ExtRep 3)) ∧
    FourClassesLarge ↥(CFSG.Sporadic.Schreier.centralizerIn fi22R (fi22ExtRep 4)) ∧
    FourClassesLarge ↥(CFSG.Sporadic.Schreier.centralizerIn fi22R (fi22ExtRep 5)) :=
  ⟨fun _ hk => KernelSpor.Fi22W.exists_comm_not_mem hk,
    fun _ h3 hk => KernelSpor.Fi22W.exists_fours h3 hk, KernelSpor.Fi22CB.fourClassesLarge_CR3,
    KernelSpor.Fi22CB.fourClassesLarge_CR4, KernelSpor.Fi22CB.fourClassesLarge_CR5⟩

end Certificates
