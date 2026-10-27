module

public import Certificates.Data.GH74.McLSylowThree
import Certificates.Kernel.McLAS.NoThreeF
public import CFSG.Sporadic.Schreier.PairMcLCertBase
public import CFSG.Sporadic.SmallOddCore.CentSpec

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Recognition.McLAS CFSG.Sporadic.SmallOddCore CFSG.Sporadic.Schreier in
theorem certificate5187 : ∀ W : Subgroup (Equiv.Perm (Fin 275)), W ≤ mclP → IsPGroup 3 ↥W →
    Subgroup.closure (tp 275 '' {x | x ∈ sylTwoGens}) ≤
      Subgroup.normalizer (W : Set (Equiv.Perm (Fin 275))) → W = ⊥ := KernelMcLAS.NoThr.noThree_sylTwo

end Certificates
