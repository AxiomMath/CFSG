module

public import CFSG.LocalAnalysis.StandardType.GGK0StageDefs
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate1952
public import Certificates.Certificate2264
public import Certificates.Certificate2267
public import Certificates.Certificate3951
public import Certificates.Certificate8033
public import Certificates.Certificate8064
public import Certificates.Certificate13659
public import Certificates.Certificate13660
import CFSG.LocalAnalysis.StandardType.GGK0StageAssembly
import CFSG.LocalAnalysis.StandardType.GGK0PositionsLeaf
import CFSG.LocalAnalysis.StandardType.GGK0LCLeaf
import CFSG.LocalAnalysis.StandardType.GGK0LQ1
import CFSG.LocalAnalysis.StandardType.GGK0LQ2
import CFSG.LocalAnalysis.StandardType.GGK0LQ3
import CFSG.LocalAnalysis.StandardType.GGK0LQ4
import CFSG.LocalAnalysis.StandardType.GGK0LEA12TwE6

public section

namespace CFSG.StandardType.GGK0MarkedKacIface1587

open CFSG CFSG.Assembly CFSG.StandardType

variable {Omega : Type} [Field Omega] [IsAlgClosed Omega] [CharP Omega 2]

theorem rationalProducerOn_of_langMark
    {tag : LargeEvenLieTag} (hAlg : ∀ c : Omega, ∃ n : ℕ, 0 < n ∧ c ^ (2 ^ n) = c)
    (hA : ∀ p : ℕ, ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → GGKacExcPair lab p →
      lab.tag = tag → LargeEvenLabelAll lab (fun R _ I _ => ∀ phi : MulAut R, phi ∈ I →
        orderOf phi = p → Nonempty (K0LangMark Omega lab p R I phi))) :
    RationalProducerOn Omega tag := fun p lab hlab hpair htag =>
  rationalAt_of_stages (hA p lab hlab hpair htag) (fun A => k0Positions_nonempty A)
    (fun A P j hj => k0_rationalComponent_quasisimple hlab hpair A P j hj)
    (fun A P j hj => k0_coreFactor_label hlab hpair A P j hj)
    (fun A P j hj => k0_rationalSpan_solvable hlab hpair A P j hj)
    (fun A P j hj hqs => k0_fullFactor_a12 hlab hpair hAlg A P j hj hqs)
    (fun A P j hj hqs u hu => k0_fullFactor_a12_invariant hlab hpair hAlg A P hlab.1 hpair.1
      hpair.2.2.1 j hj hqs u hu)
    (fun A hc => k0_centralizer_generated hlab hpair A hc)

end CFSG.StandardType.GGK0MarkedKacIface1587

end
