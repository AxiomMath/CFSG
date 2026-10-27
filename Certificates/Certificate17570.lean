module

public import Certificates.Kernel.Sporadic.Fi24Pair.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

attribute [local instance] CFSG.Sporadic.Fi24.rAction

theorem certificate17570_of_bridge
    (hL : ∀ l < 26, ∀ x : Fin 306936,
      ((CFSG.Perm.pairG CFSG.Sporadic.Fi24.gs l) • x).val = CFSG.KS.Fi24Net.LN CFSG.KD.Fi24Net.NW l x.val)
    (hC : ∀ k p : Fin 306936,
      (CFSG.Sporadic.Fi24.cls k • p).val =
        CFSG.KC.Fi24Kit.clsK CFSG.KD.Fi24Orb.OL CFSG.KD.Fi24Kit.NT k.val p.val)
    (hlv : CFSG.Perm.Native.levelLetters CFSG.Sporadic.Fi24.letters
      CFSG.Sporadic.Fi24.Native.chainBase 2 =
        #[8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) :
 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Fi24PairOrbitFacts :=
  by
    intros
    exact CFSG.KD.Fi24Pair.Group.fi24PairOrbitFacts_of hL hC hlv

theorem certificate17570 : 
    CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi24Three.Fi24PairOrbitFacts :=
  certificate17570_of_bridge (KernelFi24OrbL.bridge.letter)
    (KernelFi24OrbL.bridge.cls) (by
      intros
      rw [KernelFi24OrbL.levelLetters_eq 2 (by norm_num)]
      decide)

end Certificates
