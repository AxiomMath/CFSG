module

public import Certificates.Kernel.Sporadic.Fi24ThreeAK.Group
import Certificates.Kernel.Sporadic.Fi24OrbL.Cls

public section

namespace Certificates

open CertificateChecks

theorem certificate17353_of_bridge
    (hB : 
      CFSG.KD.Fi24ThreeO.Group.Bridge)
    (hlv : CFSG.Perm.Native.levelLetters
      CFSG.Sporadic.Fi24.letters CFSG.Sporadic.Fi24.Native.chainBase 2 =
      #[8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25]) :
    CFSG.HardMathSupport.Dickson.I271.TabFi24.ThreeAFacts :=
  by
    exact CFSG.KD.Fi24ThreeAK.Group.threeAFacts_of hB hlv

theorem certificate17353 : 
    CFSG.HardMathSupport.Dickson.I271.TabFi24.ThreeAFacts :=
  certificate17353_of_bridge KernelFi24OrbL.bridge (by
    intros
    rw [KernelFi24OrbL.levelLetters_eq 2 (by norm_num)]
    decide)

end Certificates
