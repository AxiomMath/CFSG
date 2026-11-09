module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.S5FiveYHsData
import Certificates.Kernel.Misc.Perm.HS100.X3Glue
import Certificates.Kernel.Misc.Perm.HS100.X3ClsGlue

public section

open CFSG.EvenSporadicStandard.HSStd.FiveY

namespace Certificates

open CertificateChecks

theorem x3OK_true : x3OK = true := KernelMisc.HS100.X3.x3OK_true

theorem certificate27261 : CFSG.EvenSporadicStandard.HSStd.FiveY.x3OK = true := x3OK_true

theorem card_centralizer_X3 :
    Nat.card ↥(CFSG.RankThree.Native.hs100R ⊓ Subgroup.centralizer
      ({CFSG.RankThree.Native.hs100A * CFSG.RankThree.Native.hs100U *
        (CFSG.RankThree.Native.hs100A * CFSG.RankThree.Native.hs100U)} :
        Set (Equiv.Perm (Fin 100)))) = 720 :=
  KernelMisc.HS100.X3Cls.card_centralizer_AU2

theorem card_centralizer_X3P :
    Nat.card ↥(CFSG.RankThree.Native.hs100P ⊓ Subgroup.centralizer
      ({CFSG.RankThree.Native.hs100A * CFSG.RankThree.Native.hs100U *
        (CFSG.RankThree.Native.hs100A * CFSG.RankThree.Native.hs100U)} :
        Set (Equiv.Perm (Fin 100)))) = 360 :=
  KernelMisc.HS100.X3Cls.card_centralizer_AU2P

end Certificates
