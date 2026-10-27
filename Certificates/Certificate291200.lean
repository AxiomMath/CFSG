module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InBInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InBFacts
import Certificates.Kernel.BabyMonster.Fi23InB

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint CFSG.Sporadic.GLQ
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB in
theorem certificate291200 : NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1 *
        NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1 = 1 ∧
      NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2 *
          NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2 *
        NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2 = 1 ∧
      ∀ x y : NativeSporadic.B,
        ((x : NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2) :
            Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
          NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1 →
        ((y : NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2) :
            Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
          NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2 →
        Fi23ImgFacts (runProg (initRegs x y) slp 1) (runProg (initRegs x y) slp 2) :=
  KernelBM.Fi23InB.fi23Facts_of_seeds

end Certificates
