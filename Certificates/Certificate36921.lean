module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InBInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InBFacts
public import Mathlib.LinearAlgebra.Matrix.Rank
import Certificates.Kernel.BabyMonster.Fi23Img23

public section

namespace Certificates

open CertificateChecks

open CFSG.Blueprint CFSG.Sporadic.GLQ CFSG.Sporadic.Bridge.Fi23GPL.Native
  CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.Fi23InB in
theorem certificate36921 : ∀ x y : NativeSporadic.B,
    ((x : NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2) :
        Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed1 →
    ((y : NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2) :
        Matrix (Fin 4370) (Fin 4370) (ZMod 2)) =
      NativeSporadic.decode 2 4370 1 NativeSporadic.BSeed2 →
    Matrix.rank ((((signedWord (runProg (initRegs x y) slp 1) (runProg (initRegs x y) slp 2)
          (CFSG.Sporadic.Bridge.Fi23GPL.Native.imgWords ())[2]! *
        signedWord (runProg (initRegs x y) slp 1) (runProg (initRegs x y) slp 2)
          (CFSG.Sporadic.Bridge.Fi23GPL.Native.imgWords ())[3]! : NativeSporadic.B) :
        NativeSporadic.seedMonoid 2 4370 1 NativeSporadic.BSeed1 NativeSporadic.BSeed2) :
        Matrix (Fin 4370) (Fin 4370) (ZMod 2)) - 1) = 2862 :=
  KernelBM.Fi23Img23.rank_r0_of_seeds

end Certificates
