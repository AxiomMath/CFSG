module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PairCover
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1OuterGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Data
public import CFSG.Sporadic.Schreier.M24
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24CheckInputs
import Certificates.Kernel.LocalQT.Syl.C4059
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1AutModel
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords

set_option maxRecDepth 100000

public section

namespace Certificates

open CFSG.KD.LQT.C4059 CFSG.KC.LQT.Syl CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate4059 : (m24rl.length = 2 ^ 10 ∧ m24rl.Nodup ∧ (1 : ↥NativeSporadic.M24) ∈ m24rl ∧
            (∀ x ∈ m24rl, ∀ g ∈ m24rg, x * g ∈ m24rl) ∧ (∀ x ∈ m24rl, x ^ (2 ^ 10) = 1))
    ∧ ((pairG (invG m24rl)).length < (2 ^ (6 + 1) - 1) * (2 ^ (6 + 1) - 2))
    ∧ (g1ok m24rl m24conj m24G1 11 = true ∧ g1cover m24rl m24G1 = true)
    ∧ (g2ok m24rl m24conj m24G2_11 11 = true ∧ (g2coverBad m24key m24rl m24G2_11).length = 0)
    ∧ (g2ok m24rl m24conj m24G2_23 23 = true ∧
            (g2coverBad m24key m24rl m24G2_23).length < 930) := by
  refine ⟨sylG2_sound _ m24a m24b hA hB m24RGens m24RWords 10 kS, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ⟨?_, ?_⟩⟩
  · exact (pairLen_sound _ m24a m24b hA hB m24RGens m24RWords 12546 (by decide) kP).trans_lt
      (by decide)
  · exact g1okP_sound _ m24a m24b hA hB m24RGens m24RWords m24PoolWords m24G1 11 (by decide) k1
  · exact g1cov_sound _ m24a m24b hA hB m24RGens m24RWords m24G1 h1 (by decide) k1c
  · exact g2okP_sound _ m24a m24b hA hB m24RGens m24RWords m24PoolWords m24G2_11 11 (by decide)
      k11
  · exact Nat.le_zero.1 (bad_sound _ m24a m24b hA hB m24RGens m24RWords m24G2_11 _ 0
      (by decide) (by decide)
      k11c)
  · exact g2okP_sound _ m24a m24b hA hB m24RGens m24RWords m24PoolWords m24G2_23 23 (by decide)
      k23
  · exact lt_of_le_of_lt (bad_sound _ m24a m24b hA hB m24RGens m24RWords m24G2_23 _ 888
      (by decide) (by decide) k23c) (by decide)

end Certificates
