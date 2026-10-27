module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1PermCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12Data
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M12CheckInputs
import Certificates.Kernel.LocalQT.Syl.C4069
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace Certificates

open CFSG.KD.LQT.C4069 CFSG.KC.LQT.Syl CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate4069 : (m12rl.length = 2 ^ 6 ∧ m12rl.Nodup ∧ (1 : ↥NativeSporadic.M12) ∈ m12rl ∧
            (∀ x ∈ m12rl, ∀ y ∈ m12rl, x * y ∈ m12rl) ∧ (∀ x ∈ m12rl, x ^ (2 ^ 6) = 1))
    ∧ (forallIndep (invG m12rl) (fun _ => false) 4 [] = true)
    ∧ (g1ok m12rl m12conj m12G1 11 = true ∧ g1cover m12rl m12G1 = true)
    ∧ ((m12Sigma * (evalCodes [m12A1, m12B1] m12OuterWord * m12Sigma *
              (evalCodes [m12A1, m12B1] m12OuterWord)⁻¹)) ^ 11 = 1 ∧
            m12Sigma * (evalCodes [m12A1, m12B1] m12OuterWord * m12Sigma *
              (evalCodes [m12A1, m12B1] m12OuterWord)⁻¹) ≠ 1) :=
  ⟨syl_sound _ m12a m12b hA hB m12RGens m12RWords 6 kS,
    rank_sound _ m12a m12b hA hB m12RGens m12RWords 4 (by decide) kR,
    ⟨g1ok_sound _ m12a m12b hA hB m12RGens m12RWords m12G1 11 (by decide) k1,
      g1cov_sound _ m12a m12b hA hB m12RGens m12RWords m12G1 h1 (by decide) k1c⟩, kO⟩

end Certificates
