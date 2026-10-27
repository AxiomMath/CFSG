module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1MathieuGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22CheckInputs
import Certificates.Kernel.LocalQT.Syl.C4057

public section

namespace Certificates

open CFSG.KD.LQT.C4057 CFSG.KC.LQT.Syl CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Mathieu in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate4057 : (m22rl.length = 2 ^ 7 ∧ m22rl.Nodup ∧ (1 : ↥NativeSporadic.M22) ∈ m22rl ∧
            (∀ x ∈ m22rl, ∀ y ∈ m22rl, x * y ∈ m22rl) ∧ (∀ x ∈ m22rl, x ^ (2 ^ 7) = 1))
    ∧ (forallIndep (invG m22rl) (fun _ => false) 5 [] = true)
    ∧ (g1ok m22rl m22conj m22G1 11 = true ∧ g1cover m22rl m22G1 = true)
    ∧ (g2ok m22rl m22conj m22G2 11 = true ∧ g2cover m22rl m22G2 = true) :=
  ⟨syl_sound _ m22a m22b hA hB m22RGens m22RWords 7 kS,
    rank_sound _ m22a m22b hA hB m22RGens m22RWords 5 (by decide) kR,
    ⟨g1ok_sound _ m22a m22b hA hB m22RGens m22RWords m22G1 11 (by decide) k1,
      g1cov_sound _ m22a m22b hA hB m22RGens m22RWords m22G1 h1 (by decide) k1c⟩,
    ⟨g2ok_sound _ m22a m22b hA hB m22RGens m22RWords m22G2 11 (by decide) k2,
      g2cov_sound _ m22a m22b hA hB m22RGens m22RWords m22G2 h2 (by decide) k2c⟩⟩

end Certificates
