module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M23CheckInputs
import Certificates.Kernel.LocalQT.Syl.C4037

public section

namespace Certificates

open CFSG.KD.LQT.C4037 CFSG.KC.LQT.Syl CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.Schreier in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.Schreier CFSG.Blueprint in
theorem certificate4037 : (m23rl.length = 2 ^ 7 ∧ m23rl.Nodup ∧ (1 : ↥NativeSporadic.M23) ∈ m23rl ∧
            (∀ x ∈ m23rl, ∀ y ∈ m23rl, x * y ∈ m23rl) ∧ (∀ x ∈ m23rl, x ^ (2 ^ 7) = 1))
    ∧ (forallIndep m23rinv (fun _ => false) 5 [] = true)
    ∧ (m23G1ok = true ∧ m23G1cover = true)
    ∧ (m23G2ok = true ∧ m23G2cover = true) := by
  refine ⟨syl_sound _ m23GenA m23GenB hA hB m23RGens m23RWords 7 kS, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · change forallIndep (invG m23rl) (fun _ => false) 5 [] = true
    exact rank_sound _ m23GenA m23GenB hA hB m23RGens m23RWords 5 (by decide) kR
  · change g1ok m23rl m23conj m23G1 11 = true
    exact g1ok_sound _ m23GenA m23GenB hA hB m23RGens m23RWords m23G1 11 (by decide) k1
  · exact g1covL_sound _ m23GenA m23GenB hA hB m23RGens m23RWords m23G1 h1 (by decide) k1c
  · change g2ok m23rl m23conj m23G2 11 = true
    exact g2ok_sound _ m23GenA m23GenB hA hB m23RGens m23RWords m23G2 11 (by decide) k2
  · exact g2covL_sound _ m23GenA m23GenB hA hB m23RGens m23RWords m23G2 h2 (by decide) k2c

end Certificates
