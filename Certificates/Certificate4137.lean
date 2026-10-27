module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24TCheckInputs
import Certificates.Kernel.LocalQT.Syl.C4137
import CFSG.Certificates.Kernel.LocalQTSylLSound
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1TightGen

set_option maxRecDepth 100000

public section

namespace Certificates

open CFSG.KD.LQT.C4137 CFSG.KC.LQT.Syl CFSG.KC.LQT.W CFSG.QuasithinUnique.Setup.X1
  CFSG.Sporadic.Mathieu CFSG.Blueprint in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate4137 : (m24E1l.length = 64 ∧ m24E1l.Nodup ∧ (1 : S24) ∈ m24E1l ∧
            (∀ x ∈ m24E1l, ∀ y ∈ m24E1l, x * y ∈ m24E1l) ∧ (∀ x ∈ m24E1l, x * x = 1) ∧
            (∀ x ∈ m24E1l, ∀ y ∈ m24E1l, x * y = y * x) ∧ (∀ b ∈ m24E1B, b ∈ m24E1l))
    ∧ (m24E2l.length = 64 ∧ m24E2l.Nodup ∧ (1 : S24) ∈ m24E2l ∧
            (∀ x ∈ m24E2l, ∀ y ∈ m24E2l, x * y ∈ m24E2l) ∧ (∀ x ∈ m24E2l, x * x = 1) ∧
            (∀ x ∈ m24E2l, ∀ y ∈ m24E2l, x * y = y * x) ∧ (∀ b ∈ m24E2B, b ∈ m24E2l))
    ∧ (heavyList m24rl (m24E1l ++ m24E2l) 62 = [])
    ∧ (AdjData m24E1B (m24Cj m24E1G2) m24E1A2 ∧ AdjData m24E1B (m24Cj m24E1G3) m24E1A3)
    ∧ (AdjData m24E2B (m24Cj m24E2G2) m24E2A2 ∧ AdjData m24E2B (m24Cj m24E2G3) m24E2A3)
    ∧ ((slpEval (normH NativeSporadic.M24)
            (m24Gens18 m24E1B (m24Cj m24E1G2) (m24Cj m24E1G3)) m24E1Slp).getD m24E1Tg.1 1 = m24a ∧
          (slpEval (normH NativeSporadic.M24)
            (m24Gens18 m24E1B (m24Cj m24E1G2) (m24Cj m24E1G3)) m24E1Slp).getD m24E1Tg.2 1 = m24b)
    ∧ ((slpEval (normH NativeSporadic.M24)
            (m24Gens18 m24E2B (m24Cj m24E2G2) (m24Cj m24E2G3)) m24E2Slp).getD m24E2Tg.1 1 = m24a ∧
          (slpEval (normH NativeSporadic.M24)
            (m24Gens18 m24E2B (m24Cj m24E2G2) (m24Cj m24E2G3)) m24E2Slp).getD m24E2Tg.2 1 = m24b) := by
  have hB1 : m24E1B.map (fun x : S24 => codeP (x : Equiv.Perm (Fin 24))) =
      rlGK 24 GC m24RGens m24E1Bw :=
    codes_eval NativeSporadic.M24 (by decide) [m24a, m24b] hG m24RGens m24E1Bw
  have hB2 : m24E2B.map (fun x : S24 => codeP (x : Equiv.Perm (Fin 24))) =
      rlGK 24 GC m24RGens m24E2Bw :=
    codes_eval NativeSporadic.M24 (by decide) [m24a, m24b] hG m24RGens m24E2Bw
  have hL : m24rl.map (fun x : S24 => codeP (x : Equiv.Perm (Fin 24))) =
      rlGK 24 GC m24RGens m24RWords :=
    codes_eval NativeSporadic.M24 (by decide) [m24a, m24b] hG m24RGens m24RWords
  have hE : (m24E1l ++ m24E2l).map (fun x : S24 => codeP (x : Equiv.Perm (Fin 24))) =
      lstK 24 6 (rlGK 24 GC m24RGens m24E1Bw) ++ lstK 24 6 (rlGK 24 GC m24RGens m24E2Bw) := by
    rw [List.map_append, m24E1l, m24E2l, lst_codes _ hB1, lst_codes _ hB2]
  have h1 := eab_sound m24E1B hB1 k1
  have h2 := eab_sound m24E2B hB2 k2
  have h3 := List.length_eq_zero_iff.1 (heavy_sound NativeSporadic.M24 m24rl (m24E1l ++ m24E2l) 62
    0 (by decide) hL hE kH)
  exact ⟨h1, h2, h3, pA.1, pA.2, pS1, pS2⟩

end Certificates
