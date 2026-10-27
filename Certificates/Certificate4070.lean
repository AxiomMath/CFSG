module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22TCheckInputs
import Certificates.Kernel.LocalQT.Syl.C4070
import Certificates.Kernel.LocalQT.Syl.C4070D
import CFSG.Certificates.Kernel.LocalQTSylESound
import CFSG.Certificates.Kernel.LocalQTFgSound

set_option maxRecDepth 100000

public section

namespace Certificates

open CFSG.KD.LQT.C4070 CFSG.KC.LQT.Syl CFSG.QuasithinUnique.Setup.X1 in
open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint in
theorem certificate4070 : (a2rl.length = 2 ^ 8 ∧ a2rl.Nodup ∧ (1 : ↥m22A) ∈ a2rl ∧
            (∀ x ∈ a2rl, ∀ g ∈ a2rg, x * g ∈ a2rl) ∧ (∀ x ∈ a2rl, x ^ (2 ^ 8) = 1))
    ∧ ((∀ i : Fin 5, bE i * bE i = 1) ∧ (∀ i j : Fin 5, bE i * bE j = bE j * bE i) ∧
            (∀ i : Fin 5, cE * bE i * cE⁻¹ = bE (i + 1)) ∧
            (∀ i : Fin 5, dE * bE i * dE⁻¹ = bE (2 * i)) ∧
            cE ^ 5 = 1 ∧ cE ≠ 1 ∧ dE ^ 4 = 1 ∧ dE * cE * dE⁻¹ = cE ^ 2 ∧
            cE * tE * cE⁻¹ = tE ∧ dE * tE * dE⁻¹ = tE)
    ∧ (a2e5.length = 32 ∧ a2e5.Nodup ∧ (1 : ↥m22A) ∈ a2e5 ∧
            (∀ x ∈ a2e5, ∀ y ∈ a2e5, x * y ∈ a2e5) ∧ (∀ x ∈ a2e5, x ∈ a2rl) ∧
            (∀ i : Fin 5, bE i ∈ a2e5))
    ∧ (∀ x ∈ a2e5, x * x = 1)
    ∧ (a2heavy.length < 16)
    ∧ ((tE * (yT * tE * yT⁻¹)) ^ 11 = 1 ∧ tE * (yT * tE * yT⁻¹) ≠ 1 ∧
            (bE 0 * (y0 * bE 0 * y0⁻¹)) ^ 11 = 1 ∧ bE 0 * (y0 * bE 0 * y0⁻¹) ≠ 1)
    ∧ (((x2M : NativeSporadic.M22) : Equiv.Perm (Fin 22)) = ((bE 0 * bE 1 : ↥m22A) : Equiv.Perm (Fin 22)) ∧
            ((x4M : NativeSporadic.M22) : Equiv.Perm (Fin 22)) =
              ((bE 0 * bE 1 * bE 2 * bE 3 : ↥m22A) : Equiv.Perm (Fin 22)) ∧
            bE 0 * bE 1 ≠ 1 ∧ bE 0 * bE 1 * bE 2 * bE 3 ≠ 1)
    ∧ (fgOK m22FG = true ∧
            (m22G2.all fun e => m22FG.any fun f => f.1 == e.1 && f.2.1 == e.2.1) = true) := by
  have hL := codes_eval m22A (by decide) a2gens hG a2RGens a2RWords
  have hR := codes_gens m22A (by decide) a2gens hG a2RGens
  obtain ⟨e1, e2, e3, e4, e5⟩ := sub_sound m22A a2rl a2e5 5 hL hE kE
  exact ⟨listSylG_sound m22A a2rl a2rg 8 hL hR kS, p2, ⟨e1, e2, e3, e4, e5, pB⟩, p4,
    (heavy_sound m22A a2rl a2e5 30 4 (by decide) hL hE kH).trans_lt (by decide), p6, p7,
    fg_sound hA hB m22FG kF, p8⟩

end Certificates
