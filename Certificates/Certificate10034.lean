module

public import CFSG.Monster.GMS.Griess13.ChecksOrbitTab
import Certificates.Kernel.Griess13.Orbit

public section

namespace Certificates

open CertificateChecks.KernelG13 in
open CFSG.Monster.GMS.Griess13.Co1Data in
open scoped Matrix in
theorem certificate10034 :
    (∀ v : Fin 6 → ZMod 3, codeOf v < 729)
    ∧ (∀ v : Fin 6 → ZMod 3, vecOfCode (codeOf v) = v)
    ∧ (∀ v : Fin 6 → ZMod 3, v ≠ 0 → 0 < codeOf v)
    ∧ (∀ c < 729, 0 < c → vecOfCode c ≠ 0)
    ∧ (∀ s : Fin 2, ∀ c < 729, vecOfCode (stepS s.val c) = actN s *ᵥ vecOfCode c)
    ∧ (orbCheckR = true)
    ∧ (∀ k : Fin 12, orbitClassR (repw k) = 1)
    ∧ (orbitClassR w1 = 1)
    ∧ (orbitClassR wB = 2)
    ∧ (orbitClassR wC = 3)
    ∧ (∀ w : Fin 6 → ZMod 3, orbitClassR (-w) = orbitClassR w)
    ∧ (∀ w : Fin 6 → ZMod 3, w ≠ 0 → orbitClassR w = 1 →
      ∃ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ w = c • repw k)
    ∧ (((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 1).card = 24)
    ∧ (((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 2).card = 264)
    ∧ (((Finset.univ.erase (0 : Fin 6 → ZMod 3)).filter fun w => orbitClassR w = 3).card = 440)
    ∧ ((Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 0).card = 24)
    ∧ ((Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 1).card = 264)
    ∧ ((Finset.univ.filter fun w : Fin 6 → ZMod 3 => w ≠ 0 ∧ orbitIndexR w = 2).card = 440)
    ∧ (∀ k : Fin 12, repw k ≠ 0) :=
  ⟨codeOf_lt, vecOfCode_codeOf, codeOf_pos, vecOfCode_ne_zero, vecOfCode_stepS, orbCheckR_true,
    orbitClassR_repw, orbitClassR_w1, orbitClassR_wB, orbitClassR_wC, orbitClassR_neg,
    orbitClassR_one_spec, card_orbitClassR_one, card_orbitClassR_two, card_orbitClassR_three,
    card_orbitIndexR_zero, card_orbitIndexR_one, card_orbitIndexR_two, repw_ne_zero⟩

end Certificates
