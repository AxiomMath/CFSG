module

public import Certificates.Kernel.Co2Smith.Cox
public import Certificates.Kernel.Co2Smith.Root
public import Certificates.Kernel.Co2Smith.WitK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem glBase_lt (j : Nat) : glBase[j]! < 2300 := by
  by_cases h : j < 3
  · rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2) with rfl | rfl | rfl <;> decide
  · rw [getElem!_neg glBase j (by simpa [glBase] using h)]
    decide

theorem entry_eq (cz : Bool) (s x t : Nat) (w : List Nat) (ht : t < 3) :
    glWitEntryOK glC0Let cz glBase s x t w = witEntryK glC0Let cz s x t w := by
  unfold glWitEntryOK witEntryK
  by_cases hx : x < 2300
  · by_cases hw : (w.all fun k => glC0Let.contains k) = true
    · have hl : ∀ k ∈ w, k < 22 := by
        intro k hk
        have := List.all_eq_true.1 hw k hk
        simp only [glC0Let, List.contains_cons, List.contains_nil, Bool.or_false,
          Bool.or_eq_true, beq_iff_eq] at this
        omega
      simp only
      rw [glR_eq hl, glZ_eq, commRows_unpack, glForm_eq ht, mulRows_unpack,
        glMaps_unpack _ (glBase_lt s) hx]
      congr 1
      congr 1
      apply all_congr_mem
      intro j _
      rw [glMaps_unpack _ (glBase_lt j) (glBase_lt j)]
    · rw [Bool.not_eq_true] at hw
      simp only [hw, Bool.and_false, Bool.false_and]
  · simp only [decide_eq_false hx, Bool.false_and]

theorem wit_ok : glWitOK = true := by
  have e0 : (glWit0.all fun e => glWitEntryOK glC0Let false glBase 0 e.1 e.2.1 e.2.2 &&
      glMaps (glR e.2.2) 80 80 && decide (e.2.1 < 3)) =
      glWit0.all fun e => witEntryK glC0Let false 0 e.1 e.2.1 e.2.2 &&
        mapsK (wK LP e.2.2) 80 80 && decide (e.2.1 < 3) := by
    apply all_congr_mem
    intro e _
    by_cases ht : e.2.1 < 3
    · rw [entry_eq _ _ _ _ _ ht]
      by_cases hw : (e.2.2.all fun k => glC0Let.contains k) = true
      · have hl : ∀ k ∈ e.2.2, k < 22 := by
          intro k hk
          have := List.all_eq_true.1 hw k hk
          simp only [glC0Let, List.contains_cons, List.contains_nil, Bool.or_false,
            Bool.or_eq_true, beq_iff_eq] at this
          omega
        rw [glR_eq hl, glMaps_unpack _ (by decide) (by decide)]
      · rw [Bool.not_eq_true] at hw
        simp only [witEntryK, hw, Bool.and_false, Bool.false_and]
    · simp only [decide_eq_false ht, Bool.and_false]
  have e1 : ∀ (L : List (Nat × List Nat)) (cz : Bool) (s : Nat),
      (L.all fun e => glWitEntryOK glC0Let cz glBase s e.1 0 e.2) =
        L.all fun e => witEntryK glC0Let cz s e.1 0 e.2 :=
    fun L cz s => all_congr_mem fun e _ => entry_eq _ _ _ _ _ (by decide)
  rw [← wit_k]
  unfold glWitOK glWitC0OK glWitCzOK witK
  rw [e0, e1, e1, e1, e1, e1]

end CertificateChecks.KernelCo2Smith
