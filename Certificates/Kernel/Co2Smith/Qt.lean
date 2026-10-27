module

public import Certificates.Kernel.Co2Smith.W
public import Certificates.Kernel.Co2Smith.Pts
public import Certificates.Kernel.Co2Smith.QtK
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co1F2 CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith
open CFSG.Sporadic.Co2Smith.Native CFSG.Sporadic.SmallF2.Native

theorem qtGens_get {k : Nat} (hk : k < 7) : glQtGens[k]! = unpackR 22 (qtGenK k) := by
  unfold glQtGens qtGenK
  rw [getElem!_pos _ k (by simp [hk]), Array.getElem_ofFn]
  by_cases h6 : k < 6
  · simp only [if_pos h6]
    rw [gens_get h6]
    rfl
  · simp only [if_neg h6]
    exact mkR_get (by decide)

theorem qt_ok : glQtOK = true := by
  have hK := qt_k
  have hF := qtFix_k
  unfold qtK at hK
  simp only [Bool.and_eq_true, List.all_eq_true] at hK hF
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hK
  have hD : glQtD0 = unpackR 22 (wK LP [11, 12]) := glR_eq (by decide)
  unfold glQtOK
  simp only [Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨?_, fun k hk => ?_⟩, ?_⟩, fun e he => ?_⟩, ?_⟩
  · rw [hD, glZ_eq, commRows_unpack]
    exact h1
  · rw [hD, mkR_get (List.mem_range.1 hk), commRows_unpack]
    exact h2 k hk
  · rw [glZ_eq, mkR_get (by decide), mkR_get (by decide), mulRows_unpack, mulRows_unpack,
      beq_unpack]
    exact h3
  · obtain ⟨ha, hb⟩ := h4 e he
    have ha' : ∀ k ∈ e.2, k < 7 := by simpa using ha
    have hl : e.1 < 22 := by
      have : (glQtLetters.all fun e => decide (e.1 < 22)) = true := by decide
      exact of_decide_eq_true (List.all_eq_true.1 this e he)
    refine ⟨ha, ?_⟩
    rw [wRows_unpack _ qtGenK _ (fun k hk => qtGens_get (ha' k hk)),
      glR_eq (by simpa using hl), beq_unpack]
    exact hb
  · rw [glGa_eq, glZ_eq, mulRows_unpack]
    change glMkFixIs (unpackR 22 (mulV gaK zK)) 52 = true
    rw [fixIs_of hF.1]
    exact hF.2

end CertificateChecks.KernelCo2Smith
