module

public import Certificates.Kernel.Co1SevenK.Syl
public import CFSG.Certificates.Kernel.SporSch.Co1MatWSound
public import CFSG.Certificates.Kernel.SporSch.Co1BfsSound
public import CFSG.Certificates.Kernel.Co1Seven.CenSound
public import CFSG.Certificates.Kernel.Co1F2Sound
import Mathlib.Tactic.IntervalCases

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1SevenK

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.SporSch.M24 CFSG.KC.Co1B
  CFSG.Sporadic.Co1Schreier.Native CertificateChecks.KernelSporSch.Co1Packed Timmesfeld.Co1Seven

local notation "U" => unpack 24 24

theorem base_eq : [aR, bR] = (List.range 2).map fun i => U (D.M i) := by
  have h := kBase
  simp only [Bool.and_eq_true] at h
  rw [aR_u, bR_u, ← Nat.eq_of_beq_eq_true h.1, ← Nat.eq_of_beq_eq_true h.2]
  rfl

theorem dag_eq : gDag aR bR = ((List.range D.N).map fun i => U (D.M i),
    (List.range D.N).map fun i => U (D.MI i), true) := by
  unfold gDag
  exact dagWK_sound base_eq kDag

theorem rowAt_eq (k : Nat) : rowAt (gDag aR bR).1 k = if k < D.N then U (D.M k) else one := by
  rw [dag_eq]
  unfold rowAt
  split_ifs with hk
  · simp [List.getD_eq_getElem?_getD, hk]
  · simp [List.getD_eq_getElem?_getD, hk]

theorem validRows_U (X : Nat) : CFSG.Sporadic.Co1.InvNative.validRows (U X) = true := by
  rw [← unpackR_eq_unpack]
  exact CFSG.KC.Co1F2.validRows_unpackR X

theorem iS_lt : iS < D.N := by decide
theorem iT_lt : iT < D.N := by decide

theorem rowAt_iS : rowAt (gDag aR bR).1 iS = U SK := by
  rw [rowAt_eq, if_pos iS_lt]
  rfl

theorem rowAt_iT : rowAt (gDag aR bR).1 iT = U TK := by
  rw [rowAt_eq, if_pos iT_lt]
  rfl

theorem xGen_eq (k : Nat) : xGen (gDag aR bR).1 k = U (xGK k) := by
  unfold xGen xGK
  rw [rowAt_iS, rowAt_iT]
  by_cases h0 : k = 0
  · subst h0
    rfl
  · by_cases h1 : k = 1
    · subst h1
      rfl
    · rw [if_neg h0, if_neg h1, MatL.nIf_eq, MatL.nIf_eq]
      have e0 : (Nat.beq k 0 = true) = False := by simp [h0]
      have e1 : (Nat.beq k 1 = true) = False := by simp [h1]
      simp only [e0, e1, if_false]
      rw [← mul_unpackW, unpack_powWK]
      rfl

theorem rowAt_fus (k : Nat) : rowAt (gDag aR bR).1 (fusG.getD k 0) = U (cK k) := by
  rw [rowAt_eq]
  unfold cK
  rw [MatL.strictN_eq, MatL.nIf_eq]
  by_cases h : fusG.getD k 0 < D.N
  · rw [if_pos h, if_pos (by rw [Nat.blt_eq]; exact h)]
  · rw [if_neg h, if_neg (by rw [Nat.blt_eq]; exact h), MatL.unpack_idM]

theorem tgtRow_eq (k : Nat) : tgtRow (gDag aR bR).1 k = U (tK k) := by
  unfold tgtRow tK
  rw [MatL.nIf_eq]
  by_cases h : fusTgt.getD k 0 = 0
  · rw [if_pos h, if_pos (by rw [Nat.beq_eq]; exact h), rowAt_iS]
  · rw [if_neg h, if_neg (by rw [Nat.beq_eq]; exact h), rowAt_iT]

theorem gens_eq : (gensArr 2 GP) = [U SK, U TK].toArray := by
  apply Array.ext
  · simp [gensArr]
  · intro i h1 h2
    have hi : i < 2 := by simpa [gensArr] using h1
    simp only [gensArr, Array.getElem_ofFn]
    interval_cases i <;> rfl

theorem sylowOK_K : Timmesfeld.Co1Seven.sylowOK aR bR = true := by
  have hP := kP
  rw [MatL.bAnd_eq, Bool.and_eq_true] at hP
  obtain ⟨hN, hP⟩ := hP
  obtain ⟨hT, hok⟩ := gtBFS_of_K hP
  rw [gens_eq] at hT hok
  have hS := kS
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hS
  obtain ⟨⟨⟨⟨hs1, ht1⟩, hst⟩, hs7⟩, ht7⟩ := hS
  have hC := MatL.allN_iff.1 kC
  have hF := MatL.allN_iff.1 kF
  have hT' : treeOf [U SK, U TK] = bfsTree PT.N PT.P PT.PAR PT.LAB := hT
  have hsz : (bfsTree PT.N PT.P PT.PAR PT.LAB).pts.size = 49 := by
    simp [bfsTree, Nat.eq_of_beq_eq_true hN]
  rw [MatL.unpack_idM] at hs1 ht1
  unfold Timmesfeld.Co1Seven.sylowOK
  dsimp only
  rw [rowAt_iS, rowAt_iT, hT']
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨?_, validRows_U _⟩, validRows_U _⟩, hs1⟩, ht1⟩, ?_⟩, ?_⟩, ?_⟩, hok⟩, hsz⟩, ?_⟩, ?_⟩
  · rw [dag_eq]
  · rw [mul_unpackW, mul_unpackW, Nat.eq_of_beq_eq_true hst]
  · rw [← unpack_powWK, Nat.eq_of_beq_eq_true hs7, MatL.unpack_idM]
  · rw [← unpack_powWK, Nat.eq_of_beq_eq_true ht7, MatL.unpack_idM]
  · rw [Array.all_eq_true]
    intro i hi
    have hi' : i < PT.N := by simpa [bfsTree] using hi
    simp only [bfsTree, Array.getElem_ofFn]
    have hc := hC i hi'
    rw [MatL.strictB_eq] at hc
    by_cases hx : PT.P i = idM
    · rw [hx, MatL.unpack_idM]
      simp
    · have e : Nat.beq (PT.P i) idM = false :=
        Bool.eq_false_iff.2 fun h => hx (Nat.eq_of_beq_eq_true h)
      rw [e] at hc
      simp only [MatL.strictB_eq, MatL.bAnd_eq, Bool.and_eq_true, Nat.blt_eq] at hc
      obtain ⟨hc48, hceq⟩ := hc
      rw [Bool.or_eq_true, List.any_eq_true]
      right
      refine ⟨PC i / 6, List.mem_range.2 (by omega), ?_⟩
      rw [List.any_eq_true]
      refine ⟨PC i % 6, List.mem_range.2 (by omega), ?_⟩
      rw [beq_iff_eq, xGen_eq, ← unpack_powWK, Nat.eq_of_beq_eq_true hceq]
      rfl
  · rw [List.all_eq_true]
    intro k hk
    rw [rowAt_fus, xGen_eq, tgtRow_eq, Bool.and_eq_true, beq_iff_eq, mul_unpackW, mul_unpackW]
    have hf := hF k (List.mem_range.1 hk)
    rw [MatL.strictB_eq] at hf
    exact ⟨validRows_U _, congrArg U (Nat.eq_of_beq_eq_true hf)⟩

end CertificateChecks.KernelCo1SevenK

end
