module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1CenterInputs
public import Certificates.Kernel.Co1B.C24513
public import Certificates.Kernel.Co1B.KZ25172A
public import Certificates.Kernel.Co1B.KZ25172B
public import CFSG.Certificates.Kernel.Co1BSound

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.Syl2B

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Block.Native CFSG.Sporadic.Co1.TwoBNative CFSG.Sporadic.Co1.InvNative
  CFSG.EvenSporadicStandard.TwoCo1.HypOne CFSG.EvenSporadicStandard.Solomon78

theorem eqU (A B : Nat) : (unpack 24 24 A == unpack 24 24 B) = CFSG.KC.Co1B.eqK A B := by
  rw [← unpackR_eq_unpack, ← unpackR_eq_unpack]
  exact CFSG.KC.Co1B.beq_unpack A B

theorem commB_eq (P : Nat) : commutesWithAll
    ((List.range twoBBray.length).map fun i => unpack 24 24 (S2.M i)) (unpack 24 24 P) =
      commB P := by
  rw [Bool.eq_iff_iff, commutesWithAll, commB, List.all_eq_true, MatL.allN_iff]
  have hl : twoBBray.length = 10 := rfl
  rw [hl]
  constructor
  · intro h j hj
    have := h _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
    rwa [mul_unpackW, mul_unpackW, eqU] at this
  · rintro h g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    have := h j (List.mem_range.1 hj)
    rwa [mul_unpackW, mul_unpackW, eqU]

theorem zOK_all {i : Nat} (hi : i < 32768) : zOK (ST.P i) = true := by
  obtain ⟨c, r, hr, rfl⟩ : ∃ c r, r < 4096 ∧ i = 4096 * c + r :=
    ⟨i / 4096, i % 4096, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 4096).symm⟩
  have hc : c < 8 := by omega
  interval_cases c
  · exact MatL.allN_iff.1 kZ0 r hr
  · exact MatL.allN_iff.1 kZ1 r hr
  · exact MatL.allN_iff.1 kZ2 r hr
  · exact MatL.allN_iff.1 kZ3 r hr
  · exact MatL.allN_iff.1 kZ4 r hr
  · exact MatL.allN_iff.1 kZ5 r hr
  · exact MatL.allN_iff.1 kZ6 r hr
  · exact MatL.allN_iff.1 kZ7 r hr

theorem center_ok : (bfsTree ST.N ST.P ST.PAR ST.LAB).pts.all (fun p =>
    !commutesWithAll ((List.range twoBBray.length).map fun i => unpack 24 24 (S2.M i)) p ||
      p == one || p == aR) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 32768 := by simpa [bfsTree, hN.1] using hi
  have h := zOK_all hi'
  simp only [bfsTree, Array.getElem_ofFn]
  rw [commB_eq, aR_D1, ← MatL.unpack_idM, eqU, eqU]
  exact h

theorem bray_valid : ((List.range twoBBray.length).map fun i => unpack 24 24 (S2.M i)).all
    validRows = true := by
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  rw [← unpackR_eq_unpack]
  exact CFSG.KC.Co1F2.validRows_unpackR _

open Certificates in
theorem c25172 : CFSG.EvenSporadicStandard.Solomon78.centerCheckB = true := by
  unfold centerCheckB centerSylowOf centerFilterOf
  simp only []
  rw [dagS_eq, bray_eq, sg_eq, gt_eq.1, bray_valid, center_ok]
  rfl

end CertificateChecks.KernelCo1B.Syl2B

end
