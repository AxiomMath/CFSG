module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1CenterInputs
public import Certificates.Kernel.Co1B.C2047
public import Certificates.Kernel.Co1B.KZ25171

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo1B.C25171

open CFSG.KS.SporSch.M24 CFSG.KS.Raw CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block
  CFSG.Sporadic.Co1Block.Native CFSG.Sporadic.Co1.InvNative CFSG.EvenSporadicStandard.Solomon78

theorem eqU (A B : Nat) : (unpack 24 24 A == unpack 24 24 B) = CFSG.KC.Co1B.eqK A B := by
  rw [← unpackR_eq_unpack, ← unpackR_eq_unpack]
  exact CFSG.KC.Co1B.beq_unpack A B

theorem commC_eq (P : Nat) : commutesWithAll
    ((List.range twoCBray.length).map fun i => unpack 24 24 (C2047.D2.M i)) (unpack 24 24 P) =
      commC P := by
  rw [Bool.eq_iff_iff, commutesWithAll, commC, List.all_eq_true, MatL.allN_iff]
  have hl : twoCBray.length = 8 := rfl
  rw [hl]
  constructor
  · intro h j hj
    have := h _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
    rwa [mul_unpackW, mul_unpackW, eqU] at this
  · rintro h g hg
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hg
    have := h j (List.mem_range.1 hj)
    rwa [mul_unpackW, mul_unpackW, eqU]

theorem iotaC_D1 : iotaCRows = unpack 24 24 (C2047.D1.M 2) := by
  have h := C2047.kb
  simp only [Bool.and_eq_true] at h
  rw [C2047.iotaC_u, Nat.eq_of_beq_eq_true h.2]

theorem center_ok : (bfsTree C2047.QT.N C2047.QT.P C2047.QT.PAR C2047.QT.LAB).pts.all (fun p =>
    !commutesWithAll ((List.range twoCBray.length).map fun i => unpack 24 24 (C2047.D2.M i)) p ||
      p == one || p == iotaCRows) = true := by
  rw [Array.all_eq_true]
  intro i hi
  have hi' : i < 2048 := by simpa [bfsTree, C2047.hN.2.1] using hi
  have h := MatL.allN_iff.1 kZ i hi'
  simp only [bfsTree, Array.getElem_ofFn]
  rw [commC_eq, iotaC_D1, ← MatL.unpack_idM, eqU, eqU]
  exact h

theorem bray_valid : ((List.range twoCBray.length).map fun i => unpack 24 24 (C2047.D2.M i)).all
    validRows = true := by
  rw [List.all_eq_true]
  intro g hg
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
  rw [← unpackR_eq_unpack]
  exact CFSG.KC.Co1F2.validRows_unpackR _

open Certificates in
theorem c25171 : CFSG.EvenSporadicStandard.Solomon78.centerCheckC = true := by
  unfold centerCheckC centerFilterOf
  rw [C2047.bray_eq, C2047.gt_eq, bray_valid, center_ok]
  rfl

end CertificateChecks.KernelCo1B.C25171

end
