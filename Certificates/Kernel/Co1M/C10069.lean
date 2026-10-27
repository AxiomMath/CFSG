
module

public import CFSG.Sporadic.Co1.Module.OrbitsBase
public import CFSG.Sporadic.Co1.Module.FormsInputs
public import Certificates.Kernel.Co1Cover.Bridge
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 100000

namespace CertificateChecks.KernelCo1M

open CFSG.KC.Co1F2 CFSG.KC.M1F2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.SmallF2 CertificateChecks.KernelCo1Cover

theorem f69_main :
    (mulRows 24 (mulRows 24 (transposeRows 24 (unpackR 24 R0)) f0Rows) (unpackR 24 R0) = f0Rows ∧
      mulRows 24 (mulRows 24 (transposeRows 24 (unpackR 24 R1)) f0Rows) (unpackR 24 R1) = f0Rows ∧
      mulRows 24 f0Rows f0InvRows = idRows 24 ∧ mulRows 24 f0InvRows f0Rows = idRows 24 ∧
      (∀ i < 24, ((mulRows 24 (mulRows 24 (transposeRows 24 (unpackR 24 R0)) qRows)
        (unpackR 24 R0))[i]?.getD 0).testBit i = ((qRows[i]?.getD 0).testBit i)) ∧
      (∀ i < 24, ((mulRows 24 (mulRows 24 (transposeRows 24 (unpackR 24 R1)) qRows)
        (unpackR 24 R1))[i]?.getD 0).testBit i = ((qRows[i]?.getD 0).testBit i))) := by
  exact of_decide_eq_true (by quickRfl)

theorem wordRows_eq (w : List Bool) : wordRows w =
    w.foldl (fun acc b => mulRows 24 acc (if b then unpackR 24 R0 else unpackR 24 R1)) (idRows 24) := by
  unfold wordRows letterRows
  rw [rowsA_eq, rowsB_eq]

theorem f69_words :
    (vecMulN 24 (transposeRows 24 (wordRows stabWord₁)) 2 = 2 ∧
      vecMulN 24 (transposeRows 24 (wordRows stabWord₂)) 2 = 2 ∧
      addRows (mulRows 24 certC1 (addRows (wordRows stabWord₁) (idRows 24)))
        (mulRows 24 certC2 (addRows (wordRows stabWord₂) (idRows 24))) = projRows ∧
      addRows (mulRows 24 (addRows (wordRows stabWord₁) (idRows 24)) certD1)
        (mulRows 24 (addRows (wordRows stabWord₂) (idRows 24)) certD2) = lamRows) := by
  rw [wordRows_eq, wordRows_eq]
  exact of_decide_eq_true (by quickRfl)

theorem f69_rest : (vecMulN 24 (unpackR 24 R0) 10379264 < 2 ^ 24 ∧
      vecMulN 24 (unpackR 24 R0) 10379264 ≠ 10379264) ∧
    (qRows[1]?.getD 0).testBit 1 = false ∧ (qRows[12]?.getD 0).testBit 12 = true ∧
      (qRows[0]?.getD 0).testBit 0 = false ∧
      f0Rows = #[8388608, 10379264, 4321280, 1679360, 4710400, 81920, 11182080, 13221888, 16683008,
        9777152, 8183808, 11567104, 975620, 3397214, 11318454, 15105500, 6169276, 16363858,
        14276370, 3626442, 3092234, 14347584, 2590100, 2542531] := by
  exact of_decide_eq_true (by quickRfl)

open Certificates in
open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module CFSG.Sporadic.SmallF2 in
theorem c10069 :
    mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsA) f0Rows) dat.rowsA = f0Rows ∧
      mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsB) f0Rows) dat.rowsB = f0Rows ∧
      mulRows 24 f0Rows f0InvRows = idRows 24 ∧ mulRows 24 f0InvRows f0Rows = idRows 24 ∧
      (∀ i < 24, ((mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsA) qRows)
        dat.rowsA)[i]?.getD 0).testBit i = ((qRows[i]?.getD 0).testBit i)) ∧
      (∀ i < 24, ((mulRows 24 (mulRows 24 (transposeRows 24 dat.rowsB) qRows)
        dat.rowsB)[i]?.getD 0).testBit i = ((qRows[i]?.getD 0).testBit i)) ∧
      vecMulN 24 (transposeRows 24 (wordRows stabWord₁)) 2 = 2 ∧
      vecMulN 24 (transposeRows 24 (wordRows stabWord₂)) 2 = 2 ∧
      addRows (mulRows 24 certC1 (addRows (wordRows stabWord₁) (idRows 24)))
        (mulRows 24 certC2 (addRows (wordRows stabWord₂) (idRows 24))) = projRows ∧
      addRows (mulRows 24 (addRows (wordRows stabWord₁) (idRows 24)) certD1)
        (mulRows 24 (addRows (wordRows stabWord₂) (idRows 24)) certD2) = lamRows ∧
      toVecD 24 (vecMulN 24 dat.rowsA 10379264) ≠ toVecD 24 10379264 ∧
      (qRows[1]?.getD 0).testBit 1 = false ∧ (qRows[12]?.getD 0).testBit 12 = true ∧
      (qRows[0]?.getD 0).testBit 0 = false ∧
      f0Rows = #[8388608, 10379264, 4321280, 1679360, 4710400, 81920, 11182080, 13221888, 16683008,
        9777152, 8183808, 11567104, 975620, 3397214, 11318454, 15105500, 6169276, 16363858,
        14276370, 3626442, 3092234, 14347584, 2590100, 2542531] := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := f69_main
  obtain ⟨h7, h8, h9, h10⟩ := f69_words
  obtain ⟨⟨hlt, hne⟩, h12, h13, h14, h15⟩ := f69_rest
  refine ⟨?_, ?_, h3, h4, ?_, ?_, h7, h8, h9, h10, ?_, h12, h13, h14, h15⟩
  · rw [rowsA_eq]
    exact h1
  · rw [rowsB_eq]
    exact h2
  · rw [rowsA_eq]
    exact h5
  · rw [rowsB_eq]
    exact h6
  · rw [rowsA_eq]
    intro h
    exact hne (toVecD_injective hlt (by norm_num) h)

end CertificateChecks.KernelCo1M

end
