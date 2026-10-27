module

public import CFSG.YGroups.Exact.Y432Inputs
import Certificates.Kernel.YModel.Y432
public import Certificates.Kernel.YModel.Y432F
public import Certificates.Kernel.YModel.S432C

public section

namespace Certificates

open CertificateChecks.KernelYModel CFSG.KC.YModel CFSG.YGroups

theorem y432CArrays_eq : y432CArrays = linesA (fun _ => 31671) 32 CFSG.KD.YMS432C.LF 9 := by
  have h := linesA_select (n := 31671) (w := 32) (lines := 10) (F := CFSG.KD.YM432P.F)
    [0, 1, 2, 3, 4, 5, 6, 7, 8] (by decide)
  rw [y432CArrays, y432F_arrays_eq]
  rw [linesA_congrF (lines := 9) (F := CFSG.KD.YMS432C.LF)
    (F' := fun c => CFSG.KD.YM432P.F ([0, 1, 2, 3, 4, 5, 6, 7, 8].getD c 0))
    (fun L hL => by interval_cases L <;> rfl)]
  exact h

open CFSG.YGroups CFSG.Monster.B.Co2.Native in
theorem certificate10102 :
    (y432FArrays.size = 10 ∧ ModelNative.permsOK 31671 y432FArrays = true ∧
      ModelNative.relatorsOK 31671 y432FArrays (yRels 4 3 2) = true ∧
      ModelNative.chainOK 31671 y432FArrays y432FWords y432FBase = true ∧
      ModelNative.chainSizes 31671 y432FArrays y432FWords y432FBase =
      [31671, 28160, 3159, 288, 35, 12, 3, 2, 2])
    ∧ (y432CArrays.size = 9 ∧ Nat.card (arrClosure 31671 y432CArrays) = 47377612800)
    ∧ (eqA 31671 (ModelNative.evalW 31671 y432FArrays F432Word) (idA 31671) = true ∧
      eqA 31673 (ModelNative.evalW 31673 y432Arrays F432Word)
      (ModelNative.evalW 31673 y432Arrays F432AltWord) = true ∧
      eqA 31673 (ModelNative.evalW 31673 y432Arrays F432Word) (idA 31673) = false) := by
  refine ⟨⟨y432F_size, y432F_perms, y432F_relators, y432F_chain0.1, y432F_chain0.2⟩,
    ⟨rfl, ?_⟩, ⟨y432F_w_fid, y432_w_falt, y432_w_fne⟩⟩
  rw [y432CArrays_eq]
  exact s432C_card

end Certificates
