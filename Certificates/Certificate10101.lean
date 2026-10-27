module

public import Certificates.Kernel.YModel.Y233F
public import Certificates.Kernel.YModel.S233F
public import Certificates.Kernel.YModel.S233C

public section

namespace Certificates

open CertificateChecks.KernelYModel CFSG.KC.YModel CFSG.YGroups

theorem y233CArrays_eq : y233CArrays = linesA (fun _ => 3510) 32 CFSG.KD.YMS233C.LF 8 := by
  have h := linesA_select (n := 3510) (w := 32) (lines := 9) (F := CFSG.KD.YM233F.F)
    [0, 1, 3, 4, 5, 6, 7, 8] (by decide)
  rw [y233CArrays, y233F_arrays_eq]
  rw [linesA_congrF (lines := 8) (F := CFSG.KD.YMS233C.LF)
    (F' := fun c => CFSG.KD.YM233F.F ([0, 1, 3, 4, 5, 6, 7, 8].getD c 0))
    (fun L hL => by interval_cases L <;> rfl)]
  exact h

open CFSG.YGroups in
theorem certificate10101 :
    (y233FArrays.size = 9 ∧ ModelNative.permsOK 3510 y233FArrays = true ∧
      ModelNative.relatorsOK 3510 y233FArrays (yRels 2 3 3) = true ∧
      Nat.card (arrClosure 3510 y233FArrays) = 64561751654400)
    ∧ (y233CArrays.size = 8 ∧ Nat.card (arrClosure 3510 y233CArrays) = 92897280) := by
  refine ⟨⟨y233F_size, y233F_perms, y233F_relators, ?_⟩, ⟨rfl, ?_⟩⟩
  · rw [y233F_arrays_eq, linesA_congrF (F' := CFSG.KD.YMS233F.LF)
      (fun L hL => by interval_cases L <;> rfl)]
    exact s233F_card
  · rw [y233CArrays_eq]
    exact s233C_card

end Certificates
