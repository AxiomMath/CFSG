module

public import Certificates.Kernel.B45.C260394H
public import Certificates.Kernel.SporSch.Ru.RowsGen
import Certificates.Kernel.Sporadic.ON.Gen

public section

set_option Elab.async false

#kon_slices CertificateChecks.KernelB45.C260394.rootS 18 20

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.InvTabK CFSG.KC.B45P.RuSyl

@[expose] noncomputable def ext20 : List Nat := greedyExtF 495 (cK CM) (pK PR) [20]

@[expose] noncomputable def root20P (j : Nat) : Bool :=
  Nat.ble ext20.length j ||
    forallGreedyF 495 (cK CM) (pK PR) (predC CM PR WQ (WN 0)) 3 [ext20.getD j 0, 20]

end CertificateChecks.KernelB45.C260394

end

#kss_each CertificateChecks.KernelB45.C260394.R20 CertificateChecks.KernelB45.C260394.root20P 474

public section

namespace CertificateChecks.KernelB45.C260394

open CFSG.KC.InvTabK CFSG.KC.B45P.RuSyl

theorem ext20_length : ext20.length ≤ 474 := by
  unfold ext20 greedyExtF
  dsimp only
  exact Nat.le_trans (List.length_filter_le _ _) (by simp [startF])

theorem rootS20 : rootS (nat_lit 20) = true := by
  show ext20.all (fun x => forallGreedyF 495 (cK CM) (pK PR) (predC CM PR WQ (WN 0)) 3 [x, 20]) =
    true
  rw [List.all_eq_true]
  intro x hx
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx
  have hp := R20.all j (by have := ext20_length; show j < 474; omega)
  unfold root20P at hp
  have hn : Nat.ble ext20.length j = false := by
    cases h : Nat.ble ext20.length j
    · rfl
    · exact absurd (Nat.le_of_ble_eq_true h) (by omega)
  rw [hn, Bool.false_or, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    Option.getD_some] at hp
  exact hp

end CertificateChecks.KernelB45.C260394

#kon_slices CertificateChecks.KernelB45.C260394.rootS 21 28

end
