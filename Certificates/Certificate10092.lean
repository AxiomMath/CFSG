
module


public import CFSG.Certificates.Kernel.Th.SoundnessMax3
import Certificates.Kernel.Th.Max3

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
theorem certificate10092 :
    (eqRows (powRows Slp.rowsT8 3) idRows = true ∧
      eqRows (powRows Slp.rowsS8' 19) idRows = true ∧
      eqRows (mulRows rowsX rowsX) idRows = true ∧
      eqRows (powRows rowsY 6) idRows = true ∧
      eqRows rowsZ rowsA = true ∧
      eqRows rowsZ idRows = false ∧
      eqRows (mulRows rowsZ rowsZ) idRows = true ∧
      eqRows (mulRows rowsZ rowsX) (mulRows rowsX rowsZ) = true ∧
      eqRows (mulRows rowsZ rowsY) (mulRows rowsY rowsZ) = true ∧
      (∀ i : Fin 8, eqRows (mulRows (rowsQ i) (rowsQ i)) idRows = true) ∧
      (∀ i : Fin 8, eqRows (mulRows rowsZ (rowsQ i)) (mulRows (rowsQ i) rowsZ) = true) ∧
      (∀ i j : Fin 8, eqRows (mulRows (rowsQ i) (rowsQ j))
        (mulRows (mulRows (rowsQ j) (rowsQ i)) (powRows rowsZ (c i j).val)) = true) ∧
      (∀ i : Fin 8, eqRows (mulRows (mulRows rowsX (rowsQ i)) rowsX)
        (rowsNf (xz i).val fun j => (xv i j).val) = true) ∧
      (∀ i : Fin 8, eqRows (mulRows (mulRows rowsY (rowsQ i)) (powRows rowsY 5))
        (rowsNf (yz i).val fun j => (yv i j).val) = true))
    ∧ (∀ k l : Fin 512, l < k → eqRows (rowsNfAt k) (rowsNfAt l) = false) :=
  CFSG.KC.Th.Soundness.max3_sound10092 KernelTh.max3Data KernelTh.max3_hA KernelTh.max3_hB
    KernelTh.max3_ok

end Certificates
