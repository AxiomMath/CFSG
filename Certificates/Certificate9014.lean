module

public import CFSG.Certificates.Kernel.Th.SoundnessMax3
import Certificates.Kernel.Th.Max3

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Th in
open Native Max3 in
theorem certificate9014 : 
      (∀ i : Fin 4, eqRows (mulRows (rowsEQ i) (rowsEQ i)) idRows = true) ∧
      (∀ i j : Fin 4, eqRows (mulRows (rowsEQ i) (rowsEQ j)) (mulRows (rowsEQ j) (rowsEQ i)) = true) ∧
      (∀ i : Fin 4, eqRows (mulRows (rowsFQ i) (rowsEQ i))
        (mulRows (mulRows (rowsEQ i) rowsZ) (rowsFQ i)) = true) ∧
      (∀ i j : Fin 4, i ≠ j →
        eqRows (mulRows (rowsFQ j) (rowsEQ i)) (mulRows (rowsEQ i) (rowsFQ j)) = true) :=
  CFSG.KC.Th.Soundness.max3_sound9014 KernelTh.max3Data KernelTh.max3_hA KernelTh.max3_hB
    KernelTh.max3_ok

end Certificates
