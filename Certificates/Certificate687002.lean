module

public import CFSG.Sporadic.Th.Recog.JLettersInputs
import Certificates.Kernel.Th.JLet.Glue

public section

namespace Certificates

open CertificateChecks.KernelTh.JLet

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 in
open CFSG.GH74.QTGen4.Recog.G23 in
open CFSG.Sporadic.Th.Recog in
theorem certificate687002 :
    eqRows (rowsHsw 0) CFSG.Sporadic.Th.Max3.rowsA = true ∧
      CFSG.Sporadic.Th.rowsMatrix (rowsHsw 1) ≠ CFSG.Sporadic.Th.rowsMatrix CFSG.Sporadic.Th.Max3.rowsA ∧
      (∀ i : Fin 8, i ≠ 1 → eqRows (mulRows (rowsHsw 0) (rowsHsw i))
        (mulRows (rowsHsw i) (rowsHsw 0)) = true) ∧
      checkLJ () = true ∧
      (∀ i : Fin 6, eqRows (mulRows (rowsL i) (rowsHsw 6))
        (mulRows (rowsHsw 6) (rowsL i)) = true) ∧
      CFSG.Sporadic.Th.rowsMatrix (rowsL 0) ≠ CFSG.Sporadic.Th.rowsMatrix CFSG.Sporadic.Th.Native.idRows ∧
      checkWJ2 () = true ∧
      checkWJ3 () = true ∧
      checkWJ4 () = true ∧
      checkWJ5 () = true ∧
      checkWJ6 () = true ∧
      checkWJ7 () = true := ⟨conj0, conj1, conj2, conj3, conj4, conj5, conj6, conj7, conj8, conj9, conj10, conj11⟩

end Certificates
