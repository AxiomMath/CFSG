
module


public import CFSG.Certificates.Kernel.Th.SoundnessMax3
import Certificates.Kernel.Th.Max3

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Th.Max3 CFSG.Sporadic.Th.Max3.InvRep in
theorem certificate10089 :
    (∀ k : Fin 512, eqRows (mulRows (rowsNfAt k) (rowsNfAt k)) idRows = false ∨
        eqRows (rowsNfAt k) idRows = true ∨ eqRows (rowsNfAt k) rowsZ = true ∨
        eqRows (mulRows (rowsConj k) (rowsQ 0)) (mulRows (rowsNfAt k) (rowsConj k)) = true) ∧
      (∀ k : Fin 512, eqRows (mulRows (rowsXNf k) (rowsXNf k)) idRows = false ∨
        eqRows (mulRows (rowsNfAt (uIdx k)) rowsX) (mulRows (rowsXNf k) (rowsNfAt (uIdx k))) =
          true) ∧
      (∀ k : Fin 512, eqRows (mulRows (rowsDNf k) (rowsDNf k)) idRows = false) :=
  CFSG.KC.Th.Soundness.max3_sound10089 KernelTh.max3Data KernelTh.max3_hA KernelTh.max3_hB
    KernelTh.max3_ok

end Certificates
