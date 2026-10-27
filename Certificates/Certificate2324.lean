
module

public import Certificates.Certificate2324Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase
public import CFSG.Certificates.Kernel.Th.SoundnessTsBase

public import CFSG.Sporadic.ThSchreier.TwoCentralizerInputs
public meta import CFSG.Sporadic.ThSchreier.OrbitCheck819Base
public meta import CFSG.Sporadic.Th.Max3.PacketBase1
public import CFSG.Certificates.Kernel.Th.SoundnessTs
import Certificates.Kernel.Th.Ts

public section

namespace Certificates

open CertificateChecks.KernelTh

open CFSG CFSG.Sporadic CFSG.Sporadic.ThSchreier CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Sporadic.Th.Max3

open CertificateChecks.KernelTh

theorem certificate2324 : eqRows (mulRows (hRows centWord0) rowsT) (mulRows rowsT (hRows centWord0)) = true ∧
    eqRows (mulRows (hRows centWord1) rowsT) (mulRows rowsT (hRows centWord1)) = true ∧
    (∀ R ∈ twoRowsList, eqRows (mulRows R (invRows R)) idRows = true ∧
      (invRows R).size = 248 ∧ ∀ r ∈ invRows R, r.wf = true) ∧
    twoRowsList.length = 10 ∧
    eqRows (signedRows (tupleRows twoRowsList) origWord0) rowsLX = true ∧
    eqRows (signedRows (tupleRows twoRowsList) origWord1) rowsLY = true ∧
    eqRows rowsTwoR rowsE217 = true ∧ eqRows rowsTwoR idRows = false ∧
    eqRows rowsTwoR rowsZ = false :=
  CFSG.KC.Th.Soundness.ts_sound2324 tsData ts_hA ts_hB ts_ok

end Certificates
