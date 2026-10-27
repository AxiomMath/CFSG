module

public import Certificates.Kernel.Co2Smith.RootDefs

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native

@[expose] noncomputable def witEntryK (L : List Nat) (cz : Bool) (s x t : Nat) (w : List Nat) :
    Bool :=
  decide (x < 2300) && w.all (fun k => L.contains k) && (!cz || commK (wK LP w) zK) &&
    (List.range s).all (fun j => mapsK (wK LP w) glBase[j]! glBase[j]!) &&
    mapsK (mulV (wK LP w) (FM t)) glBase[s]! x

@[expose] noncomputable def witK : Bool :=
  (glWit0.all (fun e => witEntryK glC0Let false 0 e.1 e.2.1 e.2.2 &&
      mapsK (wK LP e.2.2) 80 80 && decide (e.2.1 < 3)) &&
    glWit1.all (fun e => witEntryK glC0Let false 1 e.1 0 e.2) &&
    glWit2.all (fun e => witEntryK glC0Let false 2 e.1 0 e.2)) &&
  (glWitZ0.all (fun e => witEntryK glC0Let true 0 e.1 0 e.2) &&
    glWitZ1.all (fun e => witEntryK glC0Let true 1 e.1 0 e.2) &&
    glWitZ2.all (fun e => witEntryK glC0Let true 2 e.1 0 e.2)) &&
  glWitPtsOK

theorem wit_k : witK = true := by decide +kernel

end CertificateChecks.KernelCo2Smith
