module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu CFSG.KS.Raw

@[expose] noncomputable def derivK (k s : Nat) (D : List (List Int)) : Bool :=
  bAnd(Nat.beq (Nat.add (lenW D) k) s,
    allN s (fun j => bIf(Nat.blt j k, true, lettersK j (dword D k j))))

end CFSG.KS.SporSch

end
