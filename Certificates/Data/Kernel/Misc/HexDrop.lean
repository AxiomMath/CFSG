module

public import Certificates.Data.Kernel.Misc.HexFlat

public section

namespace CFSG.KC.Misc.HexFlat

@[expose] noncomputable def dropL (m : Nat) (cs : List Char) : List Char :=
  List.rec (motive := fun _ => Nat → List Char) (fun _ => List.nil)
    (fun c t ih k => Nat.rec (motive := fun _ => List Char) (List.cons c t) (fun k' _ => ih k') k)
    cs m

end CFSG.KC.Misc.HexFlat

end
