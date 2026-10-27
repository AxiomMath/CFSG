module

public import Certificates.Data.Kernel.FiveStdKW2

public section

namespace CFSG.KC.FiveStdK

@[expose] noncomputable def nxW (g g2 d di B Mb : Nat) (XX P : List Nat) (e : Nat × Nat) : Bool :=
  andB (validK e.2) <| andB (Nat.beq (cjK e.2 (invK e.2) g) e.1) <|
    allN Mb fun j => letB (mulK e.2 (cjK d di (f20 B j))) fun c =>
      orB (!memL XX (cjK c (invK c) g2)) (memL P c)

@[expose] noncomputable def nxK (g g2 d di B Mb R Mo : Nat) (XX P : List Nat) (W : List (Nat × Nat)) :
    Bool :=
  andB (W.all (nxW g g2 d di B Mb XX P)) <|
    allN Mo fun j => letB (oCode (f96 R j)) fun y => orB (!memL XX y) (W.any fun e => Nat.beq e.1 y)

@[expose] noncomputable def nxSup (XX P : List Nat) (g g2 : Nat) : Bool :=
  allL P fun m => andB (validK m) <|
    andB (memL XX (cjK m (invK m) g)) (memL XX (cjK m (invK m) g2))

end CFSG.KC.FiveStdK

end
