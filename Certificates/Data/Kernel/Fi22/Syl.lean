module

public import Certificates.Data.Kernel.Fi22.Letters

public section

namespace CFSG.KS.Fi22S

open CFSG.KC.Enum CFSG.KS.Fi22L

@[expose] def slText : String := include_str "syl.hex"

@[expose] noncomputable def slPacked : Nat := by hex_nat slText 231660 16986497497197206396

@[expose] noncomputable def sT (l : Nat) : Nat :=
  Nat.land (Nat.shiftRight slPacked (Nat.mul (nat_lit 42120) l)) tM

@[expose] noncomputable def LSK (l x : Nat) : Nat := lk (sT l) x

@[expose] noncomputable def wJ (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun z _ ih => strictN ih (LJk ljPacked slpPacked z)) w

@[expose] noncomputable def swChk (j : Nat) (w : List Nat) : Bool :=
  allN (nat_lit 3510) fun x => Nat.beq (LSK (Nat.mul (nat_lit 2) j) x) (wJ w x)

end CFSG.KS.Fi22S

end
