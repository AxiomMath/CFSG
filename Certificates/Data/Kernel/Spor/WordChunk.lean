module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KS.Raw

open CFSG.KC.Enum CFSG.KS CFSG.KS.Mathieu

@[expose] noncomputable def wordAccK (n w m acc : Nat) (S SI : Nat → Nat) (wd : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) acc
    (fun z _ ih => strictN ih (fun T => strictN (icode z) (fun c =>
      pcomp n w m (nIf(Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 0),
        S (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)),
        SI (Nat.sub (Nat.shiftRight c (nat_lit 1)) (nat_lit 1)))) T))) wd

@[expose] noncomputable def chunkK (n w m idn : Nat) (S SI : Nat → Nat) (wd : List Int) (L : Nat)
    (V : Nat → Nat) (i : Nat) : Bool :=
  Nat.beq (wordAccK n w m (nIf(Nat.blt (Nat.add i L) wd.length, V (Nat.add i L), idn)) S SI
    (List.take L (List.drop i wd))) (V i)

end CFSG.KS.Raw

end
