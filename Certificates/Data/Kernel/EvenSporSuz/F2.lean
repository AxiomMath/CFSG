module

public import Certificates.Data.Kernel.EvenSporSuz.SylowTree

public section

namespace CFSG.KC.EvenSporSuz.F2

open CFSG.KC.ONanSmall CFSG.KC.M24G CFSG.KC.Misc.G24 CFSG.KC.EvenSporSuz.Syl

@[expose] def allBelow (n : Nat) (p : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun j ih => p j && ih) n

@[expose] noncomputable def invK (M I : List Nat) (n : Nat) : Bool :=
  Nat.beq M.length n && Nat.beq I.length n &&
    allBelow n fun k => canonK (M.getD k 0) && canonK (I.getD k 0) &&
      Nat.beq (mulF3 (M.getD k 0) (I.getD k 0)) one3

@[expose] noncomputable def comK (MU IU MV IV : List Nat) (WU WV : List (List Nat)) (N : List Nat)
    (n : Nat) : Bool :=
  Nat.beq N.length n &&
    allBelow n fun j => canonK (N.getD j 0) &&
      letN (evalL MU IU (WU.getD j [])) fun U => letN (evalL MV IV (WV.getD j [])) fun V =>
        Nat.beq (mulF3 (mulF3 (N.getD j 0) V) U) (mulF3 U V)

@[expose] noncomputable def memK (M I : List Nat) (W : List (List Nat)) (f : Nat → Nat) (n : Nat) :
    Bool :=
  allBelow n fun t => Nat.beq (evalL M I (W.getD t [])) (f t)

@[expose] def hasK (x : Nat) (E : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => Nat.beq p.1 x || ih) E

@[expose] noncomputable def entK (T : KTree (Nat × Nat)) (G GI : List Nat) (n e cd : Nat) : Bool :=
  canonK e && allBelow n (fun k => (findK (mulF3 e (G.getD k 0)) T).isSome) &&
    bif Nat.beq (cd / 8) 0 then Nat.beq e one3 else
      Nat.blt (cd % 8) n && Option.rec (motive := fun _ => Bool) false
        (fun c => Nat.beq (c / 8 + 1) (cd / 8)) (findK (mulF3 e (GI.getD (cd % 8) 0)) T)

@[expose] noncomputable def entsK (T : KTree (Nat × Nat)) (G GI : List Nat) (n : Nat)
    (E : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun p _ ih => entK T G GI n p.1 p.2 && ih) E

@[expose] noncomputable def enumK (T : KTree (Nat × Nat)) (G GI : List Nat) (n m : Nat)
    (E : List (Nat × Nat)) : Bool :=
  Nat.beq E.length m && incK E && hasK one3 E && entsK T G GI n E

@[expose] noncomputable def cenB (G : List Nat) (n e : Nat) : Bool :=
  allBelow n fun k => Nat.beq (mulF3 e (G.getD k 0)) (mulF3 (G.getD k 0) e)

@[expose] noncomputable def cenK (G : List Nat) (n : Nat) (E : List (Nat × Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun a => Nat.beq a 0)
    (fun p _ ih a => Bool.rec (ih a)
      (Nat.beq (mulF3 p.1 p.1) one3 && Nat.blt 0 a && letN (Nat.sub a 1) ih) (cenB G n p.1)) E

end CFSG.KC.EvenSporSuz.F2
