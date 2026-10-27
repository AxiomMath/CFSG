module

public import Certificates.Data.Kernel.SporSch.MathieuOC
public import Certificates.Data.Kernel.Spor.MEnum
public import Certificates.Data.Kernel.Spor.Prim
public import CFSG.Certificates.Kernel.Spor.BindList
public import CFSG.Certificates.Kernel.Spor.RawSound

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.MEnum

@[expose] noncomputable def memL (x : Nat) (E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) E

@[expose] noncomputable def allL (f : Nat → Bool) (E : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun y _ ih => bAnd(f y, ih)) E

@[expose] noncomputable def bindLs (n w : Nat) (E : List (List Nat)) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun EP => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) EP)
    (fun l _ ih EP => List.rec (motive := fun _ => Bool) false
      (fun P EP' _ => bAnd(bindListK n w P l, ih EP')) EP) E

@[expose] noncomputable def nlE (n w m nw idn : Nat) (LR TRI : Nat → Nat) (BP nb : Nat)
    (PS PSI : Nat → Nat) (ng : Nat) (A E : List Nat) : Bool :=
  allL (fun e => bAnd(canonK n w m nw e, bAnd(siftK n w m nw idn LR TRI BP nb 0 e,
    strictB (pinvS n w m e) (fun ei => bAnd(permOK n w m nw e ei, bAnd(memL ei E,
    strictB (pcomp n w m e e) (fun e2 => bAnd(Nat.beq (pcomp n w m e2 e2) idn,
    bAnd(allL (fun f => memL (pcomp n w m e f) E) E,
      allN ng (fun j => memL (conjK n w m (PS j) (PSI j) e) E)))))))))) A

@[expose] noncomputable def nlK (n w m nw idn : Nat) (LR TR : Nat → Nat) (nb : Nat) (E : List Nat)
    (lo len : Nat) : Bool :=
  allBlk lo (fun j => strictB (elemK n w m nw idn LR TR nb j) (fun q =>
    bIf(allL (fun e => Nat.beq (pcomp n w m q e) (pcomp n w m e q)) E, memL q E, true))) len

end CFSG.KS.SporSch.MOC

end
