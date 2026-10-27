module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.F3152.Forms

public section

namespace CFSG.KS.U52N

open CFSG.KC.Enum CFSG.KS.F3152

@[expose] noncomputable def evP (n w m idn : Nat) (G : Nat → Nat) (cs : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idn (fun c _ ih => pcomp n w m (G c) ih) cs

@[expose] noncomputable def keyOf (s : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.lor (Nat.shiftLeft 1 p) ih) s

@[expose] noncomputable def memN (x : Nat) (s : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => Nat.beq x p || ih) s

@[expose] noncomputable def imgL (w m P : Nat) (s : List Nat) : List Nat :=
  s.map (pg w m P)

@[expose] noncomputable def treeGo (w m : Nat) (LP : Nat → Nat) (ok : Nat → Bool)
    (nodes : List (List Nat)) : Nat → List (List Nat) → List Nat → List Nat → Bool
  | t, s :: ns, p :: ps, g :: gs =>
    (Nat.blt p t && ok g && Nat.beq (keyOf (imgL w m (LP g) (nodes.getD p []))) (keyOf s)) &&
      treeGo w m LP ok nodes (t + 1) ns ps gs
  | _, [], [], [] => true
  | _, _, _, _ => false

@[expose] noncomputable def treeOK (n w m : Nat) (LP : Nat → Nat) (ok : Nat → Bool) (F : List Nat)
    (nodes : List (List Nat)) (par gen : List Nat) : Bool :=
  match nodes, par, gen with
  | s :: ns, _ :: ps, _ :: gs =>
    (Nat.beq (keyOf s) (keyOf F) && F.all (fun p => Nat.blt p n)) &&
      (treeGo w m LP ok (s :: ns) 1 ns ps gs && sortedK (msortK ((s :: ns).map keyOf)))
  | _, _, _ => false

@[expose] noncomputable def gensOK (n w m idn : Nat) (LP : Nat → Nat) (ok : Nat → Bool) :
    List Nat → List (List Nat) → Bool
  | v :: vs, ws :: wss =>
    (Nat.beq v (evP n w m idn LP ws) && ws.all ok) && gensOK n w m idn LP ok vs wss
  | [], [] => true
  | _, _ => false

@[expose] noncomputable def elems (n w m idn : Nat) (SV : List Nat) (EW : List (List Nat)) :
    List Nat :=
  EW.map (evP n w m idn (fun c => SV.getD c 0))

@[expose] noncomputable def stabOK (n w m idn : Nat) (F SV : List Nat) (EW : List (List Nat)) :
    Bool :=
  EW.all (fun ew => ew.all (fun c => Nat.blt c SV.length)) &&
    ((elems n w m idn SV EW).all (fun e => F.all (fun p => memN (pg w m e p) F)) &&
      sortedK (msortK (elems n w m idn SV EW)))

@[expose] noncomputable def kOK (n w m idn : Nat) (KL KG F : List Nat) : Bool :=
  (memN idn KL && KL.all (fun e => KG.all (fun g => memN (pcomp n w m e g) KL))) &&
    (sortedK (msortK KL) &&
      allN n (fun p => Bool.rec (motive := fun _ => Bool)
        (!KG.all (fun g => Nat.beq (pg w m g p) p)) (KG.all (fun g => Nat.beq (pg w m g p) p))
        (memN p F)))

@[expose] noncomputable def cosetT (n w m : Nat) (KL ris : List Nat) (e : Nat) : Bool :=
  !memN (pcomp n w m e e) KL || ris.any (fun r => memN (pcomp n w m r e) KL)

end CFSG.KS.U52N

end
