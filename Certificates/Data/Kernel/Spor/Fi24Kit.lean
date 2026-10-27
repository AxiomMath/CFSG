module

public import Certificates.Data.Kernel.Spor.Fi24NetPt
public import Certificates.Data.Kernel.Spor.Fi24Orb

public section

namespace CFSG.KC.Fi24Kit

open CFSG.KC CFSG.KC.Loop CFSG.KC.LceS CFSG.KC.MonsterConv.Perm CFSG.KC.Fi24Net CFSG.KC.Fi24NetPt
open CFSG.KC.Fi24Orb (oA oB oPar oLab)

@[expose] noncomputable def walkP (NW : Nat → Nat → Nat) (w : List Nat) (v : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun x => x)
    (fun l _ ih x => strictN (planeL NW l x) ih) w v

@[expose] noncomputable def wP (NW : Nat → Nat → Nat) (w : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun l _ ih => strictN ih (letN NW l)) w

@[expose] noncomputable def tpOK (NW : Nat → Nat → Nat) (NT : Nat → Nat) (wA wB : List Nat) (k : Nat) :
    Bool :=
  letB (tpl k) (fun v => letB (netF NT v) (fun u =>
    andB (Nat.beq (netF (NW (nat_lit 0)) u) (netF NT (walkP NW wA v)))
      (Nat.beq (netF (NW (nat_lit 1)) u) (netF NT (walkP NW wB v)))))

@[expose] noncomputable def gT (OL : Nat → Nat) (l q : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 1), oA (OL q), oB (OL q))

@[expose] noncomputable def gI (OL : Nat → Nat) (l q : Nat) : Nat :=
  nIf(Nat.beq l (nat_lit 1), oA (OL q), strictN (oB (OL q)) (fun y => oB (OL y)))

@[expose] noncomputable def upF (OL : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ q => q)
    (fun _ ih k q => nIf(Nat.beq k (nat_lit 0), q,
      strictN (OL k) (fun e => strictN (gI OL (oLab e) q) (ih (oPar e))))) f

@[expose] noncomputable def dnF (OL : Nat → Nat) (f : Nat) : Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ q => q)
    (fun _ ih k q => nIf(Nat.beq k (nat_lit 0), q,
      strictN (OL k) (fun e => strictN (ih (oPar e) q) (gT OL (oLab e))))) f

@[expose] noncomputable def upI (OL : Nat → Nat) (k q : Nat) : Nat := upF OL (Nat.succ k) k q

@[expose] noncomputable def dnT (OL : Nat → Nat) (k q : Nat) : Nat := dnF OL (Nat.succ k) k q

@[expose] noncomputable def clsK (OL : Nat → Nat) (NT : Nat → Nat) (k p : Nat) : Nat :=
  strictN (upI OL k p) (fun y => strictN (ptF NT y) (dnT OL k))

@[expose] noncomputable def stepS (NW : Nat → Nat → Nat) (ls : List Nat) (S : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) S (fun l _ ih => Nat.lor (planeL NW l S) ih) ls

@[expose] noncomputable def iterS (NW : Nat → Nat → Nat) (ls : List Nat) (d S : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S (fun _ ih => strictN ih (stepS NW ls)) d

@[expose] noncomputable def coverOK (NW : Nat → Nat → Nat) (ls : List Nat) (d S F : Nat) : Bool :=
  Nat.beq (Nat.land (Nat.lor (iterS NW ls d S) F) ptsM) ptsM

end CFSG.KC.Fi24Kit

end
