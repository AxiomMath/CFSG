module

public import Certificates.Data.Kernel.SporSch.MathieuOC

public section

namespace CFSG.KS.SporSch.J2OW

open CFSG.KC.Enum CFSG.KS CFSG.KS.M11 CFSG.KS.SporSch.MOC

@[expose] noncomputable def getK (d : Nat) (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => d)
    (fun a _ ih i => Nat.rec (motive := fun _ => Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def getW (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun a _ ih i => Nat.rec (motive := fun _ => List Nat) a (fun j _ => ih j) i) L

@[expose] noncomputable def tabK (n w m idn A B Ai Bi nT : Nat) (ws : List (List Nat))
    (ps : List Nat) : Bool :=
  allN nT fun i => Nat.beq (xyWordK n w m idn A B Ai Bi (getW ws i)) (getK 0 ps i)

@[expose] noncomputable def powsK (n w m idn nT : Nat) (ps : List Nat) (L : List (Nat × Nat × Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih =>
    bAnd(Prod.rec (motive := fun _ => Bool) (fun i kj => Prod.rec (motive := fun _ => Bool)
      (fun k j => bAnd(Nat.blt i nT, bAnd(Nat.blt j nT,
        Nat.beq (powK n w m idn (getK 0 ps i) k) (getK 0 ps j)))) kj) r, ih)) L

@[expose] noncomputable def conjsK (n w m nT : Nat) (ps : List Nat) (L : List (Nat × Nat × Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih =>
    bAnd(Prod.rec (motive := fun _ => Bool) (fun d xy => Prod.rec (motive := fun _ => Bool)
      (fun x y => bAnd(Nat.blt d nT, bAnd(Nat.blt x nT, bAnd(Nat.blt y nT,
        Nat.beq (pcomp n w m (getK 0 ps d) (getK 0 ps x))
          (pcomp n w m (getK 0 ps y) (getK 0 ps d)))))) xy) r, ih)) L

@[expose] noncomputable def commsK (n w m nT : Nat) (ps : List Nat) (L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih =>
    bAnd(Prod.rec (motive := fun _ => Bool) (fun x y => bAnd(Nat.blt x nT, bAnd(Nat.blt y nT,
      Nat.beq (pcomp n w m (getK 0 ps x) (getK 0 ps y))
        (pcomp n w m (getK 0 ps y) (getK 0 ps x))))) r, ih)) L

@[expose] noncomputable def ordsK (n w m idn nT : Nat) (ps : List Nat) (L : List (Nat × Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ ih =>
    bAnd(Prod.rec (motive := fun _ => Bool) (fun i o => bAnd(Nat.blt i nT, bAnd(Nat.blt 0 o,
      ordIs n w m idn (getK 0 ps i) (Nat.sub o 1)))) r, ih)) L

@[expose] noncomputable def memK (ps : List Nat) (v : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun j _ ih => bIf(Nat.beq v (getK 0 ps j), true, ih)) L

@[expose] noncomputable def closedK (n w m nT : Nat) (ps : List Nat) (M : List Nat) (L : List Nat) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun i tl ih =>
    bAnd(Nat.blt i nT, bAnd(bIf(memK ps (getK 0 ps i) tl, false, true),
      bAnd(List.rec (motive := fun _ => Bool) true (fun j _ ih2 =>
        bAnd(memK ps (pcomp n w m (getK 0 ps i) (getK 0 ps j)) M, ih2)) M, ih)))) L

end CFSG.KS.SporSch.J2OW

end
