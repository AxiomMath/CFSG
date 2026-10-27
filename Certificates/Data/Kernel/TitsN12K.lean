module

public import Certificates.Data.Kernel.SporSch.TitsCnt
public import Certificates.Data.Kernel.TitsOctK

public section

namespace CFSG.KC.TitsN12K

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch

@[expose] noncomputable def in2 (a b x : Nat) : Bool := bIf(Nat.beq x a, true, Nat.beq x b)

@[expose] noncomputable def sqB (BP : Nat) (g : Nat → Nat) : Bool :=
  allN 5 (fun t => strictB (pg 11 (mask 11) BP t) (fun b => Nat.beq (g (g b)) b))

@[expose] noncomputable def noFar (LAY : Nat) (g : Nat → Nat) : Bool :=
  allN 1755 (fun p => bIf(Nat.beq (CFSG.KC.TitsOctK.layAt LAY p) 8,
    bIf(Nat.beq (g p) p, false, true), true))

@[expose] noncomputable def restK (BP a b : Nat) (g : Nat → Nat) : Bool :=
  bAnd(in2 1 2 (g a), bAnd(in2 1 2 (g b), bAnd(in2 a b (g 2), bAnd(Nat.beq (g 0) 0,
    sqB BP g))))

@[expose] noncomputable def swT (BP : Nat) (g : Nat → Nat) : Bool :=
  strictB (g 1) (fun y => bIf(in2 3 4 y, restK BP 3 4 g, bIf(in2 5 7 y, restK BP 5 7 g,
    bIf(in2 9 13 y, restK BP 9 13 g, bIf(in2 17 25 y, restK BP 17 25 g, false)))))

@[expose] noncomputable def n2T (BP : Nat) (g : Nat → Nat) : Bool :=
  strictB (g 0) (fun y => bAnd(in2 1 2 y, bAnd(Nat.beq (g y) 0, sqB BP g)))

@[expose] noncomputable def farOK (LAY M c x : Nat) : Bool :=
  bIf(noFar LAY (pg 11 (mask 11) x), bIf(hasBit M c, false, true), hasBit M c)

@[expose] noncomputable def cntAt (LR TR : Nat → Nat) (i a b : Nat) (C : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c _ ih => Bool.rec (motive := fun _ => Nat) ih (Nat.succ ih) (in2 a b (gptC LR TR c i)))
    C

@[expose] noncomputable def memL (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq x y, true, ih)) L

@[expose] noncomputable def lookC (c : Nat) (C : List Nat) : List Nat → Nat :=
  List.rec (motive := fun _ => List Nat → Nat) (fun _ => nat_lit 0)
    (fun d _ ih L => List.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun l L' _ => Bool.rec (motive := fun _ => Nat) (ih L') l (Nat.beq c d)) L) C

@[expose] noncomputable def conjOK (U : Nat → Nat) (C L : List Nat) (c p j : Nat) : Bool :=
  Nat.beq (pcomp 1755 11 (mask 11) (U j) (lookC p C L)) (pcomp 1755 11 (mask 11) (lookC c C L) (U j))

@[expose] noncomputable def walkK (ok : Nat → Nat → Nat → Bool) (E : List (Nat × Nat × Nat)) :
    List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun R => R)
    (fun e _ ih R => Bool.rec (motive := fun _ => List Nat) List.nil (ih (List.cons e.1 R))
      (bAnd(memL e.2.1 R, ok e.1 e.2.1 e.2.2)))
    E

end CFSG.KC.TitsN12K

end
