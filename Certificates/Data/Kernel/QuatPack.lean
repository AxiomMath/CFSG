module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KC.QuatK

open CFSG.KC.Enum CFSG.KS

variable (n w : Nat)

@[expose] noncomputable def mulK (p q : Nat) : Nat := pcomp n w (mask w) p q

@[expose] noncomputable def memK (L : List Nat) (x : Nat) : Bool := L.any (Nat.beq x)

@[expose] noncomputable def q8K (e r i j : Nat) : List Nat :=
  [e, r, i, mulK n w i r, j, mulK n w j r, mulK n w i j, mulK n w (mulK n w i j) r]

@[expose] noncomputable def sameSetK (A B : List Nat) : Bool := A.all (memK B) && B.all (memK A)

@[expose] noncomputable def violatesK (T : List Nat) (i j : Nat) (c : Nat × Nat) : Bool :=
  T.any (fun x => !memK T (mulK n w (mulK n w c.1 x) c.2)) &&
    [i, j].any fun x => [mulK n w (mulK n w c.1 i) c.2, mulK n w (mulK n w c.1 j) c.2].any fun y =>
      !Nat.beq (mulK n w x y) (mulK n w y x)

@[expose] noncomputable def badWitK (u : Nat) (c : Nat × Nat) : Bool :=
  (fun x => !Nat.beq (mulK n w x u) (mulK n w u x) && !Nat.beq (mulK n w u (mulK n w x u)) x)
    (mulK n w (mulK n w c.1 u) c.2)

@[expose] noncomputable def identSqCheckK (e r : Nat) (S : List Nat) (W : List (Nat × Nat))
    (Ls : List (List Nat)) : Bool :=
  S.all fun u => W.any (badWitK n w u) || S.all fun v =>
    !Nat.beq (mulK n w u (mulK n w v u)) v ||
      (Ls.any (sameSetK (q8K n w e r u v)) || W.any (violatesK n w (q8K n w e r u v) u v))

@[expose] noncomputable def listOKK (l : List Nat) (p : Nat) : Bool :=
  Nat.beq l.length n && l.zipIdx.all fun x => Nat.beq (pg w (mask w) p x.2) x.1

@[expose] noncomputable def sqScanK (T : Nat → Nat) (N r : Nat) (idx : List Nat) : Bool :=
  idx.all (fun i => Nat.blt i N) && (List.range N).all fun i =>
    (fun b => cond (idx.contains i) b (!b)) (Nat.beq (mulK n w (T i) (T i)) r)

@[expose] noncomputable def cfgK (e u v u' v' : Nat) (tw : List (Nat × Nat)) (y : Nat) : Bool :=
  Nat.beq (mulK n w y u) (mulK n w u y) && Nat.beq (mulK n w y v) (mulK n w v y) &&
    Nat.beq (mulK n w y y) e && tw.any fun p =>
      Nat.beq (mulK n w y u') (mulK n w p.1 y) && Nat.beq (mulK n w y v') (mulK n w p.2 y)

@[expose] noncomputable def cfgScanK (e u v u' v' : Nat) (tw : List (Nat × Nat)) (T : Nat → Nat)
    (N s : Nat) (idx : List Nat) : Bool :=
  (List.range N).all fun i =>
    (fun b => cond (idx.contains i) b (!b)) (cfgK n w e u v u' v' tw (mulK n w (T i) s))

end CFSG.KC.QuatK

end
