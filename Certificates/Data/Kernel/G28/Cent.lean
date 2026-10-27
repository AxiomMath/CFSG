module

public import Certificates.Data.Kernel.G28.Defs

public section

namespace CFSG.KC.G28

@[expose] noncomputable def ent (x t : Nat) : Nat := fld x (Nat.mul 3 t) 3

@[expose] noncomputable def vecE (v : List Nat) (t : Nat) : Nat :=
  cond (Nat.beq (Nat.mod t 6) 0) (v.getD (Nat.div t 6) 0) 0

@[expose] noncomputable def jE (t : Nat) : Nat :=
  cond (Nat.beq (Nat.mod t 6) (Nat.mod (Nat.add (Nat.div t 6) 3) 6)) 1 0

@[expose] noncomputable def entsOK (x : Nat) (f : Nat → Nat) : Bool :=
  Nat.blt x (Nat.pow 2 108) && (List.range 36).all fun t => Nat.beq (ent x t) (f t)

@[expose] noncomputable def centP (u z : Nat) (v0 : List Nat) (vP jP b bi : Nat)
    (gs cp q qt : List Nat) : Bool :=
  entsOK vP (vecE v0) && entsOK jP jE &&
  (List.range 6).all (fun k =>
    Nat.beq (gs.getD k 0) (mulP (powP u (Nat.div k 3)) (powP z (Nat.mod k 3)))) &&
  (List.range 6).all (fun k => letB (mulP (gs.getD k 0) vP) fun c =>
    (List.range 6).all fun r => Nat.beq (ent b (Nat.add (Nat.mul 6 r) k)) (ent c (Nat.mul 6 r))) &&
  Nat.beq (mulP b bi) idP &&
  (List.range 6).all (fun i => entsOK (cp.getD i 0) fun t =>
    ent (gs.getD (Nat.mod t 6) 0) (Nat.add (Nat.mul 6 (Nat.div t 6)) i)) &&
  (List.range 6).all (fun i => Nat.beq (mulP (cp.getD i 0) bi) (q.getD i 0)) &&
  (List.range 6).all (fun i => entsOK (qt.getD i 0) fun t =>
    ent (q.getD i 0) (Nat.add (Nat.mul 6 (Nat.mod t 6)) (Nat.div t 6))) &&
  (List.range 6).all (fun i => (List.range 6).all fun k =>
    Nat.beq (mulP (q.getD i 0) (q.getD k 0)) (mulP (q.getD k 0) (q.getD i 0))) &&
  (List.range 6).all (fun i =>
    Nat.beq (mulP (mulP jP (qt.getD i 0)) jP) (powP (q.getD i 0) 8)) &&
  Nat.beq (mulP jP jP) idP

end CFSG.KC.G28

end
