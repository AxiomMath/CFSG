module

public import Certificates.Data.Kernel.J4TreeCode
public import Certificates.Data.Kernel.J4M4Sets

public section

namespace CFSG.KC.J4M4

open CFSG.KC.F2W CFSG.KC.J4Tree CFSG.J4Tree.Native

@[expose] def fieldsL (a : Nat) : List Nat := (List.range 12).map fun i => a / 2 ^ (12 * i) % 2 ^ 12

@[expose] def eqC (a b : Nat) : Bool := eqL (fieldsL a) (fieldsL b)

@[expose] noncomputable def kelK (e : Nat) : Nat :=
  (pcSeqT e).foldl (fun acc i => mulW 12 acc ((tblC kCode).getD i oneK)) oneK

@[expose] noncomputable def ccK (ce : Nat × Nat) : Nat :=
  mulW 12 (etaCK (tblC uCode) ce.1) (kelK ce.2)

@[expose] noncomputable def actR (G : List Nat) (s k : Nat) : Nat := mulW 12 k (G.getD s 0)

@[expose] noncomputable def actC (G Gi : List Nat) (s k : Nat) : Nat :=
  mulW 12 (mulW 12 (G.getD s 0) k) (Gi.getD s 0)

@[expose] noncomputable def maskK (w : List (Nat × Nat)) (m : Nat) : Nat :=
  (List.range w.length).foldl
    (fun acc l => if m.testBit l then mulW 12 acc (ccK (w.getD l (0, 0))) else acc) oneK

end CFSG.KC.J4M4
