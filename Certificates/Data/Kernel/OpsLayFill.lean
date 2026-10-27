module

public import Certificates.Data.Kernel.OpsLayMcert

public section

namespace CFSG.KC.OpsLayK

open CFSG.KC.LQT CFSG.SectionRank.Native CFSG.RankThree.Asc83Table.Native

@[expose] def memB (r : Nat) : List Nat → Bool
  | [] => false
  | i :: I => Nat.beq r i || memB r I

@[expose] def lookV (c : Lay) (r : Nat) : List Nat → List Nat → Nat
  | i :: I, v :: V => bif Nat.beq r i then v else lookV c r I V
  | _, _ => c.ONE

@[expose] def fillR (c : Lay) (n : Nat) (I V : List Nat) : List Nat :=
  (List.range n).map fun r => lookV c r I V

@[expose] def wordIn (K : List Nat) (w : Word) : Bool := w.all fun q => memB q.1 K

@[expose] def factIn (K : List Nat) : MFact → Bool
  | .ord r _ => memB r K
  | .conj h u w => memB h K && wordIn K u && wordIn K w
  | .ne u w _ => wordIn K u && wordIn K w
  | .eq u w => wordIn K u && wordIn K w

@[expose] noncomputable def evalOnto (c : Lay) (R : List Nat) (w : Word) (X : Nat) : Nat :=
  w.foldr (fun q acc => CFSG.KC.Loop.strictN acc fun Y => c.mul (powK c (getR c R q.1) q.2) Y) X

@[expose] noncomputable def wsegL (c : Lay) (R : List Nat) (w : Word) (k i Wi Wi' : Nat) : Bool :=
  Nat.beq (evalOnto c R ((w.drop (i * k)).take k) Wi') Wi

end CFSG.KC.OpsLayK

end
