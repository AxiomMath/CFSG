module

public import Certificates.Data.Kernel.Spor.F3Lane

public section

namespace CFSG.KS.F3L

open CFSG.F3.Native CFSG.KC.Enum

@[expose] noncomputable def trBit (d : Nat) (x q : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.shiftLeft (nat_lit 1) q)
    (Nat.testBit x (Nat.add (Nat.mul d (Nat.mod q d)) (Nat.div q d)))

@[expose] noncomputable def trStep (d : Nat) (L : V) (q : Nat) (acc : V) : V :=
  strictT acc.p fun ap => strictT acc.m fun am => ⟨Nat.lor ap (trBit d L.p q), Nat.lor am (trBit d L.m q)⟩

@[expose] noncomputable def trLane (d : Nat) (L : V) : V :=
  Nat.rec (motive := fun _ => V) ⟨nat_lit 0, nat_lit 0⟩ (fun q acc => trStep d L q acc) (Nat.mul d d)

@[expose] noncomputable def prodL (d E : Nat) (I : V) (Ls : List V) (word : List Nat) : V :=
  word.foldl (fun M x => mulLane d E M (Ls.getD x ⟨0, 0⟩)) I

@[expose] noncomputable def combL (d E : Nat) (I : V) (Ls : List V) (terms : List (Nat × List Nat)) : V :=
  terms.foldl (fun acc t => acc.add (Bool.rec (motive := fun _ => V) (prodL d E I Ls t.2)
    (prodL d E I Ls t.2).neg (Nat.beq t.1 (nat_lit 2)))) ⟨nat_lit 0, nat_lit 0⟩

@[expose] noncomputable def mulVecL (d : Nat) (T u : V) : V :=
  blk d (rmK d (spreadE d (nat_lit 1)) u (blk d T)) (nat_lit 0)

@[expose] noncomputable def spinL (d : Nat) (Ts : List V) (v : V) (tree : List (Nat × Nat)) : Array V :=
  tree.foldl (fun S t => S.push (mulVecL d (Ts.getD t.2 ⟨0, 0⟩) S[t.1]!)) #[v]

end CFSG.KS.F3L

end
