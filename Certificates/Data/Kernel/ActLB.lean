module

public import Certificates.Data.Kernel.YModel.Model

public section

namespace CFSG.KC.ActLB

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.YModel

@[expose] noncomputable def lcode {m : Nat} (a : Fin m × Bool) : Nat :=
  Nat.add (Nat.mul (nat_lit 2) a.1.val) (Bool.rec (motive := fun _ => Nat) (nat_lit 1) (nat_lit 0) a.2)

@[expose] noncomputable def codesOf {m : Nat} (ws : List (List (Fin m × Bool))) : List (List Nat) :=
  ws.map fun w => w.map lcode

@[expose] noncomputable def invPairs (m : Nat) : List (List Nat) :=
  (List.range m).map fun x => [2 * x, 2 * x + 1]

@[expose] noncomputable def nets (n : Nat) (Nf : Nat → Nat) : List Nat :=
  (List.range n).map Nf

@[expose] noncomputable def fixK (k N b : Nat) : Bool :=
  Nat.beq (netApply k (wid k) (nat_lit 1) N (Nat.shiftLeft (nat_lit 1) b)) (Nat.shiftLeft (nat_lit 1) b)

end CFSG.KC.ActLB

end
