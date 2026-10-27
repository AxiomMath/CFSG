module

public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23Five

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R

@[expose] noncomputable def regSl (H G : Nat → Nat) (r : Nat) (w : List Nat) (lo c : Nat) : Bool :=
  allN c fun i => strictB (Nat.add lo i) fun x => Nat.beq (tb H r x) (wa G w x)

@[expose] def decB : List Nat → Nat → Bool
  | [], _ => true
  | x :: l, b => Nat.blt x b && decB l x

@[expose] noncomputable def fixK (H : Nat → Nat) (w : List Nat) (L : List Nat) : Bool :=
  bAnd(decB L.reverse (nat_lit 31671),bAnd(L.all fun x => Nat.beq (wv H w x) x,
    Nat.beq (cntS (fun x => Nat.beq (wv H w x) x) (nat_lit 0) (nat_lit 31671)) L.length))

@[expose] noncomputable def cmK (G : Nat → Nat) (i j : Nat) : Bool := Nat.beq (tA G i j) j

@[expose] def graphK (c : Nat → Nat → Bool) (G : List Nat) : Bool :=
  !G.isEmpty && (G.all fun i => G.any fun j => j != i && c i j) &&
    (G.all fun i => G.all fun j => c i j || G.any fun k => c k i && c k j)

@[expose] def pathK (c : Nat → Nat → Bool) (F : List Nat) : List Nat :=
  (F.findSome? fun i₁ => F.findSome? fun i₂ =>
    if i₂ == i₁ || c i₁ i₂ then none else F.findSome? fun i₃ =>
      if i₃ == i₁ || i₃ == i₂ || c i₂ i₃ || !c i₁ i₃ then none else F.findSome? fun i₄ =>
        if i₄ == i₁ || i₄ == i₂ || i₄ == i₃ || c i₃ i₄ || !c i₁ i₄ || !c i₂ i₄ then none
        else some [i₁, i₂, i₃, i₄]).getD []

end CFSG.KC.Fi23Five

end
