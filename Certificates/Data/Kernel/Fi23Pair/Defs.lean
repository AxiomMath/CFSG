module

public import Certificates.Data.Kernel.Fi23Q.Defs
public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23Pair

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23Q CFSG.KC.Fi23R

@[expose] noncomputable def ordK (G : Nat → Nat) (e : Nat) (y t : List Nat) : Bool :=
  bAnd(eqH G (powW e y) List.nil, bAnd(Bool.not (eqH G y List.nil),
    eqH G (List.append y t) (List.append t y)))

@[expose] noncomputable def stK (G : Nat → Nat) (s t : List Nat) (p : Nat) : Bool :=
  bAnd(eqH G (powW (nat_lit 3) s) List.nil, bAnd(Bool.not (eqH G s List.nil),
    bAnd(Nat.beq (wv G s p) p, Nat.beq (wv G t p) p)))

end CFSG.KC.Fi23Pair

end
