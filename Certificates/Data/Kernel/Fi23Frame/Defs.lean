module

public import Certificates.Data.Kernel.Fi23R.Defs

public section

namespace CFSG.KC.Fi23Frame

open CFSG.KC.Enum CFSG.KC.Fi23K CFSG.KC.Fi23R

@[expose] def frPts : List Nat :=
  [0, 830, 1493, 1795, 10795, 4391, 13637, 29382, 17196, 14554, 8136, 4576, 21555, 13389, 6282,
    22056, 29944, 29779, 17072, 15480, 28185, 18757, 14065]

@[expose] def frMasks : List Nat :=
  [7684609, 3817986, 3113476, 6062600, 5742608, 2580512, 3252800, 5137024, 4440832, 6988800,
    5859328, 3993600]

@[expose] def frW (P L : List Nat) : List Nat :=
  (L.map fun i => Nat.add (nat_lit 128) (List.getD P i (nat_lit 0))).reverse

@[expose] def frBits (m : Nat) : List Nat :=
  (List.range (nat_lit 23)).filter fun i =>
    Nat.beq (Nat.land (Nat.shiftRight m i) (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def frComm (G : Nat → Nat) (P : List Nat) : Bool :=
  allN (nat_lit 23) fun i => allN i fun j => eqB G (frW P [i, j]) (frW P [j, i])

@[expose] noncomputable def frNe (G : Nat → Nat) (u v : List Nat) : Bool := Bool.not (eqB G u v)

@[expose] noncomputable def frTripAt (G : Nat → Nat) (P : List Nat) (i j k : Nat) : Bool :=
  bIf(Nat.beq i j, true, bIf(Nat.beq k i, true, bIf(Nat.beq k j, true,
    frNe G (frW P [i, j]) (frW P [k]))))

@[expose] noncomputable def frTrip (G : Nat → Nat) (P : List Nat) (lo len : Nat) : Bool :=
  allN len fun d => allN (nat_lit 23) fun j => allN (nat_lit 23) fun k =>
    frTripAt G P (Nat.add lo d) j k

@[expose] noncomputable def frRows (G : Nat → Nat) (P M : List Nat) : Bool :=
  allN (nat_lit 12) fun r => eqB G (frW P (frBits (List.getD M r (nat_lit 0)))) []

end CFSG.KC.Fi23Frame

end
