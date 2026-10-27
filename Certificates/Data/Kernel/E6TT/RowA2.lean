module

public import Certificates.Data.Kernel.E6TT.Row

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictB)
open Certificates.Data.E6TableT (Vec)
open Certificates.Data.E6TableTTwo (cosetW)

@[expose] noncomputable def rowA2Body (Hs : List (List Nat)) (Os : List (List (List Nat)))
    (b : List Vec) (π : List Nat) (cw : Bool) : Bool :=
  bAnd(Nat.beq Hs.length (nat_lit 3), bAnd(permK π (nat_lit 3),
    (List.range (nat_lit 3)).all (rowA2 Hs Os b π cw)))

@[expose] noncomputable def rowKA2 (Hs : List (List Nat)) (Os : List (List (List Nat)))
    (b : List Vec) : Bool :=
  strictB ((piK Hs b).getD (nat_lit 0) (nat_lit 0)) fun p0 =>
  strictB ((piK Hs b).getD (nat_lit 1) (nat_lit 0)) fun p1 =>
  strictB ((piK Hs b).getD (nat_lit 2) (nat_lit 0)) fun p2 =>
  bIf(cosetW b, rowA2Body Hs Os b [p0, p1, p2] true, rowA2Body Hs Os b [p0, p1, p2] false)

@[expose] noncomputable def leafKA2 (Hs : List (List Nat)) (Os : List (List (List Nat)))
    (V : Nat) (a0 a1 a2 a3 a4 a5 : Nat) : Nat :=
  nIf(rowKA2 Hs Os (bV V a0 a1 a2 a3 a4 a5), nat_lit 0, nat_lit 1)

end CFSG.KC.E6TT

end
