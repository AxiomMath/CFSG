module

public import Certificates.Data.Kernel.E6TT.Weyl
public import Certificates.Data.E6TableTTwo

public section

namespace CFSG.KC.E6TT

open CFSG.KC.Enum (strictB)
open Certificates.Data.E6TableT (Vec iform act)
open Certificates.Data.E6TableTTwo (cosetW orbitLen inOrbit)

@[expose] noncomputable def vecAt (V a : Nat) : Vec :=
  digs (nat_lit 3) (nat_lit 3) (Nat.shiftRight V (Nat.mul (nat_lit 18) a)) (nat_lit 6)

@[expose] noncomputable def bV (V a0 a1 a2 a3 a4 a5 : Nat) : List Vec :=
  [vecAt V a0, vecAt V a1, vecAt V a2, vecAt V a3, vecAt V a4, vecAt V a5]

@[expose] noncomputable def dK (H : List Nat) : List Vec := vecs (H.getD 2 0) (H.getD 0 0)

@[expose] noncomputable def hdK (H : List Nat) : Vec := (dK H).getD 0 []

@[expose] noncomputable def meetK (H : List Nat) (x : Vec) : Bool :=
  (dK H).any fun δ => iform x δ != 0

@[expose] noncomputable def idxK (x : Vec) : List (List Nat) → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun i => i)
    (fun H _ ih i => nIf(meetK H x, i, ih (Nat.succ i)))

@[expose] noncomputable def piK (Hs : List (List Nat)) (b : List Vec) : List Nat :=
  Hs.map fun H => idxK (act b (hdK H)) Hs (nat_lit 0)

@[expose] noncomputable def permK (π : List Nat) (n : Nat) : Bool :=
  bAnd(π.all fun i => Nat.blt i n, (List.range n).all fun i => π.contains i)

@[expose] noncomputable def connK (H : List Nat) : Bool :=
  allIdx (fun t δ => bIf(Nat.beq t (nat_lit 0), true, ((dK H).take t).any fun δ' => iform δ δ' != 0))
    (dK H) (nat_lit 0)

@[expose] noncomputable def sepK (Hs : List (List Nat)) : Bool :=
  (List.range Hs.length).all fun i => (List.range Hs.length).all fun j =>
    bIf(Nat.beq i j, true, !meetK (Hs.getD j []) (hdK (Hs.getD i [])))

@[expose] noncomputable def hsK (Hs : List (List Nat)) : Bool := bAnd(Hs.all connK, sepK Hs)

@[expose] noncomputable def f1 (b : List Vec) : Vec → Vec := act b
@[expose] noncomputable def f2 (b : List Vec) : Vec → Vec := fun x => act b (act b x)
@[expose] noncomputable def f3 (b : List Vec) : Vec → Vec := fun x => act b (act b (act b x))

@[expose] noncomputable def vacA2 (Hs : List (List Nat)) (b : List Vec) (π : List Nat) (j : Nat) :
    Bool :=
  (List.range Hs.length).any fun j' =>
    bAnd(!inOrbit π j j', bIf(!Nat.beq (orbitLen π j') (nat_lit 1), true, inK (Hs.getD j' []) (f1 b)))

@[expose] noncomputable def rowA2 (Hs : List (List Nat)) (Os : List (List (List Nat)))
    (b : List Vec) (π : List Nat) (cw : Bool) (j : Nat) : Bool :=
  strictB (orbitLen π j) fun o =>
  bIf(bAnd(Nat.beq o (nat_lit 1), outK (Hs.getD j []) (Os.getD j []) (f1 b)), true,
    bIf(bIf(cw, bAnd(Nat.beq o (nat_lit 2), inK (Hs.getD j []) (f2 b)),
        bAnd(Nat.beq o (nat_lit 3), outK (Hs.getD j []) (Os.getD j []) (f3 b))), true,
      vacA2 Hs b π j))

@[expose] noncomputable def rowD4 (H : List Nat) (O : List (List Nat)) (b : List Vec) (cw : Bool) :
    Bool :=
  bIf(cw, bAnd(outK H O (f1 b), inK H (f2 b)),
    bIf(inK H (f1 b), true, bAnd(outK H O (f1 b), outK H O (f2 b))))

@[expose] noncomputable def rowK (k : Nat) (Hs : List (List Nat)) (Os : List (List (List Nat)))
    (b : List Vec) : Bool :=
  bAnd(permK (piK Hs b) Hs.length,
  bAnd(bIf(Nat.beq k (nat_lit 1), piK Hs b == [nat_lit 0, nat_lit 1], true),
  bIf(Nat.beq k (nat_lit 0),
    (List.range Hs.length).all (rowA2 Hs Os b (piK Hs b) (cosetW b)),
  bIf(Nat.beq k (nat_lit 1), bAnd(!cosetW b, outK (Hs.getD 0 []) (Os.getD 0 []) (f1 b)),
  bIf(Nat.beq k (nat_lit 2), rowD4 (Hs.getD 0 []) (Os.getD 0 []) b (cosetW b),
  bIf(Nat.beq k (nat_lit 3),
    bIf(cosetW b, inK (Hs.getD 0 []) (f1 b), outK (Hs.getD 0 []) (Os.getD 0 []) (f1 b)),
    bAnd(!cosetW b, outK (Hs.getD 0 []) (Os.getD 0 []) (f1 b))))))))

@[expose] noncomputable def leafK (k : Nat) (Hs : List (List Nat)) (Os : List (List (List Nat)))
    (V : Nat) (a0 a1 a2 a3 a4 a5 : Nat) : Nat :=
  nIf(rowK k Hs Os (bV V a0 a1 a2 a3 a4 a5), nat_lit 0, nat_lit 1)

end CFSG.KC.E6TT

end
