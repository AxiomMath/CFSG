module

public import Certificates.Data.Kernel.LocalQT.SylV

public section

namespace CFSG.KC.LQT.JX

open CFSG.KC.Enum CFSG.KS CFSG.KS.Prim CFSG.KC.LQT.TC CFSG.KC.LQT.SV

@[expose] noncomputable def mtJ (b : Nat) (MR : Nat → Nat) (i j : Nat) : Nat :=
  pg b (mask b) (MR i) j

@[expose] noncomputable def isInvJ (b : Nat) (MR : Nat → Nat) (i : Nat) : Bool :=
  bAnd(bIf(Nat.beq i (nat_lit 0), false, true), Nat.beq (mtJ b MR i i) (nat_lit 0))

@[expose] noncomputable def conjJ (b : Nat) (MR IT : Nat → Nat) (s i : Nat) : Nat :=
  mtJ b MR (mtJ b MR s i) (IT s)

@[expose] noncomputable def inFgJ (b : Nat) (MR : Nat → Nat) (a b' u : Nat) : Bool :=
  bIf(Nat.beq u a, true, bIf(Nat.beq u b', true, Nat.beq u (mtJ b MR a b')))

@[expose] noncomputable def getP2 (L : List (Nat × Nat)) (k : Nat) : Nat × Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat) (fun _ => Prod.mk 0 0)
    (fun x _ ih k => Nat.rec (motive := fun _ => Nat × Nat) x (fun j _ => ih j) k) L k

@[expose] noncomputable def len2 (L : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def witJ (b N : Nat) (MR IT : Nat → Nat) (reps : List (Nat × Nat))
    (i j v : Nat) : Bool :=
  bIf(Nat.beq v (nat_lit 0), true,
    strictB (Nat.shiftRight (Nat.sub v 1) 8) fun a => strictB (Nat.land (Nat.sub v 1) 255) fun s =>
      bAnd(isInvJ b MR i, bAnd(isInvJ b MR j, bAnd(Nat.beq (mtJ b MR i j) (mtJ b MR j i),
        bAnd(Nat.blt a (len2 reps), bAnd(Nat.blt s N,
          Prod.rec (motive := fun _ => Bool) (fun ra rb =>
            strictB (conjJ b MR IT s i) fun ci => strictB (conjJ b MR IT s j) fun cj =>
              bAnd(bIf(Nat.beq ci cj, false, true),
                bAnd(inFgJ b MR ra rb ci, inFgJ b MR ra rb cj))) (getP2 reps a)))))))

@[expose] noncomputable def rowJX (b gb N ng : Nat) (PT LT TB MR IT GW : Nat → Nat)
    (reps : List (Nat × Nat)) (i : Nat) : Bool :=
  bAnd(Nat.beq (mtJ b MR i (nat_lit 0)) i,
  bAnd(allBlk (nat_lit 0) (fun j => strictB (mtJ b MR i j) fun m => bAnd(Nat.blt m N,
      bIf(Nat.beq j (nat_lit 0), true, strictB (PT j) fun p => strictB (LT j) fun l =>
        bAnd(Nat.blt p j, bAnd(Nat.blt l ng,
          Nat.beq m (TB (Nat.add (Nat.mul (mtJ b MR i p) ng) l))))))) N,
  bAnd(strictB (IT i) fun t => bAnd(Nat.blt t N, bAnd(Nat.beq (mtJ b MR i t) (nat_lit 0),
      allBlk (nat_lit 0) (fun j => bIf(Nat.beq (mtJ b MR i j) (nat_lit 0), false, true)) t)),
    allBlk (nat_lit 0) (fun j => witJ b N MR IT reps i j (pg gb (mask gb) (GW i) j)) N)))

@[expose] noncomputable def rowsJX (b gb N ng : Nat) (PT LT TB MR IT GW : Nat → Nat)
    (reps : List (Nat × Nat)) (lo len : Nat) : Bool :=
  allBlk lo (fun i => bIf(Nat.blt i N, rowJX b gb N ng PT LT TB MR IT GW reps i, true)) len

@[expose] noncomputable def repsJX (b N : Nat) (MR : Nat → Nat) (reps : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun ab _ ih => bAnd(Nat.blt ab.1 N, bAnd(Nat.blt ab.2 N,
      bAnd(isInvJ b MR ab.1, bAnd(isInvJ b MR ab.2, ih))))) reps

@[expose] noncomputable def invsJX (b N : Nat) (MR : Nat → Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) List.nil
    (fun i ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons i ih) (isInvJ b MR i)) N

@[expose] noncomputable def goodJ (gb : Nat) (GW : Nat → Nat) (i j : Nat) : Bool :=
  bIf(Nat.beq (pg gb (mask gb) (GW i) j) (nat_lit 0), false, true)

@[expose] noncomputable def tripJ (b gb : Nat) (MR GW : Nat → Nat) (i j k : Nat) : Bool :=
  bIf(bAnd(bIf(Nat.beq i j, false, true), bAnd(bIf(Nat.beq i k, false, true),
      bAnd(bIf(Nat.beq i (mtJ b MR j k), false, true), bAnd(bIf(Nat.beq j k, false, true),
      bAnd(Nat.beq (mtJ b MR i j) (mtJ b MR j i), bAnd(Nat.beq (mtJ b MR i k) (mtJ b MR k i),
        Nat.beq (mtJ b MR j k) (mtJ b MR k j))))))),
    bIf(goodJ gb GW i j, true, bIf(goodJ gb GW i k, true, goodJ gb GW j k)), true)

@[expose] noncomputable def triJX (b gb N : Nat) (MR GW : Nat → Nat) (i : Nat) : Bool :=
  bIf(isInvJ b MR i,
    (fun (L : List Nat) => List.rec (motive := fun _ => Bool) true
      (fun j _ ih => bAnd(List.rec (motive := fun _ => Bool) true
        (fun k _ ih2 => bAnd(tripJ b gb MR GW i j k, ih2)) L, ih)) L) (invsJX b N MR),
    true)

@[expose] noncomputable def trisJX (b gb N : Nat) (MR GW : Nat → Nat) (lo len : Nat) : Bool :=
  allBlk lo (fun i => bIf(Nat.blt i N, triJX b gb N MR GW i, true)) len

end CFSG.KC.LQT.JX

end
