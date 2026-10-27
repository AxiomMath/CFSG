module

public import Certificates.Data.HatA6Embed
public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.HatA6

open CFSG.Quasithin.H13.HatE CFSG.Quasithin.H13.HatC CFSG.Quasithin.H13.HatM

@[expose] noncomputable def fldR (M k : Nat) : Nat := Nat.land (Nat.shiftRight M (Nat.mul 6 k)) 63

@[expose] noncomputable def mactR (M c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun n ih => Nat.xor ih
    (nIf(Nat.beq (Nat.land (Nat.shiftRight c n) 1) 1, fldR M n, 0))) 6

@[expose] noncomputable def pk6 (a b c d e f : Nat) : Nat :=
  Nat.lor a (Nat.lor (Nat.shiftLeft b 6) (Nat.lor (Nat.shiftLeft c 12)
    (Nat.lor (Nat.shiftLeft d 18) (Nat.lor (Nat.shiftLeft e 24) (Nat.shiftLeft f 30)))))

@[expose] noncomputable def unpackL (M : Nat) : List Nat :=
  [fldR M 0, fldR M 1, fldR M 2, fldR M 3, fldR M 4, fldR M 5]

@[expose] noncomputable def packL (m : List Nat) : Nat :=
  pk6 (m.getD 0 0) (m.getD 1 0) (m.getD 2 0) (m.getD 3 0) (m.getD 4 0) (m.getD 5 0)

@[expose] noncomputable def mmulR (A B : Nat) : Nat :=
  pk6 (mactR A (fldR B 0)) (mactR A (fldR B 1)) (mactR A (fldR B 2)) (mactR A (fldR B 3))
    (mactR A (fldR B 4)) (mactR A (fldR B 5))

@[expose] noncomputable def IDC : Nat := pk6 1 2 4 8 16 32

@[expose] noncomputable def OMC : Nat := pk6 2 3 8 12 32 48

@[expose] noncomputable def A0C : Nat := pk6 42 63 4 8 45 54

@[expose] noncomputable def powR (M n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) IDC (fun _ ih => mmulR M ih) n

@[expose] noncomputable def allR (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => bAnd(f i, ih)) n

@[expose] noncomputable def injR (M : Nat) : Bool :=
  allR 63 (fun c => bIf(Nat.beq (mactR M (Nat.succ c)) 0, false, true))

@[expose] noncomputable def inZR (X : Nat) : Bool :=
  bIf(Nat.beq X IDC, true, bIf(Nat.beq X OMC, true, Nat.beq X (mmulR OMC OMC)))

@[expose] noncomputable def invHypR (M : Nat) : Bool :=
  bAnd(Nat.beq (mactR M (fldR M 0)) 1, bAnd(Nat.beq (mmulR M M) IDC,
    bAnd(injR M, bIf(Nat.beq M IDC, false, true))))

@[expose] noncomputable def genHypR (M : Nat) : Bool :=
  bAnd(Nat.beq (mactR M (mactR M (mactR M (fldR M 0)))) 1, bAnd(Nat.beq (powR M 4) IDC,
    bAnd(injR M, bAnd(inZR (powR (mmulR A0C M) 5), inZR (powR (mmulR A0C (mmulR M M)) 5)))))

@[expose] noncomputable def hcR (c0 c2 c4 : Nat) : Nat :=
  pk6 c0 (mactR OMC c0) c2 (mactR OMC c2) c4 (mactR OMC c4)

@[expose] noncomputable def invSliceR (lo len : Nat) : Bool :=
  allR len (fun i => allR 64 (fun c2 => allR 64 (fun c4 =>
    bIf(invHypR (hcR (Nat.add lo i) c2 c4), invOK (unpackL (hcR (Nat.add lo i) c2 c4)), true))))

@[expose] noncomputable def genSliceR (lo len : Nat) : Bool :=
  allR len (fun i => allR 64 (fun c2 => allR 64 (fun c4 =>
    bIf(genHypR (hcR (Nat.add lo i) c2 c4), genOK (unpackL (hcR (Nat.add lo i) c2 c4)), true))))

@[expose] noncomputable def memR (x : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun y _ ih => bIf(Nat.beq y x, true, ih)) L

@[expose] noncomputable def g0R (G : List Nat) : Bool :=
  bAnd(memR IDC G, List.rec (motive := fun _ => Bool) true (fun M _ ih =>
    bAnd(memR (mmulR (pk6 4 8 16 32 21 42) M) G, bAnd(memR (mmulR (pk6 16 32 4 8 57 30) M) G,
      bAnd(memR (mmulR (pk6 21 42 1 2 4 8) M) G, bAnd(memR (mmulR (pk6 27 45 4 8 1 2) M) G, ih)))))
    G)

end CFSG.KC.HatA6

end
