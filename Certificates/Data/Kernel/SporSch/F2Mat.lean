module

public import Certificates.Data.Kernel.Spor.Prim

public section

namespace CFSG.KS.SporSch

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def rowP (d M i : Nat) : Nat := fld(M, Nat.mul d i, mask d)

@[expose] noncomputable def bitN (x k : Nat) : Nat := Nat.land (Nat.shiftRight x k) (nat_lit 1)

@[expose] noncomputable def vmP (d M v : Nat) : Nat :=
  foldN d (fun j acc => nIf(Nat.beq (bitN v j) (nat_lit 1), Nat.xor acc (rowP d M j), acc))
    (nat_lit 0)

@[expose] noncomputable def packR (d : Nat) (f : Nat → Nat) : Nat :=
  foldN d (fun i acc => Nat.lor acc (Nat.shiftLeft (f i) (Nat.mul d i))) (nat_lit 0)

@[expose] noncomputable def mulP (d X Y : Nat) : Nat := packR d (fun i => vmP d Y (rowP d X i))

@[expose] noncomputable def idP (d : Nat) : Nat := packR d (fun i => Nat.shiftLeft (nat_lit 1) i)

@[expose] noncomputable def powP (d M e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (idP d) (fun _ acc => strictN acc (fun a => mulP d a M)) e

@[expose] noncomputable def transP (d M : Nat) : Nat :=
  packR d (fun j => foldN d (fun i acc => nIf(Nat.beq (bitN (rowP d M i) j) (nat_lit 1),
    Nat.lor acc (Nat.shiftLeft (nat_lit 1) i), acc)) (nat_lit 0))

@[expose] noncomputable def pidx (i j : Nat) : Nat :=
  Nat.add (Nat.sub (Nat.mul (nat_lit 22) i) (Nat.div (Nat.mul i (Nat.sub i (nat_lit 1))) (nat_lit 2)))
    (Nat.sub j i)

@[expose] noncomputable def triP (t : Nat) : Nat :=
  packR (nat_lit 22) (fun i => foldN (nat_lit 22) (fun j acc =>
    nIf(bAnd(Nat.ble i j, Nat.beq (bitN t (pidx i j)) (nat_lit 1)),
      Nat.lor acc (Nat.shiftLeft (nat_lit 1) j), acc)) (nat_lit 0))

@[expose] noncomputable def coefN (C i j : Nat) : Nat :=
  nIf(Nat.beq i j, bitN (rowP (nat_lit 22) C i) i,
    Nat.xor (bitN (rowP (nat_lit 22) C i) j) (bitN (rowP (nat_lit 22) C j) i))

@[expose] noncomputable def coefOKK (C t : Nat) : Bool :=
  allN (nat_lit 22) (fun i => allN (nat_lit 22) (fun j =>
    bIf(Nat.ble i j, Nat.beq (coefN C i j) (bitN t (pidx i j)), true)))

@[expose] noncomputable def pullK (A t t' : Nat) : Bool :=
  coefOKK (mulP (nat_lit 22) (transP (nat_lit 22) A) (mulP (nat_lit 22) (triP t') A)) t

@[expose] noncomputable def offK (t t' : Nat) : Bool :=
  allN (nat_lit 22) (fun i => allN (nat_lit 22) (fun j =>
    bIf(Nat.blt i j, Nat.beq (bitN t (pidx i j)) (bitN t' (pidx i j)), true)))

@[expose] noncomputable def diagK (t : Nat) : Nat :=
  foldN (nat_lit 22) (fun i acc => nIf(Nat.beq (bitN t (pidx i i)) (nat_lit 1),
    Nat.lor acc (Nat.shiftLeft (nat_lit 1) i), acc)) (nat_lit 0)

@[expose] noncomputable def wsK (c : Nat) : Bool :=
  bIf(Nat.beq c (nat_lit 32), true, bIf(Nat.beq c (nat_lit 9), true, bIf(Nat.beq c (nat_lit 10), true,
    bIf(Nat.beq c (nat_lit 13), true, bIf(Nat.beq c (nat_lit 11), true, Nat.beq c (nat_lit 12))))))

@[expose] noncomputable def parK (c : Nat) : Nat :=
  nIf(bAnd(Nat.ble (nat_lit 48) c, Nat.ble c (nat_lit 57)),
    Nat.land (Nat.sub c (nat_lit 48)) (nat_lit 1), nat_lit 0)

@[expose] noncomputable def payRun (d : Nat) (cs : List Char) : Nat → Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Nat) (fun _ _ M => M)
    (fun ch _ ih ph idx M => strictN (Char.toNat ch) (fun c =>
      nIf(Nat.beq ph (nat_lit 0),
        nIf(Nat.beq c (nat_lit 10), ih (nat_lit 1) idx M, ih (nat_lit 0) idx M),
        nIf(wsK c, ih (nat_lit 1) idx M,
          strictN (nIf(bAnd(Nat.beq (parK c) (nat_lit 1), Nat.blt idx (Nat.mul d d)),
              Nat.lor M (Nat.shiftLeft (nat_lit 1) idx), M)) (fun M' =>
            ih (nat_lit 1) (Nat.succ idx) M')))))
    cs

@[expose] noncomputable def payK (cs : List Char) (d R : Nat) : Bool :=
  Nat.beq (payRun d cs (nat_lit 0) (nat_lit 0) (nat_lit 0)) R

end CFSG.KS.SporSch

end
