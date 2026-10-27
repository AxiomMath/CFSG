module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.O8

open CFSG.KC.Enum

@[expose] noncomputable def colK (M c : Nat) : Nat := fld(M, Nat.mul (nat_lit 8) c, nat_lit 255)

@[expose] noncomputable def matAppK (M v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c ih => Nat.xor ih (nIf(Nat.beq (Nat.land (Nat.shiftRight v c) (nat_lit 1)) (nat_lit 1),
      colK M c, nat_lit 0))) (nat_lit 8)

@[expose] noncomputable def matMulK (A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun c ih => Nat.xor ih (Nat.mul (Nat.land (Nat.shiftRight B c) (nat_lit 72340172838076673))
      (colK A c))) (nat_lit 8)

@[expose] noncomputable def idK : Nat := nat_lit 9241421688590303745

@[expose] noncomputable def actsK (NS NI P M : Nat) : Bool :=
  allN (nat_lit 120) fun p => strictB (pg (nat_lit 9) (nat_lit 511) P p) fun x =>
    bAnd(Nat.blt x (nat_lit 120), Nat.beq x (pg (nat_lit 8) (nat_lit 255) NI
      (matAppK M (pg (nat_lit 8) (nat_lit 255) NS p))))

@[expose] noncomputable def saAtK (SC i : Nat) : Nat :=
  fld(SC, Nat.mul (nat_lit 64) i, nat_lit 18446744073709551615)

@[expose] noncomputable def ix13 (T i : Nat) : Nat := fld(T, Nat.mul (nat_lit 13) i, nat_lit 8191)

@[expose] noncomputable def saClosedAt (SC MT GT i : Nat) : Bool :=
  strictB (saAtK SC i) fun x => allN (nat_lit 5) fun l =>
    Nat.beq (matMulK (saAtK SC (ix13 GT l)) x)
      (saAtK SC (ix13 MT (Nat.add (Nat.mul (nat_lit 5) i) l)))

@[expose] noncomputable def saTreeAt (MT PT LT i : Nat) : Bool :=
  bIf(Nat.beq i (nat_lit 0), true,
    strictB (ix13 PT i) fun p => strictB (fld(LT, Nat.mul (nat_lit 3) i, nat_lit 7)) fun l =>
      bAnd(Nat.blt p i, bAnd(Nat.blt l (nat_lit 5),
        Nat.beq (ix13 MT (Nat.add (Nat.mul (nat_lit 5) p) l)) i)))

@[expose] noncomputable def saSortAt (SC SP SPI i : Nat) : Bool :=
  bAnd(Nat.blt (ix13 SPI i) (nat_lit 8192), bAnd(Nat.beq (ix13 SP (ix13 SPI i)) i,
    bIf(Nat.blt i (nat_lit 8191),
      Nat.blt (saAtK SC (ix13 SP i)) (saAtK SC (ix13 SP (Nat.succ i))), true)))

@[expose] noncomputable def involAt (SC YI WT i : Nat) : Bool :=
  strictB (saAtK SC i) fun x =>
  bIf(bAnd(bIf(Nat.beq i (nat_lit 0), false, true), Nat.beq (matMulK x x) idK),
    strictB (fld(WT, Nat.add (Nat.mul (nat_lit 32) i) (nat_lit 26), nat_lit 63)) fun j =>
    strictB (fld(WT, Nat.add (Nat.mul (nat_lit 32) i) (nat_lit 13), nat_lit 8191)) fun c =>
    strictB (fld(WT, Nat.mul (nat_lit 32) i, nat_lit 8191)) fun ci =>
      bAnd(Nat.blt j (nat_lit 38), bAnd(Nat.blt c (nat_lit 8192), bAnd(Nat.blt ci (nat_lit 8192),
      bAnd(Nat.beq (matMulK (saAtK SC c) (saAtK SC ci)) idK,
        Nat.beq (matMulK (matMulK (saAtK SC c) (saAtK SC (ix13 YI j))) (saAtK SC ci)) x)))),
    true)

@[expose] noncomputable def conjK (G Gi : Nat → Nat) (w : List Nat) (b : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) b (fun l _ ih => matMulK (matMulK (G l) ih) (Gi l)) w

@[expose] noncomputable def memK (x : Nat) (found : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ ih => bIf(Nat.beq a x, true, ih)) found

@[expose] noncomputable def greedyK (G Gi : Nat → Nat) (b : Nat) (ws : List (List Nat)) :
    List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun found => Nat.ble (nat_lit 5) found.length)
    (fun w _ ih found => bIf(Nat.ble (nat_lit 5) found.length, true,
      strictB (conjK G Gi w b) fun c => bIf(memK c found, ih found, ih (c :: found)))) ws

@[expose] noncomputable def fiveAt (SC YI RG RGI : Nat) (ws : List (List Nat)) (j i : Nat) : Bool :=
  strictB (saAtK SC i) fun x => strictB (matMulK x x) fun x2 =>
  strictB (saAtK SC (ix13 YI j)) fun y =>
    bIf(bAnd(bIf(Nat.beq x2 idK, false, true), bAnd(Nat.beq (matMulK x2 x2) idK,
        Nat.beq (matMulK x y) (matMulK y x))),
      greedyK (fun l => saAtK RG (Nat.add (Nat.mul (nat_lit 5) j) l))
        (fun l => saAtK RGI (Nat.add (Nat.mul (nat_lit 5) j) l)) x ws [], true)

end CFSG.KC.O8

end
