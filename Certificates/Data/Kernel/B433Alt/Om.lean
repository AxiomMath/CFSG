module

public import Certificates.Data.Kernel.B433Alt.Cov
public import CFSG.Certificates.Kernel.MonsterConv.Perm
public import CFSG.Certificates.Kernel.MonsterConv.PermValid

public section

namespace CFSG.KC.B4A

open CFSG.KC.Y333

@[expose] noncomputable def OW : Nat := nat_lit 524288

@[expose] noncomputable def ON : Nat := nat_lit 412896

@[expose] noncomputable def netOf (MS : Nat → Nat) (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun i acc => Nat.lor acc (Nat.shiftLeft (MS (Nat.add (Nat.mul (nat_lit 37) c) i)) (Nat.mul i OW)))
    (nat_lit 37)

@[expose] noncomputable def netApp19 (MS : Nat → Nat) (c x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun t acc => sN acc (fun a => CFSG.KC.MonsterConv.Perm.dsw
      (CFSG.KC.MonsterConv.Perm.stageShift (nat_lit 19) t) (MS (Nat.add (Nat.mul (nat_lit 37) c) t)) a))
    (nat_lit 37)

@[expose] noncomputable def netAppP (MS : Nat → Nat) (c x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) x
    (fun t acc => sN acc (fun a => CFSG.KC.MonsterConv.Perm.dsw
      (CFSG.KC.MonsterConv.Perm.stageShift (nat_lit 19) t)
      (Nat.mul (MS (Nat.add (Nat.mul (nat_lit 37) c) t)) (CFSG.KC.MonsterConv.Perm.repU OW (nat_lit 19))) a))
    (nat_lit 37)

@[expose] noncomputable def masksOK19 (MS : Nat → Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i acc => andB acc (CFSG.KC.MonsterConv.Perm.dswValid OW
      (CFSG.KC.MonsterConv.Perm.stageShift (nat_lit 19) (Nat.mod i (nat_lit 37))) (MS i)))
    (nat_lit 370)

@[expose] noncomputable def unStepM (m x j : Nat) : Nat :=
  (fun M => (fun y => Nat.lor (Nat.xor x y) (Nat.shiftRight y (Nat.mul (nat_lit 1216) (Nat.shiftLeft (nat_lit 1) j))))
      (Nat.land x M))
    (Nat.mul (rep2 (Nat.mul (nat_lit 1280) (Nat.shiftLeft (nat_lit 2) j)) (Nat.sub (Nat.sub m (nat_lit 1)) j))
      (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.shiftLeft (nat_lit 64) j)) (nat_lit 1))
        (Nat.mul (nat_lit 1280) (Nat.shiftLeft (nat_lit 1) j))))

@[expose] noncomputable def unspreadM (m C k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (Nat.land (Nat.shiftRight C (Nat.mul (nat_lit 64) k))
      (Nat.mul (rep2 (nat_lit 1280) m) (nat_lit 18446744073709551615)))
    (fun j x => unStepM m x j) m

@[expose] noncomputable def catTree (f : Nat → Nat) : Nat → Nat → Nat
  | 0, b => untag (f b)
  | k + 1, b => cat (81920 * 2 ^ k) (catTree f k b) (catTree f k (b + 2 ^ k))

@[expose] noncomputable def colPlane (CB : Nat → Nat) (c b : Nat) : Nat :=
  unspreadM (nat_lit 13) (catTree (fun x => CB (Nat.add (Nat.mul (nat_lit 256) c) x)) 7 0) b

@[expose] noncomputable def netColOK (MS CB : Nat → Nat) (c b : Nat) : Bool :=
  andB (Nat.beq (netApp19 MS c (CFSG.KC.MonsterConv.Perm.idPlane OW b)) (colPlane CB c b))
    (Nat.beq (colPlane CB c (nat_lit 19)) (nat_lit 0))

@[expose] noncomputable def wordOn19 (MS : Nat → Nat) : List Nat → Nat → Nat
  | [], X => X
  | c :: w, X => sN (netAppP MS c X) (fun Y => wordOn19 MS w Y)

@[expose] noncomputable def relOK (MS : Nat → Nat) (w : List Nat) : Bool :=
  Nat.beq (wordOn19 MS w (CFSG.KC.MonsterConv.Perm.idP (nat_lit 19))) (CFSG.KC.MonsterConv.Perm.idP (nat_lit 19))

@[expose] noncomputable def omStep (MS : Nat → Nat) (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) X (fun c acc => Nat.lor acc (netApp19 MS c X)) (nat_lit 10)

@[expose] noncomputable def omAll : Nat := ones ON

@[expose] noncomputable def omOrbitOK (MS : Nat → Nat) (R : Nat) : Bool :=
  andB (Nat.beq (omStep MS omAll) omAll)
    (Nat.beq (Nat.rec (motive := fun _ => Nat) (nat_lit 1) (fun _ X => sN (omStep MS X) (fun Y => Y)) R) omAll)

@[expose] noncomputable def appW19 (MS : Nat → Nat) (w E : Nat) : Nat :=
  sN (wLen w) (fun n =>
    Nat.rec (motive := fun _ => Nat) E
      (fun j acc => sN acc (fun a => netApp19 MS (wAt w (Nat.sub (Nat.sub n (nat_lit 1)) j)) a)) n)

@[expose] noncomputable def appSeg19 (MS : Nat → Nat) (w a n X : Nat) : Nat :=
  sN (wLen w) (fun len =>
    Nat.rec (motive := fun _ => Nat) X
      (fun i acc => sN acc (fun x =>
        netApp19 MS (wAt w (Nat.sub (Nat.sub len (nat_lit 1)) (Nat.add a i))) x)) n)

@[expose] noncomputable def genOf (GS : Nat → Nat) (j s : Nat) : Nat :=
  fld (GS j) (Nat.mul (nat_lit 20) s) (ones (nat_lit 20))

section Seg
variable (MS RD RW PW CB : Nat → Nat) (LIVE : Nat) (RN RL GS GN XO SJ ST SA SN STL : Nat → Nat)
  (NS : Nat)

@[expose] noncomputable def eOf (j s : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (rootSet RD PW CB LIVE j (RN j) (RL j))
    (fun t acc => Nat.lor acc (XO (STL (Nat.add (Nat.mul (nat_lit 128) j) t)))) s

@[expose] noncomputable def segChk (k : Nat) : Bool :=
  sB (SJ k) fun j => sB (ST k) fun s => sB (SA k) fun a => sB (SN k) fun n =>
  sB (genOf GS j s) fun g =>
    andB (Nat.blt k NS) (andB (genOK RD j g) (andB (Nat.ble (Nat.add a n) (wLen (RW g)))
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.beq (SJ (Nat.sub k (nat_lit 1))) j) (andB (Nat.beq (ST (Nat.sub k (nat_lit 1))) s)
          (andB (Nat.beq (Nat.add (SA (Nat.sub k (nat_lit 1))) (SN (Nat.sub k (nat_lit 1)))) a)
            (Nat.beq (appSeg19 MS (RW g) a n (XO (Nat.sub k (nat_lit 1)))) (XO k)))))
        (Nat.beq (appSeg19 MS (RW g) (nat_lit 0) n (eOf RD PW CB LIVE RN RL XO STL j s)) (XO k))
        (Nat.beq a (nat_lit 0)))))

@[expose] noncomputable def finChk (j : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool) true
    (andB (Nat.beq (eOf RD PW CB LIVE RN RL XO STL j (GN j)) omAll)
      (Nat.rec (motive := fun _ => Bool) true
        (fun s acc => andB acc (sB (STL (Nat.add (Nat.mul (nat_lit 128) j) s)) fun k =>
          andB (Nat.blt k NS) (andB (Nat.beq (SJ k) j) (andB (Nat.beq (ST k) s)
            (Nat.beq (Nat.add (SA k) (SN k)) (wLen (RW (genOf GS j s)))))))) (GN j)))
    (Nat.blt (nat_lit 0) (Nat.land LIVE (Nat.shiftLeft (nat_lit 1) j)))

end Seg

end CFSG.KC.B4A

end
