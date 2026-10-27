module

public import Certificates.Data.Kernel.KDense.Init

public section

namespace CFSG.KC.KDense

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop

@[expose] noncomputable def svRec (OCT p : Nat) : Nat :=
  (fun neg => Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat)
      ((fun pp => (fun i j => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
          (Nat.lor (Nat.shiftLeft (nat_lit 4) (Nat.mul (nat_lit 4) i))
            (Nat.shiftLeft (Bool.rec (motive := fun _ => Nat) (nat_lit 4) (nat_lit 11) (Nat.beq (bitN pp (nat_lit 10)) (nat_lit 0)))
              (Nat.mul (nat_lit 4) j)))
          (andB (Nat.blt pp (nat_lit 2048)) (andB (Nat.blt i j) (Nat.blt j (nat_lit 24)))))
          (Nat.land (Nat.shiftRight pp (nat_lit 5)) (nat_lit 31)) (Nat.land pp (nat_lit 31)))
        (Nat.sub p (nat_lit 114688)))
      ((fun q => (fun w => (fun d => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
            (fun k acc => Nat.lor acc (Nat.shiftLeft
              (Nat.mod (Nat.sub (Nat.add (nat_lit 15) (Nat.mul (nat_lit 2) (bitN w k))) (Nat.mul (nat_lit 4) (bitN d k)))
                (nat_lit 15)) (Nat.mul (nat_lit 4) k))) (nat_lit 24))
          (spreadT w ((fun r => Nat.add (Nat.shiftLeft r (nat_lit 1)) (parT (nat_lit 6) r)) (Nat.land q (nat_lit 63)))))
          (wordT (f12 OCT (Nat.shiftRight q (nat_lit 6)))))
        (Nat.sub p (nat_lit 65536)))
      (Nat.blt p (nat_lit 114112)))
    ((fun t i => Bool.rec (motive := fun _ => Nat) (nat_lit 0)
        ((fun w => Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun k acc => Nat.lor acc (Nat.shiftLeft
            (neg (bitN w k) (Bool.rec (motive := fun _ => Nat) (nat_lit 1) (nat_lit 12) (Nat.beq k i)))
            (Nat.mul (nat_lit 4) k))) (nat_lit 24)) (wordT (Nat.shiftLeft t (nat_lit 1))))
        (Nat.blt i (nat_lit 24)))
      (Nat.shiftRight p (nat_lit 5)) (Nat.land p (nat_lit 31)))
    (Nat.blt p (nat_lit 65536)))
  (fun b r => Bool.rec (motive := fun _ => Nat) r (Nat.mod (Nat.sub (nat_lit 15) r) (nat_lit 15)) (Nat.beq b (nat_lit 1)))

@[expose] noncomputable def utRange (OCT d : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool)
    (fun K lo => Nat.beq K (svRec OCT lo))
    (fun e ih K lo => (fun h => andB (ih (Nat.land K (ones (Nat.mul (nat_lit 128) h))) lo)
        (ih (Nat.shiftRight K (Nat.mul (nat_lit 128) h)) (Nat.add lo h)))
      (Nat.shiftLeft (nat_lit 1) e)) d

@[expose] noncomputable def utSlice (UT i : Nat) : Nat :=
  Nat.land (Nat.shiftRight UT (Nat.mul i (nat_lit 2097152))) (ones (nat_lit 2097152))

@[expose] noncomputable def utOK (OCT UT : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun i ih => andB (utRange OCT (nat_lit 14) (utSlice UT i) (Nat.mul i (nat_lit 16384))) ih) (nat_lit 8)

@[expose] noncomputable def uFromUT (UT l : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Nat.lor acc (Nat.shiftLeft
      (rawPlane UT (nat_lit 128) SX (nat_lit 17) (nat_lit 0) (Nat.add (Nat.mul (nat_lit 4) l) b)) (Nat.mul b SX)))
    (nat_lit 4)

@[expose] noncomputable def uVec (U l : Nat) : Nat :=
  Nat.land (Nat.shiftRight U (Nat.mul l (Nat.mul (nat_lit 4) SX))) (m4 SX)

@[expose] noncomputable def uPlanesOK (UT U : Nat) : Bool :=
  andB (Nat.blt U (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 24) (Nat.mul (nat_lit 4) SX))))
    (Nat.rec (motive := fun _ => Bool) true (fun l ih => andB (Nat.beq (uVec U l) (uFromUT UT l)) ih) (nat_lit 24))

@[expose] noncomputable def mEnt (MK k i j : Nat) : Nat :=
  fld(MK, Nat.mul (nat_lit 4) (Nat.add (Nat.mul (nat_lit 576) k) (Nat.add (Nat.mul (nat_lit 24) i) j)), nat_lit 15)

@[expose] noncomputable def mkOK (tab : Array Int) (MK : Nat) : Bool :=
  (fun l => andB (Nat.blt MK (Nat.shiftLeft (nat_lit 1) (Nat.mul (nat_lit 4) (Nat.mul (nat_lit 576) (nat_lit 15)))))
    (Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (Nat.rec (motive := fun _ => Bool) true
      (fun j ih2 => andB (Nat.beq (mEnt MK (nat_lit 0) i j) (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1)
        (Nat.beq i j)))
        (andB (Nat.rec (motive := fun _ => Bool) true
          (fun k ih3 => andB (Nat.beq (mEnt MK (Nat.add k (nat_lit 1)) i j)
            (Nat.mod (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
              (fun m acc => Nat.add acc (Nat.mul (mEnt MK k i m) (res15I (lgetI l (aIdxT m j))))) (nat_lit 24))
              (nat_lit 15))) ih3) (nat_lit 14)) ih2)) (nat_lit 24)) ih) (nat_lit 24)))
  (Array.rec (motive := fun _ => List Int) (fun l => l) tab)

@[expose] noncomputable def mulC (c x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => Bool.rec (motive := fun _ => Nat) acc (add15 SX acc (rotk SX b x)) (Nat.beq (bitN c b) (nat_lit 1)))
    (nat_lit 4)

@[expose] noncomputable def mulV (x y : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b acc => add15 SX acc (Nat.land (rotk SX b x) (rep4 SX (plane SX b y)))) (nat_lit 4)

@[expose] noncomputable def qVec (U MK k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun l acc => strictN (add15 SX acc (mulV (uVec U l)
      (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun m acc2 => strictN (add15 SX acc2 (mulC (mEnt MK k l m) (uVec U m))) (fun y => y)) (nat_lit 24))))
      (fun y => y)) (nat_lit 24)

@[expose] noncomputable def qOK (U MK k Q : Nat) : Bool := Nat.beq (norm15 SX (qVec U MK k)) (norm15 SX Q)

@[expose] noncomputable def dig5 (x : Nat) : Nat :=
  (fun p0 p1 p2 p3 =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun r acc => (fun m => Nat.lor acc (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
          (fun b acc2 => Nat.lor acc2 (Nat.shiftLeft (selB (bitN (Nat.mod (Nat.mod r (nat_lit 15)) (nat_lit 5)) b) m)
            (Nat.mul b SX))) (nat_lit 3)))
        (Nat.land (Nat.land (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) p0) p0 (Nat.beq (bitN r 0) 1))
            (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) p1) p1 (Nat.beq (bitN r 1) 1)))
          (Nat.land (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) p2) p2 (Nat.beq (bitN r 2) 1))
            (Bool.rec (motive := fun _ => Nat) (Nat.xor (ones SX) p3) p3 (Nat.beq (bitN r 3) 1)))))
      (nat_lit 16))
  (plane SX 0 x) (plane SX 1 x) (plane SX 2 x) (plane SX 3 x)

@[expose] noncomputable def lexStep (lt eq d e : Nat) : Nat × Nat :=
  (fun d0 d1 d2 e0 e1 e2 =>
    (fun x2 x1 x0 =>
      (fun dlt => (Nat.lor lt (Nat.land eq dlt), Nat.land eq (Nat.land x2 (Nat.land x1 x0))))
      (Nat.lor (Nat.land (Nat.xor (ones SX) d2) e2)
        (Nat.land x2 (Nat.lor (Nat.land (Nat.xor (ones SX) d1) e1) (Nat.land x1 (Nat.land (Nat.xor (ones SX) d0) e0))))))
      (Nat.xor (ones SX) (Nat.xor d2 e2)) (Nat.xor (ones SX) (Nat.xor d1 e1)) (Nat.xor (ones SX) (Nat.xor d0 e0)))
  (plane SX 0 d) (plane SX 1 d) (plane SX 2 d) (plane SX 0 e) (plane SX 1 e) (plane SX 2 e)

@[expose] noncomputable def sortOK (QS : Nat → Nat) (NS : Nat) : Bool :=
  andB (netOK (nat_lit 17) NS) (andB (Nat.beq (netP SX (nat_lit 17) (nat_lit 1) NS validX) (ones (nat_lit 98280)))
    (Prod.rec (motive := fun _ => Bool) (fun lt _ => Nat.beq (Nat.land lt (ones (nat_lit 98279))) (ones (nat_lit 98279)))
      (Nat.rec (motive := fun _ => Nat × Nat) (nat_lit 0, ones SX)
        (fun j ih => Prod.rec (motive := fun _ => Nat × Nat) (fun lt eq =>
          (fun d => lexStep lt eq d (Nat.land (Nat.shiftRight d (nat_lit 1)) (repP SX (nat_lit 3) (ones (Nat.sub SX 1)))))
            (dig5 (netP SX (nat_lit 17) (nat_lit 4) NS (QS (Nat.sub (nat_lit 14) j))))) ih)
        (nat_lit 14))))

end CFSG.KC.KDense

end
