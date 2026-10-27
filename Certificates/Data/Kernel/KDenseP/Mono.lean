module

public import Certificates.Data.Kernel.KDenseP.Letters

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense

structure MonoE where
  cn : Nat
  on : Nat
  qn : Nat
  sel : Nat
  xsel : Nat
  wn : Nat
  psw : Nat
  sgX : Nat
  sgW : Nat
  sgA : Nat

structure MonoTab where
  keys : List (List Nat)
  ents : Nat → MonoE

@[expose] noncomputable def netRepN (S n k U R N x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun j ih y => strictN
      ((fun i => dsw (stageShift k i)
          (repN S n (Nat.land R (Nat.mul (Nat.land (Nat.shiftRight N (Nat.mul i (Nat.shiftLeft (nat_lit 1) k)))
            (ones (Nat.shiftLeft (nat_lit 1) k))) U))) y)
        (Nat.sub (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 2)) j)) ih)
    (Nat.sub (Nat.mul (nat_lit 2) k) (nat_lit 1)) x

@[expose] noncomputable def bswapN (S n a b R x : Nat) : Nat :=
  dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) b) (Nat.shiftLeft (nat_lit 1) a))
    (repN S n (Nat.land R (Nat.land (idPlane S a) (clrN S b)))) x

@[expose] noncomputable def revN (S n lo w R x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun k ih y => ih (strictN (bswapN S n (Nat.add lo k) (Nat.sub (Nat.add lo (Nat.sub w (nat_lit 1))) k) R y)
      (fun z => z)))
    (Nat.div w (nat_lit 2)) x

@[expose] noncomputable def rotrN (S n lo w r R x : Nat) : Nat :=
  revN S n (Nat.add lo (Nat.sub w r)) r R (revN S n lo (Nat.sub w r) R (revN S n lo w R x))

@[expose] noncomputable def qPl (b : Nat) : Nat := idPlane SX (Nat.add (nat_lit 10) b)

@[expose] noncomputable def qClr (b : Nat) : Nat := clrN SX (Nat.add (nat_lit 10) b)

@[expose] noncomputable def qPar : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun b acc => Nat.xor acc (qPl b)) (nat_lit 6)

@[expose] noncomputable def selRep (L s : Nat) : Nat :=
  Nat.shiftLeft (Nat.mul (Nat.land (Nat.shiftRight L (Nat.mul (nat_lit 1024) s)) (ones (nat_lit 1024)))
    (repU (nat_lit 1024) (nat_lit 64))) (nat_lit 65536)

@[expose] noncomputable def opJK (n u v M x : Nat) : Nat :=
  dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 9) v)) (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 9) u)))
    (repN SX n (Nat.land M (Nat.land (qPl (Nat.sub u (nat_lit 1))) (qClr (Nat.sub v (nat_lit 1)))))) x

@[expose] noncomputable def op0K (n v M x : Nat) : Nat :=
  dsw (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 9) v))
    (repN SX n (Nat.land M (Nat.land (qClr (Nat.sub v (nat_lit 1))) qPar))) x

@[expose] noncomputable def opJ7 (n u M x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun b ih y => ih (Bool.rec (motive := fun _ => Nat)
      (strictN (dsw (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 10) b))
        (repN SX n (Nat.land M (Nat.land (qClr b) (qPl (Nat.sub u (nat_lit 1)))))) y) (fun z => z))
      y (Nat.beq b (Nat.sub u (nat_lit 1)))))
    (nat_lit 6) x

@[expose] noncomputable def op07 (n M x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun y => y)
    (fun k ih y => ih ((fun a b => strictN
        (dsw (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 10) b)) (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 10) a)))
          (repN SX n (Nat.land M (Nat.land qPar (Nat.land (qPl a) (qClr b)))))
          (dsw (Nat.add (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 10) a)) (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 10) b)))
            (repN SX n (Nat.land M (Nat.land qPar (Nat.land (qClr a) (qClr b))))) y)) (fun z => z))
      (Nat.mul (nat_lit 2) k) (Nat.add (Nat.mul (nat_lit 2) k) (nat_lit 1))))
    (nat_lit 3) x

@[expose] noncomputable def opT (n u v M x : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (opJK n u v M x) (op0K n v M x) (Nat.beq u (nat_lit 0)))
    (Bool.rec (motive := fun _ => Nat) (opJ7 n u M x) (op07 n M x) (Nat.beq u (nat_lit 0)))
    (Nat.beq v (nat_lit 7))

@[expose] noncomputable def slotUV (s : Nat) : Nat :=
  fld(nat_lit 0x1f160d042f260b02372513012f260b021f160d04, Nat.mul (nat_lit 8) s, nat_lit 255)

@[expose] noncomputable def octSlots (n : Nat) (E : MonoE) (x : Nat) : Nat :=
  (fun y => Nat.rec (motive := fun _ => Nat → Nat) (fun z => z)
      (fun b ih z => ih (strictN (dsw (Nat.shiftLeft (nat_lit 1) (Nat.add (nat_lit 10) b))
        (repN SX n (Nat.land (selRep E.xsel b) (qClr b))) z) (fun w => w)))
      (nat_lit 6) y)
    (Nat.rec (motive := fun _ => Nat → Nat) (fun z => z)
      (fun s ih z => strictN (ih z) (fun w =>
        (fun uv => opT n (Nat.div uv (nat_lit 8)) (Nat.mod uv (nat_lit 8)) (selRep E.sel s) w) (slotUV s)))
      (nat_lit 20) x)

@[expose] noncomputable def repLow (S k : Nat) : Nat :=
  repU (Nat.shiftLeft (nat_lit 1) k) (Nat.div S (Nat.shiftLeft (nat_lit 1) k))

@[expose] noncomputable def amapN (n cn x : Nat) : Nat :=
  transpN n (netRepN SA n (nat_lit 5) (repLow SA (nat_lit 5)) (ones SA) cn
    (transpN n (netRepN SA n (nat_lit 5) (repLow SA (nat_lit 5)) (ones SA) cn x)))

@[expose] noncomputable def pairBlocks : Nat := Nat.shiftLeft (ones (nat_lit 2048)) (nat_lit 114688)

@[expose] noncomputable def monoOdd (n : Nat) (E : MonoE) (X : Nat) : Nat :=
  rotrN SX n (nat_lit 0) (nat_lit 16) (nat_lit 10) (idPlane SX (nat_lit 16))
    (netRepN SX n (nat_lit 10) (repLow SX (nat_lit 10)) (idPlane SX (nat_lit 16)) E.qn
      (octSlots n E (rotrN SX n (nat_lit 0) (nat_lit 16) (nat_lit 6) (idPlane SX (nat_lit 16))
        (rotrN SX n (nat_lit 0) (nat_lit 16) (nat_lit 11) lo16
          (netRepN SX n (nat_lit 11) (repLow SX (nat_lit 11)) lo16 E.on
            (rotrN SX n (nat_lit 0) (nat_lit 16) (nat_lit 5) lo16
              (netRepN SX n (nat_lit 5) (repLow SX (nat_lit 5)) lo16 E.cn
                (Nat.land X (Nat.xor (mN SX n) (repN SX n pairBlocks))))))))))

@[expose] noncomputable def monoPair (n : Nat) (E : MonoE) (o X : Nat) : Nat :=
  (fun P => amapN n E.cn (Nat.lor P (transpN n P))) (Nat.land (compactN n o X) (repN SA n upA))

@[expose] noncomputable def pairsBack (n psw P0 P1 : Nat) : Nat :=
  Nat.lor
    (expandN n (nat_lit 114688) (Nat.land (Nat.lor (Nat.land P0 (repN SA n (Nat.xor (ones SA) psw)))
      (Nat.land P1 (repN SA n psw))) (repN SA n upA)))
    (expandN n (nat_lit 115712) (Nat.land (Nat.lor (Nat.land P1 (repN SA n (Nat.xor (ones SA) psw)))
      (Nat.land P0 (repN SA n psw))) (repN SA n upA)))

@[expose] noncomputable def monoW (n : Nat) (E : MonoE) (W : Nat) : Nat :=
  rotrN SX n (nat_lit 0) (nat_lit 17) (nat_lit 12) (ones SX)
    (netRepN SX n (nat_lit 12) (repLow SX (nat_lit 12)) (ones SX) E.wn
      (rotrN SX n (nat_lit 0) (nat_lit 17) (nat_lit 5) (ones SX)
        (netRepN SX n (nat_lit 5) (repLow SX (nat_lit 5)) (ones SX) E.cn W)))

@[expose] noncomputable def monoStepN (n : Nat) (E : MonoE) (X A W : Nat) : Nat × Nat × Nat :=
  (fun X1 => (Nat.lor (monoOdd n E X1)
      (pairsBack n E.psw (monoPair n E (nat_lit 114688) X1) (monoPair n E (nat_lit 115712) X1)),
    amapN n E.cn (negMN SA n E.sgA A), monoW n E (negMN SX n E.sgW W)))
    (negMN SX n E.sgX X)

end CFSG.KC.KDenseP

end
