module

public import Certificates.Data.Kernel.Misc.Base

public section

namespace CFSG.KC.Misc.Ext

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def bitK (x k : Nat) : Nat := Nat.land (Nat.shiftRight x k) (nat_lit 1)

@[expose] noncomputable def rowK (y k : Nat) : Nat :=
  Nat.land (Nat.shiftRight y (Nat.mul (nat_lit 3) k)) (nat_lit 7)

@[expose] noncomputable def prodRow (x y i : Nat) : Nat :=
  Nat.xor (Nat.mul (bitK x (Nat.mul (nat_lit 3) i)) (rowK y (nat_lit 0)))
    (Nat.xor (Nat.mul (bitK x (Nat.add (Nat.mul (nat_lit 3) i) (nat_lit 1))) (rowK y (nat_lit 1)))
      (Nat.mul (bitK x (Nat.add (Nat.mul (nat_lit 3) i) (nat_lit 2))) (rowK y (nat_lit 2))))

@[expose] noncomputable def mulK (x y : Nat) : Nat :=
  Nat.lor (prodRow x y (nat_lit 0)) (Nat.lor (Nat.shiftLeft (prodRow x y (nat_lit 1)) (nat_lit 3))
    (Nat.shiftLeft (prodRow x y (nat_lit 2)) (nat_lit 6)))

@[expose] noncomputable def pk (g X : Nat) : Nat := Nat.lor g (Nat.shiftLeft X (nat_lit 9))

@[expose] noncomputable def lo (p : Nat) : Nat := Nat.land p (nat_lit 511)

@[expose] noncomputable def hi (p : Nat) : Nat := Nat.shiftRight p (nat_lit 9)

@[expose] noncomputable def pmulK (p q : Nat) : Nat :=
  pk (mulK (lo p) (lo q)) (Nat.xor (mulK (lo p) (hi q)) (mulK (hi p) (lo q)))

@[expose] noncomputable def ppowK (p n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 273) (fun _ acc => pmulK acc p) n

@[expose] noncomputable def relAK (a x : Nat) : Bool :=
  Nat.beq (pmulK (pk a x) (pk a x)) (nat_lit 273)

@[expose] noncomputable def relBK (b y : Nat) : Bool :=
  Nat.beq (ppowK (pk b y) (nat_lit 3)) (nat_lit 273)

@[expose] noncomputable def relABK (a b x y : Nat) : Bool :=
  Nat.beq (ppowK (pmulK (pk a x) (pk b y)) (nat_lit 7)) (nat_lit 273)

@[expose] noncomputable def cobK (a b x y m : Nat) : Bool :=
  andB (Nat.beq x (Nat.xor (mulK a m) (mulK m a))) (Nat.beq y (Nat.xor (mulK b m) (mulK m b)))

@[expose] noncomputable def c3362 (a b : Nat) (XS YS T : List Nat) : Bool :=
  andB (andB (Nat.blt a (nat_lit 512)) (Nat.blt b (nat_lit 512)))
  (andB (allN (nat_lit 512) fun x => impB (relAK a x) (memN x XS))
  (andB (allN (nat_lit 512) fun y => impB (relBK b y) (memN y YS))
  (andB (allL T fun t => Nat.blt (Nat.shiftRight t (nat_lit 18)) (nat_lit 512))
    (allL XS fun x => allL YS fun y => impB (relABK a b x y)
      (anyL T fun t => andB (Nat.beq (Nat.land t (nat_lit 262143)) (pk x y))
        (cobK a b x y (Nat.shiftRight t (nat_lit 18))))))))

end CFSG.KC.Misc.Ext

end
