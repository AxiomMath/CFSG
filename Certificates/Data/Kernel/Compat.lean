module

public import Certificates.Data.Kernel.QdOmega

public section

namespace CFSG.KC.Compat

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.LQT.S CFSG.KC.Sym6Sq

@[expose] noncomputable def memI (L : List Nat) (n x : Nat) : Bool := Nat.blt (idxK L x) n

@[expose] noncomputable def cjK (g x gi : Nat) : Nat := mul 24 (mul 24 g x) gi

@[expose] noncomputable def cmK (u x xi : Nat) : Nat := mul 24 u (mul 24 (mul 24 x (inv 24 u)) xi)

@[expose] noncomputable def cntK (L : List Nat) (f : Nat → Bool) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun x _ ih => Nat.add (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) (f x)) ih) L

@[expose] noncomputable def nodupK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x t ih => andB (notB (memL x t)) ih) L

@[expose] noncomputable def iffB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def cpRun (E B : List Nat) : Bool :=
  andB (allL E fun a => strictA (inv 24 a) fun ai => allL B fun b => memI B 16 (cjK a b ai))
  (andB (allL B fun b => strictA (inv 24 b) fun bi => allL E fun a => memI E 64 (cjK b a bi))
  (andB (Nat.beq (cntK E fun a => memI B 16 a) (nat_lit 4))
    (allL B fun x => impB (notB (memI E 64 x)) (strictA (inv 24 x) fun xi =>
      forceA (E.map fun a => cmK a x xi) fun C =>
        andB (allL C fun c => memI B 16 c)
          (allL B fun b => impB (memI E 64 b) (memI C 64 b))))))

@[expose] noncomputable def czRun (E B ZB Z : List Nat) : Bool :=
  andB (nodupK Z) (andB (memI Z 16 (one 24))
  (andB (allL Z fun x => allL Z fun y => memI Z 16 (mul 24 x y))
  (andB (allL Z fun x => memI E 64 x)
  (andB (allL Z fun x => impB (memI B 16 x) (Nat.beq x (one 24)))
  (andB (allL ZB fun z => memI Z 16 z)
    (allL ZB fun z => strictA (inv 24 z) fun zi => forceA (B.map fun b => cmK b z zi) fun C =>
      andB (allL C fun c => andB (memI E 64 c) (memI B 16 c))
        (allL B fun c => impB (memI E 64 c) (memI C 16 c))))))))

@[expose] noncomputable def cyRun (E B ZB Z : List Nat) (y yi : Nat) : Bool :=
  andB (allL B fun b => memI B 16 (cjK y b yi))
  (andB (allL Z fun z => memI Z 16 (cjK y z yi))
  (andB (Nat.beq (mul 24 (mul 24 y y) y) (one 24))
  (andB (allL B fun b => iffB (Nat.beq (cjK y b yi) b) (memI E 64 b))
    (forceA (Z.map fun x => cmK x y yi) fun C =>
      andB (allL C fun c => memI Z 16 c) (allL ZB fun z => memI C 16 z)))))

@[expose] noncomputable def zIdx : List Nat := [8, 4, 14, 9]

@[expose] noncomputable def compatK (G : List Nat) (rgw bw b0w : List (List Int)) (yw : List Int) :
    Bool :=
  forceA (lstK 24 6 (rlGK 24 G rgw bw)) fun E =>
  forceA (lstK 24 4 (b0w.map (evalZK 24 G))) fun B =>
  forceA (zIdx.map fun j => getK E j (one 24)) fun ZB =>
  forceA (lstK 24 4 ZB) fun Z =>
  strictA (evalZK 24 G yw) fun y => strictA (inv 24 y) fun yi =>
    andB (cpRun E B) (andB (czRun E B ZB Z) (cyRun E B ZB Z y yi))

end CFSG.KC.Compat

end
