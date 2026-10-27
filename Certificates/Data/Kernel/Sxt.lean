module

public import Certificates.Data.Kernel.Compat

public section

namespace CFSG.KC.Sxt

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.W CFSG.KC.LQT.Syl CFSG.KC.LQT.S CFSG.KC.Sym6Sq
  CFSG.KC.Compat

@[expose] noncomputable def nrmK (E : List Nat) (g gi : Nat) : Bool :=
  allL E fun x => andB (memI E 64 (cjK g x gi)) (memI E 64 (cjK gi x g))

@[expose] noncomputable def fxoK (E : List Nat) : Bool :=
  allN 24 fun x => allN 24 fun q =>
    impB (allL E fun k => impB (Nat.beq (img k x) x) (Nat.beq (img k q) q))
      (anyL E fun f => Nat.beq (img f x) q)

@[expose] noncomputable def stepK (GS GIS l : List Nat) (p i : Nat) : List Nat :=
  Bool.rec (motive := fun _ => List Nat) l
    (strictA (cjK (getK GS i 0) (getK l p 0) (getK GIS i 0)) fun c => l ++ [c])
    (andB (Nat.blt p (lenK l)) (Nat.blt i (lenK GS)))

@[expose] noncomputable def reachK (GS GIS : List Nat) (w : List (Nat × Nat)) (l : List Nat) :
    List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun l => l)
    (fun pi _ ih l => forceA (Prod.rec (motive := fun _ => List Nat)
      (fun p i => stepK GS GIS l p i) pi) ih) w l

@[expose] noncomputable def orbK (E GS GIS : List Nat) (a f : Nat) (w : List (Nat × Nat)) : Bool :=
  andB (memI E 64 a) (andB (notB (Nat.beq a (one 24)))
    (forceA (reachK GS GIS w [a]) fun R =>
      allL E fun s => impB (andB (notB (Nat.beq s (one 24))) (Nat.beq (fix 24 s) f)) (memL s R)))

@[expose] noncomputable def clsN (E : List Nat) (f : Nat) : Nat :=
  cntK E fun s => andB (notB (Nat.beq s (one 24))) (Nat.beq (fix 24 s) f)

@[expose] noncomputable def fiveK (E : List Nat) (r ri : Nat) (Q R4 : List Nat) : Bool :=
  andB (nrmK E r ri) (andB (notB (Nat.beq r (one 24)))
  (andB (Nat.beq (pow 24 r 5) (one 24))
  (andB (Nat.beq (cntK E fun x => Nat.beq (cjK r x ri) x) (nat_lit 4))
  (andB (nodupK Q) (andB (memI Q 16 (one 24))
  (andB (allL Q fun x => allL Q fun y => memI Q 16 (mul 24 x y))
    (allL Q fun q => strictA (inv 24 q) fun qi =>
      andB (nrmK E q qi) (memI R4 4 (cjK q r qi)))))))))

@[expose] noncomputable def sxtB (E GS GIS : List Nat) (a1 a2 f1 f2 r ri : Nat)
    (w1 w2 : List (Nat × Nat)) (Q R4 : List Nat) : Bool :=
  andB (fxoK E) (andB (allL GS fun g => strictA (inv 24 g) fun gi => nrmK E g gi)
  (andB (orbK E GS GIS a1 f1 w1) (andB (orbK E GS GIS a2 f2 w2)
  (andB (Nat.beq (clsN E f1) (nat_lit 45)) (andB (Nat.beq (clsN E f2) (nat_lit 18))
  (andB (notB (Nat.beq f1 f2))
  (andB (allL E fun s => impB (notB (Nat.beq s (one 24)))
      (orB (Nat.beq (fix 24 s) f1) (Nat.beq (fix 24 s) f2)))
    (fiveK E r ri Q R4))))))))

@[expose] noncomputable def sxtK (G : List Nat) (rgw bw gw : List (List Int)) (rwd : List Int)
    (qgw qws : List (List Int)) (w1 w2 : List (Nat × Nat)) : Bool :=
  forceA (lstK 24 6 (rlGK 24 G rgw bw)) fun E =>
  forceA (gw.map (evalZK 24 G)) fun GS =>
  forceA (GS.map (inv 24)) fun GIS =>
  strictA (getK E 1 (one 24)) fun a1 => strictA (getK E 22 (one 24)) fun a2 =>
  strictA (fix 24 a1) fun f1 => strictA (fix 24 a2) fun f2 =>
  strictA (evalZK 24 G rwd) fun r => strictA (inv 24 r) fun ri =>
  forceA (rlGK 24 G qgw qws) fun Q =>
  forceA [r, pow 24 r 2, pow 24 r 3, pow 24 r 4] fun R4 =>
    sxtB E GS GIS a1 a2 f1 f2 r ri w1 w2 Q R4

end CFSG.KC.Sxt

end
