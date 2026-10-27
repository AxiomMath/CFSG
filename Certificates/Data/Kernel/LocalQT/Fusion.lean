module

public import Certificates.Data.Kernel.LocalQT.Base

public section

namespace CFSG.KC.LQT.BC

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.LQT.S CFSG.KC.LQT.L

@[expose] noncomputable def kidsK (n x : Nat) (G : List Nat) :
    (NT → List Nat → Nat → Bool) → NT → List Nat → Nat → Bool :=
  List.rec (motive := fun _ => (NT → List Nat → Nat → Bool) → NT → List Nat → Nat → Bool)
    (fun k t R s => k t R s)
    (fun g _ ih k t R s => letB (mul n g x) fun c =>
      Bool.rec (motive := fun _ => Bool)
        (List.rec (motive := fun _ => Bool) false
          (fun r R' _ => andB (Nat.beq c r) (ih k (insT t c) R' (Nat.succ s))) R)
        (ih k t R s) (memT t c)) G

@[expose] noncomputable def bfsOrdK (n : Nat) (G L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun x0 R0 _ => andB (Nat.beq x0 (one n))
      (List.rec (motive := fun _ => NT → List Nat → Nat → Bool)
        (fun _ R _ => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) R)
        (fun x _ ih t R s => andB (Nat.blt 0 s) (kidsK n x G ih t R (Nat.sub s 1)))
        L (NT.nd NT.lf x0 NT.lf) R0 1)) L

@[expose] noncomputable def wordAB (n a b : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (one n)
    (fun x _ ih => mul n (Bool.rec (motive := fun _ => Nat) b a (Nat.beq x 0)) ih) w

@[expose] noncomputable def prodIdx (n : Nat) (L cs w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (one n)
    (fun p _ ih => mul n (getK L (getK cs p)) ih) w

@[expose] noncomputable def gwsK (n : Nat) (L cs G : List Nat) : List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool) (fun _ => true)
    (fun g _ ih gws => List.rec (motive := fun _ => Bool)
      (andB (Nat.beq (one n) g) (ih []))
      (fun w gws' _ => andB (Nat.beq (prodIdx n L cs w) g) (ih gws')) gws) G

@[expose] noncomputable def witK (n a b z : Nat) (L : List Nat)
    (wt : List Nat × List Nat × Nat) : Bool :=
  letB (wordAB n a b wt.1) fun g => letB (wordAB n a b wt.2.1) fun gi =>
    andB (Nat.blt wt.2.2 (lenA L)) (andB (Nat.beq (mul n gi g) (one n))
      (Nat.beq (mul n gi (mul n z g)) (getK L wt.2.2)))

@[expose] noncomputable def fusionQ (n a b : Nat) (G L : List Nat) (zi : Nat)
    (wits : List (List Nat × List Nat × Nat)) (gws : List (List Nat)) (fuel : Nat) : Bool :=
  andB (Nat.ble (lenA L) fuel) (andB (bfsOrdK n G L) (andB (Nat.blt zi (lenA L))
  (letB (getK L zi) fun z => allBs [
    notB (Nat.beq z (one n)), Nat.beq (mul n z z) (one n),
    allL G (fun g => Nat.beq (mul n g z) (mul n z g)),
    allL L (fun x => impB (allL G fun g => Nat.beq (mul n g x) (mul n x g))
      (orB (Nat.beq x (one n)) (Nat.beq x z))),
    allA wits (witK n a b z L),
    gwsK n L (List.rec (motive := fun _ => List Nat) [] (fun wt _ ih => List.cons wt.2.2 ih) wits)
      G gws])))

@[expose] noncomputable def fusionR (n a b : Nat) (R : List Nat) (qp : List (Nat × Nat))
    (L : List Nat) (zi : Nat) (wits : List (List Nat × List Nat × Nat)) (gws : List (List Nat))
    (fuel : Nat) : Bool :=
  andB (allA qp fun p => Nat.blt p.1 (lenA R))
    (fusionQ n a b (List.rec (motive := fun _ => List Nat) []
      (fun p _ ih => List.cons (nodeK R p.1) ih) qp) L zi wits gws fuel)

@[expose] noncomputable def fusionK (n : Nat) (ta tb : List Nat) (prog : List (Nat × Nat))
    (qp : List (Nat × Nat)) (L : List Nat) (zi : Nat) (wits : List (List Nat × List Nat × Nat))
    (gws : List (List Nat)) (fuel : Nat) : Bool :=
  andB (tabL n ta) (andB (tabL n tb) (andB (slpOKK prog 2)
    (letB (codeL ta) fun a => letB (codeL tb) fun b =>
      fusionR n a b (slpK n a b prog) qp L zi wits gws fuel)))

end CFSG.KC.LQT.BC

end
