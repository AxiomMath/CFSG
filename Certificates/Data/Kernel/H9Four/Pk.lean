module

public import Certificates.Data.Kernel.Misc.G24

public section

namespace CFSG.KC.H9Four

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.G24

@[expose] noncomputable def mul4 (a b : Nat) : Nat := mulF2 (nat_lit 4) a b

@[expose] noncomputable def one4 : Nat := nat_lit 33825

@[expose] noncomputable def tr4 (x : Nat) : Nat :=
  letN (Nat.land (Nat.xor x (Nat.shiftRight x (nat_lit 3))) (nat_lit 2570)) fun t =>
  letN (Nat.xor x (Nat.xor t (Nat.shiftLeft t (nat_lit 3)))) fun y =>
  letN (Nat.land (Nat.xor y (Nat.shiftRight y (nat_lit 6))) (nat_lit 204)) fun u =>
  Nat.xor y (Nat.xor u (Nat.shiftLeft u (nat_lit 6)))

@[expose] noncomputable def colV (v : Nat) : Nat :=
  Nat.lor (Nat.lor (bit v (nat_lit 0)) (Nat.shiftLeft (bit v (nat_lit 1)) (nat_lit 4)))
    (Nat.lor (Nat.shiftLeft (bit v (nat_lit 2)) (nat_lit 8))
      (Nat.shiftLeft (bit v (nat_lit 3)) (nat_lit 12)))

@[expose] noncomputable def gather (z : Nat) : Nat :=
  Nat.lor (Nat.lor (bit z (nat_lit 0)) (Nat.shiftLeft (bit z (nat_lit 4)) (nat_lit 1)))
    (Nat.lor (Nat.shiftLeft (bit z (nat_lit 8)) (nat_lit 2))
      (Nat.shiftLeft (bit z (nat_lit 12)) (nat_lit 3)))

@[expose] noncomputable def mkE (a ai b : Nat) : Nat :=
  Nat.lor a (Nat.lor (Nat.shiftLeft ai (nat_lit 16)) (Nat.shiftLeft b (nat_lit 32)))

@[expose] noncomputable def fa (t : Nat) : Nat := Nat.land t (nat_lit 65535)

@[expose] noncomputable def fai (t : Nat) : Nat :=
  Nat.land (Nat.shiftRight t (nat_lit 16)) (nat_lit 65535)

@[expose] noncomputable def fb (t : Nat) : Nat := Nat.land (Nat.shiftRight t (nat_lit 32)) (nat_lit 1)

@[expose] noncomputable def oneE : Nat := nat_lit 2216789025

@[expose] noncomputable def mulE (s t : Nat) : Nat :=
  letN (fa s) fun a => letN (fai s) fun ai => letN (fa t) fun a2 => letN (fai t) fun ai2 =>
  Bool.rec (motive := fun _ => Nat)
    (mkE (mul4 a a2) (mul4 ai2 ai) (fb t))
    (mkE (mul4 a (tr4 ai2)) (mul4 (tr4 a2) ai) (Nat.xor (nat_lit 1) (fb t)))
    (Nat.beq (fb s) (nat_lit 1))

@[expose] noncomputable def aMul (s t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (mul4 (fa s) (fa t)) (mul4 (fa s) (tr4 (fai t)))
    (Nat.beq (fb s) (nat_lit 1))

@[expose] noncomputable def commE (s t : Nat) : Bool := Nat.beq (aMul s t) (aMul t s)

@[expose] noncomputable def invE (t : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (mkE (fai t) (fa t) (nat_lit 0))
    (mkE (tr4 (fa t)) (tr4 (fai t)) (nat_lit 1)) (Nat.beq (fb t) (nat_lit 1))

@[expose] noncomputable def validE (t : Nat) : Bool :=
  andB (Nat.beq (mul4 (fa t) (fai t)) one4) (Nat.beq (mul4 (fai t) (fa t)) one4)

@[expose] noncomputable def invoE (t : Nat) : Bool :=
  andB (validE t) (andB (Nat.beq (mulE t t) oneE) (notB (Nat.beq t oneE)))

@[expose] noncomputable def appL (a b : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) b (fun x _ ih => List.cons x ih) a

@[expose] noncomputable def mapL (g : Nat → Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun x _ ih => List.cons (g x) ih) l

@[expose] noncomputable def elemsK (G : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons oneE List.nil)
    (fun g _ E => appL E (mapL (mulE g) E)) G

@[expose] noncomputable def actK (t w : Nat) : Nat :=
  letN (Nat.land w (nat_lit 15)) fun x =>
  letN (Nat.land (Nat.shiftRight w (nat_lit 4)) (nat_lit 15)) fun y =>
  Bool.rec (motive := fun _ => Nat)
    (Nat.lor (gather (mul4 (fa t) (colV x)))
      (Nat.shiftLeft (Nat.land (mul4 y (fai t)) (nat_lit 15)) (nat_lit 4)))
    (Nat.lor (gather (mul4 (fa t) (colV y)))
      (Nat.shiftLeft (Nat.land (mul4 x (fai t)) (nat_lit 15)) (nat_lit 4)))
    (Nat.beq (fb t) (nat_lit 1))

@[expose] noncomputable def fullM : Nat :=
  Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 256)) (nat_lit 1)

@[expose] noncomputable def plane (s : Nat) : Nat :=
  letN (Nat.shiftLeft (nat_lit 1) s) fun h =>
  Nat.mul (Nat.div fullM (Nat.sub (Nat.shiftLeft (nat_lit 1) (Nat.add h h)) (nat_lit 1)))
    (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) h) (nat_lit 1)) h)

@[expose] noncomputable def rowP (row off : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun s acc => Nat.xor acc (Nat.mul (bit row s) (plane (Nat.add s off)))) (nat_lit 4)

@[expose] noncomputable def colOf (c i : Nat) : Nat :=
  Nat.lor (Nat.lor (bit c i) (Nat.shiftLeft (bit c (Nat.add i (nat_lit 4))) (nat_lit 1)))
    (Nat.lor (Nat.shiftLeft (bit c (Nat.add i (nat_lit 8))) (nat_lit 2))
      (Nat.shiftLeft (bit c (Nat.add i (nat_lit 12))) (nat_lit 3)))

@[expose] noncomputable def fixK (t : Nat) : Nat :=
  letN (Nat.mul (nat_lit 4) (fb t)) fun o1 => letN (Nat.sub (nat_lit 4) o1) fun o2 =>
  letN (fa t) fun a => letN (fai t) fun ai =>
  Nat.xor fullM (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun r acc => Nat.lor acc (Nat.lor
      (Nat.xor (plane r) (rowP (Nat.land (Nat.shiftRight a (Nat.mul (nat_lit 4) r)) (nat_lit 15)) o1))
      (Nat.xor (plane (Nat.add r (nat_lit 4))) (rowP (colOf ai r) o2)))) (nat_lit 4))

@[expose] noncomputable def pop256 (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun w acc => Nat.add acc (bit m w)) (nat_lit 256)

@[expose] noncomputable def pop1 (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun w acc => Nat.add acc (bit m w)) (nat_lit 16)

@[expose] noncomputable def pop2 (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun y acc => Nat.add acc (bit m (Nat.mul (nat_lit 16) y))) (nat_lit 16)

@[expose] noncomputable def w1M : Nat := nat_lit 65535

@[expose] noncomputable def w2M : Nat :=
  Nat.div fullM (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 16)) (nat_lit 1))

@[expose] noncomputable def bfly (s S : Nat) : Nat :=
  letN (Nat.xor fullM (plane s)) fun lo => letN (Nat.shiftLeft (nat_lit 1) s) fun h =>
  Nat.lor (Nat.shiftLeft (Nat.land S lo) h) (Nat.land (Nat.shiftRight S h) lo)

@[expose] noncomputable def translK (S v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) S
    (fun s T => Bool.rec (motive := fun _ => Nat) T (bfly s T) (Nat.beq (bit v s) (nat_lit 1)))
    (nat_lit 8)

@[expose] noncomputable def insV (S v : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (Nat.lor S (translK S v)) S (Nat.beq (bit S v) (nat_lit 1))

@[expose] noncomputable def spanM (U : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun w S => Bool.rec (motive := fun _ => Nat) S (insV S w) (Nat.beq (bit U w) (nat_lit 1)))
    (nat_lit 256)

@[expose] noncomputable def eltX (v : Nat) : Nat :=
  Nat.land v (nat_lit 17179869183)

@[expose] noncomputable def maskX (v : Nat) : Nat := Nat.shiftRight v (nat_lit 34)

@[expose] noncomputable def spanCols (X : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 1)
    (fun v _ S => letN (eltX v) fun t => Nat.rec (motive := fun _ => Nat) S
      (fun k S2 => letN (Nat.shiftLeft (nat_lit 1) k) fun e =>
        insV S2 (Nat.xor (actK t e) e)) (nat_lit 8)) X

@[expose] noncomputable def memX (x : Nat) (X : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun v _ ih => orB (Nat.beq x (eltX v)) ih) X

@[expose] noncomputable def lenK (X : List Nat) : Nat := lenN X

@[expose] noncomputable def nthK (L : List (List Nat)) (i : Nat) : List Nat := nthL L i

@[expose] noncomputable def eqLL (A B : List (List Nat)) : Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun B => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) B)
    (fun x _ ih B => List.rec (motive := fun _ => Bool) false
      (fun y t _ => andB (eqLN x y) (ih t)) B) A B

@[expose] noncomputable def lenLL (L : List (List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def invAllK (L : List Nat) (S : List (Nat × Nat)) : List Nat :=
  appL (mapL (fun k => mkE k k (nat_lit 0)) L)
    (List.rec (motive := fun _ => List Nat) List.nil
      (fun p _ ih => List.cons (Prod.rec (motive := fun _ => Nat)
        (fun a ai => mkE a ai (nat_lit 1)) p) ih) S)

@[expose] noncomputable def checkInvK (L : List Nat) (S : List (Nat × Nat)) : Bool :=
  andB (allL L fun k => andB (Nat.blt k (nat_lit 65536))
    (andB (Nat.beq (mul4 k k) one4) (notB (Nat.beq k one4))))
    (List.rec (motive := fun _ => Bool) true (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool)
      (fun a ai => andB (andB (Nat.blt a (nat_lit 65536)) (Nat.blt ai (nat_lit 65536)))
        (andB (andB (Nat.beq (mul4 a ai) one4) (Nat.beq (mul4 ai a) one4))
          (andB (Nat.beq (mul4 a (tr4 ai)) one4) (Nat.beq (mul4 (tr4 a) ai) one4)))) p) ih) S)

@[expose] noncomputable def memS (k : Nat) (S : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun p _ ih => orB (Prod.rec (motive := fun _ => Bool) (fun a _ => Nat.beq k a) p) ih) S

@[expose] noncomputable def kerV (k : Nat) : Bool :=
  anyN (nat_lit 16) fun v => andB (Nat.blt (nat_lit 0) v) (Nat.beq (mul4 k (colV v)) (nat_lit 0))

@[expose] noncomputable def stepK (L : List Nat) (S : List (Nat × Nat)) (k : Nat) : Bool :=
  andB (impB (andB (Nat.beq (mul4 k k) one4) (notB (Nat.beq k one4))) (memN k L))
    (impB (Nat.beq (tr4 k) k) (orB (memS k S) (kerV k)))

@[expose] noncomputable def walkK (L : List Nat) (S : List (Nat × Nat)) (base len : Nat) : Bool :=
  allN len fun i => letB (Nat.add base i) (stepK L S)

@[expose] noncomputable def gensK (gs : List (Nat × Nat × Bool)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun p _ ih => List.cons (Prod.rec (motive := fun _ => Nat) (fun a q =>
      Prod.rec (motive := fun _ => Nat) (fun ai b =>
        mkE a ai (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) b)) q) p) ih) gs

@[expose] noncomputable def canonK (gs : List (Nat × Nat × Bool)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) (fun a q =>
      Prod.rec (motive := fun _ => Bool) (fun ai _ =>
        andB (Nat.blt a (nat_lit 65536)) (Nat.blt ai (nat_lit 65536))) q) p) ih) gs

@[expose] noncomputable def repsK (R : List (List (Nat × Nat × Bool))) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) List.nil
    (fun gs _ ih => List.cons (gensK gs) ih) R

@[expose] noncomputable def canonR (R : List (List (Nat × Nat × Bool))) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun gs _ ih => andB (canonK gs) ih) R

@[expose] noncomputable def repOK (G X : List Nat) : Bool :=
  andB (allL G invoE) <|
  andB (allL G fun g => allL G fun h => Nat.beq (mulE g h) (mulE h g)) <|
  andB (eqLN (mapL eltX X) (elemsK G)) <|
  andB (nodupN (mapL eltX X)) (allL X fun v => Nat.beq (maskX v) (fixK (eltX v)))

@[expose] noncomputable def pinK (R : List (List (Nat × Nat × Bool))) (RG RX : List (List Nat)) :
    Bool :=
  andB (canonR R) <| andB (eqLL RG (repsK R)) <| andB (Nat.beq (lenLL RX) (lenLL RG)) <|
    allN (lenLL RG) fun i => repOK (nthK RG i) (nthK RX i)

@[expose] noncomputable def entK (G X : List Nat) (RX : List (List Nat)) (x ent : Nat) : Bool :=
  letB (Nat.land ent (nat_lit 255)) fun j => letB (Nat.shiftRight ent (nat_lit 8)) fun c =>
  letB (invE c) fun ci =>
  andB (validE c) <| andB (Nat.beq (lenK (nthK RX j)) (Nat.mul (nat_lit 2) (lenK X))) <|
    allL (List.cons x G) fun g => memX (mulE (mulE c g) ci) (nthK RX j)

@[expose] noncomputable def liveK (G X : List Nat) (x : Nat) : Bool :=
  andB (allL G (commE x)) (notB (memX x X))

@[expose] noncomputable def closRowK (G X : List Nat) (RX : List (List Nat)) (I T : List Nat) :
    Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun T => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) T)
    (fun x _ ih T => Bool.rec (motive := fun _ => Bool) (ih T)
      (List.rec (motive := fun _ => Bool) false (fun ent rest _ => andB (entK G X RX x ent) (ih rest))
        T)
      (liveK G X x)) I T

@[expose] noncomputable def fixAllK (G : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) fullM (fun g _ ih => Nat.land (fixK g) ih) G

@[expose] noncomputable def inLK (G : List Nat) : Bool := allL G fun g => Nat.beq (fb g) (nat_lit 0)

@[expose] noncomputable def rankK (RG : List (List Nat)) : Bool :=
  allLL RG fun G => Nat.ble (lenN G) (nat_lit 4)

@[expose] noncomputable def ffK (G X : List Nat) : Bool :=
  orB (Nat.beq (lenN G) (nat_lit 0)) <|
    orB (Nat.blt (Nat.mul (lenK X) (pop256 (fixAllK G))) (nat_lit 256))
      (andB (inLK G) (Nat.beq (lenK X) (nat_lit 16)))

@[expose] noncomputable def commK (X : List Nat) : Bool :=
  orB (Nat.blt (lenK X) (nat_lit 4)) (Nat.ble (nat_lit 8) (pop256 (spanCols X)))

@[expose] noncomputable def centK (G X : List Nat) : Bool :=
  orB (Nat.blt (lenK X) (nat_lit 4))
    (Nat.blt (Nat.mul (nat_lit 4) (pop256 (fixAllK G))) (nat_lit 256))

@[expose] noncomputable def constFixK (X : List Nat) : Bool :=
  allL X fun v => allL X fun u => orB (Nat.beq (eltX v) oneE) <| orB (Nat.beq (eltX u) oneE) <|
    andB (Nat.beq (Nat.land (maskX v) w1M) (Nat.land (maskX u) w1M))
      (Nat.beq (Nat.land (maskX v) w2M) (Nat.land (maskX u) w2M))

@[expose] noncomputable def axesK (G X : List Nat) : Bool :=
  orB (notB (inLK G)) <| orB (Nat.blt (lenK X) (nat_lit 4)) <| orB (notB (constFixK X)) <|
    andB (Nat.beq (lenK X) (nat_lit 4)) (allL X fun v => orB (Nat.beq (eltX v) oneE)
      (andB (Nat.beq (pop1 (maskX v)) (nat_lit 4)) (Nat.beq (pop2 (maskX v)) (nat_lit 4))))

@[expose] noncomputable def invarK (RG RX : List (List Nat)) : Bool :=
  allN (lenLL RG) fun i =>
    andB (andB (ffK (nthK RG i) (nthK RX i)) (commK (nthK RX i)))
      (andB (centK (nthK RG i) (nthK RX i)) (axesK (nthK RG i) (nthK RX i)))

@[expose] noncomputable def gam2K (X : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun v _ acc => Nat.lor acc
    (List.rec (motive := fun _ => Nat) (nat_lit 0) (fun u _ acc2 => Nat.lor acc2
      (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (Nat.land (maskX v) (maskX u))
        (andB (notB (Nat.beq (eltX v) oneE))
          (andB (notB (Nat.beq (eltX u) oneE)) (notB (Nat.beq (eltX v) (eltX u))))))) X)) X

@[expose] noncomputable def gam3K (X : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun v _ acc => Nat.lor acc
    (Bool.rec (motive := fun _ => Nat) (maskX v) (nat_lit 0) (Nat.beq (eltX v) oneE))) X

@[expose] noncomputable def e16PairK (X : List Nat) : Bool :=
  andB (anyL X fun v => andB (Nat.beq (fb (eltX v)) (nat_lit 0)) (Nat.beq (pop1 (maskX v)) (nat_lit 8)))
    (andB (anyL X fun v => andB (andB (Nat.beq (fb (eltX v)) (nat_lit 0))
        (notB (Nat.beq (eltX v) oneE))) (notB (Nat.beq (pop1 (maskX v)) (nat_lit 8))))
      (Nat.ble (nat_lit 128) (pop256 (spanM (gam3K X)))))

@[expose] noncomputable def e16K (G0 X0 G1 X1 G2 X2 : List Nat) : Bool :=
  letB (spanM (gam2K X2)) fun S2 =>
  andB (andB (Nat.beq (pop256 (fixAllK G0)) (nat_lit 16))
      (Nat.beq (pop256 (spanM (gam2K X0))) (nat_lit 256))) <|
  andB (andB (Nat.beq (pop256 (fixAllK G1)) (nat_lit 2))
      (Nat.beq (pop256 (spanM (gam2K X1))) (nat_lit 64))) <|
  andB (andB (Nat.beq (pop256 (fixAllK G2)) (nat_lit 4)) (Nat.beq (pop256 S2) (nat_lit 64))) <|
  andB (allL X2 fun v => orB (Nat.beq (eltX v) oneE)
      (Nat.blt (nat_lit 0) (Nat.land S2 (Nat.xor fullM (maskX v))))) <|
    andB (e16PairK X1) (e16PairK X2)

end CFSG.KC.H9Four

end
