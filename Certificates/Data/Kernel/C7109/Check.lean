module

public import Init

public section

namespace CFSG.KC.C7109

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def eqB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) (notB b) b a

@[expose] noncomputable def impB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true b a

@[expose] noncomputable def letB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def letN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k 0) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def allN (n : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun i ih => andB (f i) ih) n

@[expose] noncomputable def bitB (x i : Nat) : Bool := Nat.blt 0 (Nat.land x (Nat.shiftLeft 1 i))

@[expose] noncomputable def fd (w x i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul w i)) (Nat.sub (Nat.shiftLeft 1 w) 1)

@[expose] noncomputable def rx (r : Nat) : Nat := Nat.land r 255
@[expose] noncomputable def rfix (r : Nat) : Nat := Nat.land (Nat.shiftRight r 8) 4294967295
@[expose] noncomputable def rfixT (r : Nat) : Nat := Nat.land (Nat.shiftRight r 40) 4294967295
@[expose] noncomputable def rM (r : Nat) : Nat := Nat.land (Nat.shiftRight r 72) 33554431
@[expose] noncomputable def rcm (r : Nat) : Nat := Nat.shiftRight r 97
@[expose] noncomputable def rrow (r : Nat) : Nat := Nat.shiftRight r 289
@[expose] noncomputable def rowAt (r y : Nat) : Nat := Nat.land (Nat.shiftRight (rrow r) (Nat.mul 8 y)) 255

@[expose] noncomputable def popT : Nat :=
  95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224

@[expose] noncomputable def pop32 (x : Nat) : Nat :=
  Nat.add (Nat.add (fd 4 popT (fd 8 x 0)) (fd 4 popT (fd 8 x 1)))
    (Nat.add (fd 4 popT (fd 8 x 2)) (fd 4 popT (fd 8 x 3)))

@[expose] noncomputable def mul25 (A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight A k) 1082401)
      (Nat.land (Nat.shiftRight B (Nat.mul 5 k)) 31))) 5

@[expose] noncomputable def tr25 (A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun t acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight A t) 1)
      (Nat.add (Nat.mul 5 (Nat.mod t 5)) (Nat.div t 5)))) 25

@[expose] noncomputable def symPos : Nat := 0
  + 0 + 1 * 32 + 2 * 1024 + 3 * 32768 + 4 * 1048576 + 6 * 33554432 + 7 * 1073741824
  + 8 * 34359738368 + 9 * 1099511627776 + 12 * 35184372088832 + 13 * 1125899906842624
  + 14 * 36028797018963968 + 18 * 1152921504606846976 + 19 * 36893488147419103232
  + 24 * 1180591620717411303424

@[expose] noncomputable def symIdx : Nat := 1177132112564295994695803482640

@[expose] noncomputable def symEnc25 (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight P (fd 5 symPos k)) 1) k)) 15

@[expose] noncomputable def symE (k : Nat) : Nat :=
  letN (fd 5 symPos k) fun p =>
    Nat.lor (Nat.shiftLeft 1 p) (Nat.shiftLeft 1 (Nat.add (Nat.mul 5 (Nat.mod p 5)) (Nat.div p 5)))

@[expose] noncomputable def img (M Mt k : Nat) : Nat := symEnc25 (mul25 (mul25 M (symE k)) Mt)

@[expose] noncomputable def W : Nat := 32768
@[expose] noncomputable def full : Nat := Nat.sub (Nat.shiftLeft 1 W) 1

@[expose] noncomputable def coord (k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (Nat.shiftLeft (Nat.sub (Nat.shiftLeft 1 (Nat.shiftLeft 1 k)) 1) (Nat.shiftLeft 1 k))
    (fun j acc => letN acc fun a =>
      Nat.lor a (Nat.shiftLeft a (Nat.shiftLeft 1 (Nat.add (Nat.add k 1) j))))
    (Nat.sub 14 k)

@[expose] noncomputable def planeOf (M : Nat) (j : Nat) : Nat :=
  letN (tr25 M) fun Mt =>
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (coord k))
      (bitB (img M Mt k) j)) 15

@[expose] noncomputable def ffG (M : Nat) : Nat :=
  Nat.xor full (Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => letN acc fun a => Nat.lor a (Nat.xor (planeOf M j) (coord j))) 15)

@[expose] noncomputable def rowZ (v i : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.xor acc (coord (fd 4 symIdx (Nat.add (Nat.mul 5 i) j)))) (bitB v j)) 5

@[expose] noncomputable def zMask (v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) full
    (fun i acc => letN acc fun a => Nat.land a (Nat.xor full (rowZ v i))) 5

@[expose] noncomputable def singMask : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun v acc => letN acc fun a => Nat.lor a (zMask (Nat.succ v))) 31

@[expose] noncomputable def ffS (B : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) full
    (fun r _ acc => letN acc fun a => Nat.land a (ffG (rM r))) B

@[expose] noncomputable def formOK (S : Nat) (B : List Nat) : Bool :=
  Nat.beq (Nat.land (ffS B) (Nat.xor full S)) 0

@[expose] noncomputable def nodeOK (S k f fT : Nat) (B : List Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (Bool.rec (motive := fun _ => Bool) true
      (letB (pop32 f) fun a => letB (pop32 fT) fun b =>
        Bool.rec (motive := fun _ => Bool) true (formOK S B) (Nat.beq a b))
      (Nat.beq k 4))
    (letB (pop32 f) fun a => letB (pop32 fT) fun b =>
      orB (andB (Nat.beq a 4) (Nat.beq b 8)) (andB (Nat.beq a 8) (Nat.beq b 4)))
    (orB (Nat.beq k 5) (Nat.beq k 6))

@[expose] noncomputable def canonZ (z : Nat) (nw : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun w _ ih => andB (Nat.blt (rx z) (rowAt z w)) ih) nw

@[expose] noncomputable def filterP (r Ym' : Nat) (nw rest : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun z _ ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons z ih)
      (andB (andB (bitB (rcm r) (rx z)) (notB (bitB Ym' (rx z)))) (canonZ z nw))) rest

@[expose] noncomputable def newOnly (r : Nat) (Yl : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons (rx r) List.nil)
    (fun y _ ih => List.cons (rowAt r y) ih) Yl

@[expose] noncomputable def newMask (r : Nat) (Yl : List Nat) (Ym : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (Nat.lor Ym (Nat.shiftLeft 1 (rx r)))
    (fun y _ ih => Nat.lor ih (Nat.shiftLeft 1 (rowAt r y))) Yl

@[expose] noncomputable def appendL (a b : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) b (fun x _ ih => List.cons x ih) a

@[expose] noncomputable def walkP (S : Nat) (fuel : Nat) :
    Nat → Nat → List Nat → Nat → Nat → List Nat → List Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → List Nat → Nat → Nat → List Nat → List Nat → Bool)
    (fun _ _ _ _ _ _ _ => false)
    (fun _ ih k Ym Yl f fT B cands => andB (nodeOK S k f fT B)
      (List.rec (motive := fun _ => Bool) true
        (fun r rest acc => andB
            (letB (newMask r Yl Ym) fun Ym' =>
              letB (Nat.land f (rfix r)) fun f' => letB (Nat.land fT (rfixT r)) fun fT' =>
                ih (Nat.succ k) Ym' (appendL (newOnly r Yl) Yl) f' fT' (List.cons r B)
                  (filterP r Ym' (newOnly r Yl) rest))
          acc) cands)) fuel

@[expose] noncomputable def repU : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 4775) 1) (Nat.sub (Nat.shiftLeft 1 25) 1)

@[expose] noncomputable def prodL (M MT : Nat) : Nat :=
  letN (Nat.mul 31 repU) fun m31 =>
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight M k) 1082401)
      (Nat.land (Nat.shiftRight MT (Nat.mul 5 k)) m31))) 5

@[expose] noncomputable def prodR (M MT : Nat) : Nat :=
  letN (Nat.mul 1082401 repU) fun m1 =>
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.xor acc (Nat.mul (Nat.land (Nat.shiftRight MT k) m1)
      (Nat.land (Nat.shiftRight M (Nat.mul 5 k)) 31))) 5

@[expose] noncomputable def fold25 (t : Nat) : Nat :=
  letN (Nat.lor t (Nat.shiftRight t 1)) fun a => letN (Nat.lor a (Nat.shiftRight a 2)) fun b =>
  letN (Nat.lor b (Nat.shiftRight b 4)) fun c => letN (Nat.lor c (Nat.shiftRight c 8)) fun d =>
  Nat.lor d (Nat.shiftRight d 9)

@[expose] noncomputable def mv (M v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight 2523490710
      (Nat.land (fd 5 M i) v)) 1) i)) 5

@[expose] noncomputable def vm (M v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc (Nat.xor acc (fd 5 M i)) (bitB v i)) 5

@[expose] noncomputable def recOK (MT r : Nat) : Bool :=
  letB (rM r) fun M => letB (rx r) fun x =>
  andB (andB (Nat.beq (fd 25 MT x) M)
    (andB (Nat.beq (Nat.land M 15961120) 0) (andB (Nat.beq (Nat.land M 17043521) 17043521)
      (andB (Nat.beq (mul25 M M) 17043521) (notB (Nat.beq M 17043521))))))
  (letB (prodL M MT) fun AB => letB (fold25 (Nat.xor AB (prodR M MT))) fun NZ =>
    andB (allN 191 fun z =>
      letB (Bool.rec (motive := fun _ => Nat) 0 1
        (andB (notB (bitB NZ (Nat.mul 25 z))) (notB (Nat.beq z x)))) fun c =>
      andB (eqB (bitB (rcm r) z) (Nat.beq c 1))
        (impB (Nat.beq c 1) (letB (rowAt r z) fun e =>
          andB (Nat.blt e 191) (Nat.beq (fd 25 MT e) (fd 25 AB z)))))
    (allN 32 fun v => andB (eqB (bitB (rfix r) v) (Nat.beq (mv M v) v))
      (eqB (bitB (rfixT r) v) (Nat.beq (vm M v) v))))

@[expose] noncomputable def recsFrom (MT : Nat) (RL : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i 191)
    (fun r _ ih i => andB (Nat.beq (rx r) i) (andB (recOK MT r) (ih (Nat.succ i)))) RL

@[expose] noncomputable def recsOK (MT : Nat) (RL : List Nat) : Bool := recsFrom MT RL 0

@[expose] noncomputable def upBits : Nat := 0 + 1 * 1 + 2 * 32 + 3 * 1024 + 4 * 32768 + 7 * 1048576
  + 8 * 33554432 + 9 * 1073741824 + 13 * 34359738368 + 14 * 1099511627776 + 19 * 35184372088832

@[expose] noncomputable def uni (c : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 17043521
    (fun k acc => Nat.lor acc (Nat.shiftLeft (Nat.land (Nat.shiftRight c k) 1) (fd 5 upBits k))) 10

@[expose] noncomputable def complOK (MT : Nat) : Bool :=
  allN 1024 fun c => letB (uni c) fun M =>
    orB (notB (Nat.beq (mul25 M M) 17043521)) (orB (Nat.beq M 17043521)
      (notB (Nat.beq (Nat.land (fold25 (Nat.xor MT (Nat.mul M repU))) repU) repU)))

end CFSG.KC.C7109

end
