module

public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.GHFus

open CFSG.KC.Enum

@[expose] noncomputable def addV (x y : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.xor x y) (nat_lit 21))
    (Nat.land (Nat.xor (Nat.xor x y) (Nat.shiftLeft (Nat.land (Nat.land x y) (nat_lit 21)) (nat_lit 1)))
      (nat_lit 42))

@[expose] noncomputable def mulK (dm mv a b : Nat) : Nat :=
  Nat.lor
    (Nat.shiftLeft (Nat.land (Nat.shiftRight dm
      (Nat.lor (Nat.shiftLeft (Nat.shiftRight a (nat_lit 6)) (nat_lit 5))
        (Nat.shiftLeft (Nat.shiftRight b (nat_lit 6)) (nat_lit 2)))) (nat_lit 7)) (nat_lit 6))
    (addV (Nat.land a (nat_lit 63))
      (Nat.land (Nat.shiftRight mv (Nat.shiftLeft
        (Nat.lor (Nat.land a (nat_lit 448)) (Nat.land b (nat_lit 63))) (nat_lit 3))) (nat_lit 63)))

@[expose] noncomputable def m87 : Nat := nat_lit 154742504910672534362390527

@[expose] noncomputable def lane (R P : Nat) : Nat :=
  Nat.land (Nat.shiftRight R (Nat.add (Nat.shiftLeft P (nat_lit 7)) (nat_lit 64))) m87

@[expose] noncomputable def nib (P k : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.shiftLeft k (nat_lit 2))) (nat_lit 15)

@[expose] noncomputable def clsK (CT c : Nat) : Nat :=
  Nat.land (Nat.shiftRight CT (Nat.shiftLeft c (nat_lit 2))) (nat_lit 15)

@[expose] noncomputable def evalFrom (dm mv Q acc : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun i _ ih acc => strictN (mulK dm mv acc (Nat.land (Nat.shiftRight Q i) (nat_lit 511))) ih)
    w acc

@[expose] noncomputable def evalWK (dm mv Q : Nat) (w : List Nat) : Nat := evalFrom dm mv Q (nat_lit 0) w

@[expose] noncomputable def okK (rel : Bool) (x : Nat) : Bool :=
  Bool.rec (Bool.not' (Nat.beq x (nat_lit 0))) (Nat.beq x (nat_lit 0)) rel

@[expose] noncomputable def isInvK (dm mv c : Nat) : Bool :=
  Bool.and' (Nat.beq (mulK dm mv c c) (nat_lit 0)) (Bool.not' (Nat.beq c (nat_lit 0)))

@[expose] noncomputable def patK (dm mv x y : Nat) : Nat :=
  strictN (mulK dm mv x y) fun p => strictN (mulK dm mv p p) fun p2 =>
    Nat.lor (Nat.lor (Bool.toNat (Nat.beq p (nat_lit 0)))
        (Nat.shiftLeft (Bool.toNat (Nat.beq p2 (nat_lit 0))) (nat_lit 1)))
      (Nat.lor (Nat.shiftLeft (Bool.toNat (Nat.beq (mulK dm mv p2 p2) (nat_lit 0))) (nat_lit 2))
        (Nat.shiftLeft (Bool.toNat (Nat.beq p (mulK dm mv y x))) (nat_lit 3)))

@[expose] noncomputable def rowK (dm mv x : Nat) (L : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun e _ ih j => Nat.lor (Prod.rec (motive := fun _ => Nat) (fun c _ =>
      Nat.shiftLeft (nat_lit 1) (Nat.add (Nat.add (Nat.shiftLeft (patK dm mv x c) (nat_lit 7))
        (nat_lit 64)) j)) e)
      (strictN (Nat.succ j) ih)) L (nat_lit 0)

@[expose] noncomputable def rowsOK (dm mv : Nat) (R L : List (Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun e _ ih => Bool.and'
    (Prod.rec (motive := fun _ => Bool) (fun c r =>
      Nat.beq (Nat.lor (rowK dm mv c L) (Nat.land r (nat_lit 18446744073709551615))) r) e) ih) R

@[expose] noncomputable def codeMask (L : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e _ ih => Nat.lor (Prod.rec (motive := fun _ => Nat) (fun c _ => Nat.shiftLeft (nat_lit 1) c) e) ih) L

@[expose] noncomputable def invsOK (dm mv : Nat) (L : List (Nat × Nat)) : Bool :=
  strictB (codeMask L) fun M =>
    Nat.rec (motive := fun _ => Bool) true (fun c ih => Bool.and'
      (Bool.or' (Bool.not' (isInvK dm mv c))
        (Nat.beq (Nat.land (Nat.shiftRight M c) (nat_lit 1)) (nat_lit 1))) ih) (nat_lit 512)

@[expose] noncomputable def badBK (dm mv CT BP Q : Nat) (IK : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun r _ ih => Bool.or' (Prod.rec (motive := fun _ => Bool) (fun c9 w =>
      Nat.beq (Nat.land (Nat.shiftRight BP (Nat.add c9 (clsK CT (evalWK dm mv Q w)))) (nat_lit 1))
        (nat_lit 1)) r) ih) IK

@[expose] noncomputable def predEK (c : Nat) : Bool :=
  Bool.and' (Nat.blt c (nat_lit 256)) (Nat.beq (Nat.land c (nat_lit 5)) (nat_lit 0))

@[expose] noncomputable def predFK (c : Nat) : Bool :=
  Bool.and' (Nat.blt c (nat_lit 256)) (Nat.beq (Nat.land c (nat_lit 5))
    (nib (nat_lit 5440) (Nat.shiftRight c (nat_lit 6))))

@[expose] noncomputable def diffK (dm mv Q : Nat) (pred : Nat → Bool) (EW : List (Nat × List Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun r _ ih => Bool.or' (Prod.rec (motive := fun _ => Bool) (fun e w =>
      Bool.rec (pred (evalWK dm mv Q w)) (Bool.not' (pred (evalWK dm mv Q w))) (pred e)) r) ih) EW

@[expose] noncomputable def outK (dm mv CT BP Q : Nat) (IK EW : List (Nat × List Nat)) (zw : List Nat)
    (uE uF : Bool) (good : Nat → Bool) : Bool :=
  Bool.or' (badBK dm mv CT BP Q IK)
    (Bool.or' (Bool.and' (Nat.beq (evalWK dm mv Q zw) (nat_lit 32))
        (Bool.or' (Bool.and' uE (diffK dm mv Q predEK EW)) (Bool.and' uF (diffK dm mv Q predFK EW))))
      (good Q))

abbrev Test := List Nat × List Nat × Bool

@[expose] noncomputable def pairOkK (x : Nat) (t : Test) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun _ sr => Prod.rec (motive := fun _ => Bool) (fun s rel =>
    List.rec (motive := fun _ => Bool) (okK rel x) (fun _ _ _ => true) s) sr) t

@[expose] noncomputable def triOkK (dm mv Q x : Nat) (t : Test) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun _ sr => Prod.rec (motive := fun _ => Bool) (fun s rel =>
    okK rel (evalFrom dm mv Q x s)) sr) t

@[expose] noncomputable def preK (t : Test) : List Nat :=
  Prod.rec (motive := fun _ => List Nat) (fun p _ => p) t

abbrev FusT := Nat × Nat × (Test × Test × Test) × List (Nat × List Nat) × Nat ×
  List (Nat × List Nat) × List Nat × Bool × Bool

@[expose] noncomputable def walkM (f : Nat → Nat → Bool) (L : List (Nat × Nat)) (m : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun e _ ih m => Bool.rec
      (Bool.rec (strictB (Nat.shiftRight m (nat_lit 1)) ih)
        (Bool.and' (Prod.rec (motive := fun _ => Bool) f e) (strictB (Nat.shiftRight m (nat_lit 1)) ih))
        (Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 1)))
      true (Nat.beq m (nat_lit 0))) L m

@[expose] noncomputable def walkR (f : Nat → Nat → Bool) (lo hi : Nat) (L : List (Nat × Nat))
    (m : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => true)
    (fun e _ ih j m => Bool.and'
      (Bool.or' (Bool.not' (Bool.and' (Nat.beq (Nat.land m (nat_lit 1)) (nat_lit 1))
          (Bool.and' (Nat.ble lo j) (Nat.blt j hi))))
        (Prod.rec (motive := fun _ => Bool) f e))
      (strictB (Nat.succ j) fun j' => strictB (Nat.shiftRight m (nat_lit 1)) (ih j'))) L (nat_lit 0) m

@[expose] noncomputable def stage3 (dm mv CT BP Qp x1 x2 x3 : Nat) (t1 t2 t3 : Test)
    (IK EW : List (Nat × List Nat)) (zw : List Nat) (uE uF : Bool) (good : Nat → Bool) (c3 _ : Nat) :
    Bool :=
  strictB (Nat.lor Qp (Nat.shiftLeft c3 (nat_lit 27))) fun Q =>
    Bool.or' (Bool.not' (Bool.and' (triOkK dm mv Q x1 t1)
        (Bool.and' (triOkK dm mv Q x2 t2) (triOkK dm mv Q x3 t3))))
      (outK dm mv CT BP Q IK EW zw uE uF good)

@[expose] noncomputable def stage2 (dm mv CT BP Qv A3 p23 : Nat) (L : List (Nat × Nat)) (t1 t2 t3 : Test)
    (IK EW : List (Nat × List Nat)) (zw : List Nat) (uE uF : Bool) (good : Nat → Bool) (c2 R2 : Nat) :
    Bool :=
  strictB (Nat.lor Qv (Nat.shiftLeft c2 (nat_lit 18))) fun Qp =>
  strictB (evalWK dm mv Qp (preK t1)) fun x1 =>
  strictB (evalWK dm mv Qp (preK t2)) fun x2 =>
  strictB (evalWK dm mv Qp (preK t3)) fun x3 =>
    Bool.or' (Bool.not' (Bool.and' (pairOkK x1 t1) (Bool.and' (pairOkK x2 t2) (pairOkK x3 t3))))
      (strictB (Nat.land A3 (lane R2 p23))
        (walkM (stage3 dm mv CT BP Qp x1 x2 x3 t1 t2 t3 IK EW zw uE uF good) L))

@[expose] noncomputable def stage1 (dm mv CT BP v Rv P : Nat) (L : List (Nat × Nat)) (t1 t2 t3 : Test)
    (IK EW : List (Nat × List Nat)) (zw : List Nat) (uE uF : Bool) (good : Nat → Bool) (c1 R1 : Nat) :
    Bool :=
  strictB (Nat.land (lane Rv (nib P (nat_lit 1))) (lane R1 (nib P (nat_lit 2)))) fun m2 =>
  strictB (Nat.land (lane Rv (nib P (nat_lit 3))) (lane R1 (nib P (nat_lit 4)))) fun A3 =>
    walkM (stage2 dm mv CT BP (Nat.lor v (Nat.shiftLeft c1 (nat_lit 9))) A3 (nib P (nat_lit 5)) L
      t1 t2 t3 IK EW zw uE uF good) L m2

@[expose] noncomputable def fusRange (dm mv CT : Nat) (L : List (Nat × Nat)) (D : FusT)
    (good : Nat → Bool) (lo hi : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun v r => Prod.rec (motive := fun _ => Bool) (fun P r =>
  Prod.rec (motive := fun _ => Bool) (fun T r => Prod.rec (motive := fun _ => Bool) (fun IK r =>
  Prod.rec (motive := fun _ => Bool) (fun BP r => Prod.rec (motive := fun _ => Bool) (fun EW r =>
  Prod.rec (motive := fun _ => Bool) (fun zw r => Prod.rec (motive := fun _ => Bool) (fun uE uF =>
  Prod.rec (motive := fun _ => Bool) (fun t1 t23 => Prod.rec (motive := fun _ => Bool) (fun t2 t3 =>
    strictB (rowK dm mv v L) fun Rv =>
      walkR (stage1 dm mv CT BP v Rv P L t1 t2 t3 IK EW zw uE uF good) lo hi L
        (lane Rv (nib P (nat_lit 0)))) t23) T) r) r) r) r) r) r) r) D

@[expose] noncomputable def goodNoneK (_ : Nat) : Bool := false

@[expose] noncomputable def goodFixZK (dm mv Q : Nat) : Bool :=
  Nat.beq (evalWK dm mv Q [nat_lit 9, nat_lit 18, nat_lit 9, nat_lit 18]) (nat_lit 32)

@[expose] noncomputable def goodClsTK (dm mv CT Q : Nat) : Bool :=
  Nat.beq (clsK CT (evalWK dm mv Q [nat_lit 9, nat_lit 18, nat_lit 9, nat_lit 18])) (nat_lit 1)

@[expose] noncomputable def hasEdgeK (dm mv CT Q i9 j : Nat) (IK : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun r _ ih => Bool.or' (Prod.rec (motive := fun _ => Bool) (fun c9 w =>
      Bool.and' (Nat.beq c9 i9) (Nat.beq (clsK CT (evalWK dm mv Q w)) j)) r) ih) IK

@[expose] noncomputable def goodAZK (dm mv CT : Nat) (IK : List (Nat × List Nat))
    (x : List Nat × List Nat × List Nat) (wit : List Nat) (Q : Nat) : Bool :=
  Bool.and' (hasEdgeK dm mv CT Q (nat_lit 9) (nat_lit 7) IK)
    (Bool.and' (hasEdgeK dm mv CT Q (nat_lit 63) (nat_lit 3) IK)
      (Bool.and' (hasEdgeK dm mv CT Q (nat_lit 45) (nat_lit 8) IK)
        (Prod.rec (motive := fun _ => Bool) (fun w26 r => Prod.rec (motive := fun _ => Bool) (fun w4 w2 =>
          strictB (evalWK dm mv Q w26) fun a => strictB (evalWK dm mv Q w4) fun b =>
          strictB (mulK dm mv b (evalWK dm mv Q w2)) fun bc =>
            List.rec (motive := fun _ => Bool) false (fun s _ ih => Bool.or'
              (Bool.and' (Nat.beq (mulK dm mv a s) (mulK dm mv s (nat_lit 8)))
                (Bool.or' (Nat.beq (mulK dm mv b s) (mulK dm mv s (nat_lit 68)))
                  (Nat.beq (mulK dm mv bc s) (mulK dm mv s (nat_lit 100))))) ih) wit) r) x)))

@[expose] noncomputable def a1K : List Nat :=
  [nat_lit 0, nat_lit 8, nat_lit 32, nat_lit 40, nat_lit 64, nat_lit 72, nat_lit 96, nat_lit 104,
    nat_lit 256, nat_lit 264, nat_lit 288, nat_lit 296, nat_lit 320, nat_lit 328, nat_lit 352, nat_lit 360]

@[expose] noncomputable def goodA34K (dm mv CT : Nat) (IK : List (Nat × List Nat))
    (x : List Nat × List Nat × List Nat × List Nat) (wit : List Nat) (Q : Nat) : Bool :=
  Bool.and' (Bool.or' (hasEdgeK dm mv CT Q (nat_lit 9) (nat_lit 0) IK)
      (hasEdgeK dm mv CT Q (nat_lit 0) (nat_lit 1) IK))
    (Bool.and' (Bool.or' (hasEdgeK dm mv CT Q (nat_lit 45) (nat_lit 8) IK)
        (hasEdgeK dm mv CT Q (nat_lit 72) (nat_lit 5) IK))
      (Prod.rec (motive := fun _ => Bool) (fun w26 r => Prod.rec (motive := fun _ => Bool) (fun w2 r =>
        Prod.rec (motive := fun _ => Bool) (fun w3 w4 =>
        Bool.and' (Nat.beq (clsK CT (evalWK dm mv Q w4)) (nat_lit 8))
          (strictB (evalWK dm mv Q w26) fun a => strictB (evalWK dm mv Q w2) fun b =>
           strictB (evalWK dm mv Q w3) fun c =>
            List.rec (motive := fun _ => Bool) false (fun s _ ih => Bool.or'
              (Bool.and' (Nat.beq (mulK dm mv s (nat_lit 64)) (mulK dm mv (nat_lit 64) s))
                (Bool.and' (Nat.beq (mulK dm mv a s) (mulK dm mv s (nat_lit 32)))
                  (Bool.and' (Bool.or' (Nat.beq (mulK dm mv b s) (mulK dm mv s (nat_lit 8)))
                      (Nat.beq (mulK dm mv b s) (mulK dm mv s (nat_lit 40))))
                    (List.rec (motive := fun _ => Bool) false (fun w _ ih' =>
                      Bool.or' (Nat.beq (mulK dm mv c s) (mulK dm mv s w)) ih') a1K)))) ih) wit)) r) r) x))

end CFSG.KC.GHFus
