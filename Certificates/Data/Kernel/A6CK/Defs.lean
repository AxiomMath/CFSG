module

public import Init

public section

namespace CFSG.KC.A6CK

@[expose] noncomputable def andB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) false b a

@[expose] noncomputable def orB (a b : Bool) : Bool := Bool.rec (motive := fun _ => Bool) b true a

@[expose] noncomputable def notB (a : Bool) : Bool := Bool.rec (motive := fun _ => Bool) true false a

@[expose] noncomputable def strictN (y : Nat) (k : Nat → Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def strictB (y : Nat) (k : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] def L1 : Nat :=
  2357752553686663413275543872507213904221338446006071722568470434335642990279740406315346638471097795286728961

@[expose] def L3 : Nat :=
  7073257661059990239826631617521641712664015338018215167705411303006928970839221218946039915413293385860186883

@[expose] def L63 : Nat :=
  148538410882259795036359263967954475965944322098382518521813637363145508387623645597866838223679161103063924543

@[expose] def COL : Nat :=
  544676694159832071040257517828751419058300915320685476433944354390887168148418989260845405857382655

@[expose] def ROW : Nat := 281474976710655

@[expose] def SP : Nat := 2305843009213693951

@[expose] noncomputable def encS (m : Nat) : Nat := Nat.lor (Nat.shiftLeft m 64) (Nat.mod m SP)

@[expose] def IDK : Nat :=
  43322963970637732180921895621699643152240774528997234560531000626933414021807058868302816246946325485308758093179344487790413825

@[expose] noncomputable def redK (x : Nat) : Nat :=
  strictN (Nat.add (Nat.land (Nat.shiftRight x 2) L63) (Nat.land x L3)) fun x1 =>
  strictN (Nat.add (Nat.land (Nat.shiftRight x1 2) L3) (Nat.land x1 L3)) fun x2 =>
  strictN (Nat.add (Nat.land (Nat.shiftRight x2 2) L1) (Nat.land x2 L3)) fun x3 =>
  strictN (Nat.land (Nat.land x3 (Nat.shiftRight x3 1)) L1) fun t =>
  Nat.xor x3 (Nat.lor t (Nat.shiftLeft t 1))

@[expose] noncomputable def colK (a j : Nat) : Nat :=
  Nat.land (Nat.shiftRight a (Nat.add 64 (Nat.mul 8 j))) COL

@[expose] noncomputable def rowK (b j : Nat) : Nat :=
  Nat.land (Nat.shiftRight b (Nat.add 64 (Nat.mul 64 j))) ROW

@[expose] noncomputable def mulK (a b : Nat) : Nat :=
  encS (redK (Nat.add (Nat.add (Nat.add (Nat.mul (colK a 0) (rowK b 0)) (Nat.mul (colK a 1) (rowK b 1)))
    (Nat.add (Nat.mul (colK a 2) (rowK b 2)) (Nat.mul (colK a 3) (rowK b 3))))
    (Nat.add (Nat.mul (colK a 4) (rowK b 4)) (Nat.mul (colK a 5) (rowK b 5)))))

@[expose] noncomputable def addK (a b : Nat) : Nat :=
  encS (redK (Nat.add (Nat.shiftRight a 64) (Nat.shiftRight b 64)))

@[expose] noncomputable def negM (m : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft (Nat.land m L1) 1) (Nat.land (Nat.shiftRight m 1) L1)

@[expose] noncomputable def negK (x : Nat) : Nat := encS (negM (Nat.shiftRight x 64))

@[expose] noncomputable def eqPK (x y : Nat) : Bool := orB (Nat.beq x y) (Nat.beq x (negK y))

@[expose] noncomputable def keyK (x : Nat) : Nat :=
  (fun y => Bool.rec (motive := fun _ => Nat) y x (Nat.blt x y)) (negK x)

@[expose] noncomputable def commK (x y : Nat) : Bool := eqPK (mulK x y) (mulK y x)

@[expose] noncomputable def validK (x : Nat) : Bool :=
  (fun m => andB (Nat.beq (encS m) x)
    (andB (Nat.beq (Nat.land m L3) m) (Nat.beq (Nat.land (Nat.land m (Nat.shiftRight m 1)) L1) 0)))
    (Nat.shiftRight x 64)

@[expose] noncomputable def trK (x : Nat) : Nat :=
  encS (Nat.rec (motive := fun _ => Nat) 0
    (fun p ih => strictN ih fun s =>
      Nat.lor s (Nat.shiftLeft
        (Nat.land (Nat.shiftRight x
          (Nat.add 64 (Nat.add (Nat.mul 64 (Nat.div p 6)) (Nat.mul 8 (Nat.mod p 6))))) 255)
        (Nat.add (Nat.mul 64 (Nat.mod p 6)) (Nat.mul 8 (Nat.div p 6)))))
    36)

@[expose] noncomputable def simTK (g gt : Nat) : Bool :=
  andB (andB (validK g) (Nat.beq (trK g) gt)) (eqPK (mulK g gt) IDK)

@[expose] noncomputable def simK (g : Nat) : Bool := simTK g (trK g)

@[expose] noncomputable def pow4K (x : Nat) : Nat := strictN (mulK x x) fun y => mulK y y

@[expose] noncomputable def pow5K (x : Nat) : Nat := mulK x (pow4K x)

@[expose] noncomputable def relK (a x : Nat) : Bool :=
  andB (eqPK (mulK a a) IDK)
    (andB (eqPK (pow4K (mulK a x)) IDK) (eqPK (pow5K (mulK (mulK x a) x)) IDK))

@[expose] noncomputable def getK (L : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) L

@[expose] noncomputable def lenK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun n => n)
    (fun _ _ ih n => strictN (Nat.succ n) ih) L 0

@[expose] noncomputable def allK (p : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (p x) ih) L

@[expose] noncomputable def anyK (p : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (p x) ih) L

@[expose] noncomputable def filtK (p : Nat → Bool) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => Bool.rec (motive := fun _ => List Nat) ih (x :: ih) (p x)) L

@[expose] noncomputable def beqLK (L : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun M => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) M)
    (fun x _ ih M => List.rec (motive := fun _ => Bool) false (fun y M' _ => andB (Nat.beq x y) (ih M')) M) L

@[expose] noncomputable def kidsK (step : Nat → Nat → Nat) (K x i : Nat) (k : List Nat → Nat → Bool)
    (g : List Nat) : List Nat → Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Nat → Bool) (fun cs p => k cs p)
    (fun l _ ih cs p => List.rec (motive := fun _ => Bool) false
      (fun y cs' _ => andB (andB (Nat.blt l K) (Nat.blt i p))
        (andB (Nat.beq y (step l x)) (strictB (Nat.succ p) fun p' => ih cs' p'))) cs) g

@[expose] noncomputable def runK (step : Nat → Nat → Nat) (K : Nat) (E : List Nat) :
    List (List Nat) → List Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => List (List Nat) → List Nat → Nat → Nat → Bool)
    (fun Cs cs _ _ => andB (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) Cs)
      (List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) cs))
    (fun x _ ih Cs cs i p => List.rec (motive := fun _ => Bool) false
      (fun g Cs' _ => kidsK step K x i (fun cs' p' => strictB (Nat.succ i) fun i' =>
        ih Cs' cs' i' p') g cs p) Cs) E

@[expose] noncomputable def walkK (step : Nat → Nat → Nat) (K x0 N : Nat) (E : List Nat)
    (C : List (List Nat)) : Bool :=
  andB (andB (Nat.beq (lenK E) N) (Nat.beq (getK E 0) x0))
    (List.rec (motive := fun _ => Bool) false (fun _ cs _ => runK step K E C cs 0 1) E)

@[expose] noncomputable def mergeK (L : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun M => M)
    (fun x xs ih M => List.rec (motive := fun _ => List Nat) (x :: xs)
      (fun y ys ihy => Bool.rec (motive := fun _ => List Nat) (y :: ihy) (x :: ih (y :: ys))
        (Nat.blt x y)) M) L

@[expose] noncomputable def pairK (Ls : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List Nat → Nat → List (List Nat))
    (fun pend f => Nat.rec (motive := fun _ => List (List Nat)) [] (fun _ _ => [pend]) f)
    (fun x _ ih pend f => Nat.rec (motive := fun _ => List (List Nat)) (ih x 1)
      (fun _ _ => mergeK pend x :: ih [] 0) f) Ls [] 0

@[expose] noncomputable def incK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih b => andB (Nat.ble b x) (ih (Nat.succ x))) L 0

@[expose] noncomputable def sortK (d : Nat) (L : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun x _ _ => x)
    (Nat.rec (motive := fun _ => List (List Nat))
      (List.rec (motive := fun _ => List (List Nat)) [] (fun x _ ih => [x] :: ih) L)
      (fun _ ih => pairK ih) d)

@[expose] noncomputable def nodupK (E : List Nat) : Bool :=
  incK (sortK 14 (List.rec (motive := fun _ => List Nat) [] (fun x _ ih => keyK x :: ih) E))
@[expose] def decM (x : Nat) : Array Nat :=
  Array.ofFn (n := 36) fun p => (x >>> (64 + 64 * (p.val / 6) + 8 * (p.val % 6))) &&& 255

@[expose] noncomputable def conjStepK (G GT : List Nat) (l x : Nat) : Nat :=
  mulK (mulK (getK G l) x) (getK GT l)

@[expose] noncomputable def leftStepK (E : List Nat) (l x : Nat) : Nat := mulK (getK E l) x

@[expose] noncomputable def gensK (G : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun GT => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) GT)
    (fun g _ ih GT => List.rec (motive := fun _ => Bool) false
      (fun gt GT' _ => andB (simTK g gt) (ih GT')) GT) G

@[expose] noncomputable def centGensK (E : List Nat) (x0 : Nat) : Bool :=
  allK (fun e => andB (simK e) (commK e x0)) E

@[expose] noncomputable def inReflK (F : List Nat) (c : Nat) : Bool := anyK (fun z => eqPK z c) F

@[expose] noncomputable def pairsK (F K : List Nat) : Bool :=
  allK (fun y1 => allK (fun y2 =>
    orB (orB (orB (eqPK y1 IDK) (eqPK y2 IDK)) (orB (eqPK y1 y2) (inReflK F y1)))
      (orB (inReflK F y2) (inReflK F (mulK y1 y2)))) K) K

@[expose] noncomputable def pairAK (g0 : Nat) (K0 F : List Nat) (a : Nat) (Ka : List Nat) : Bool :=
  orB (notB (relK a g0))
    (andB (andB (beqLK (filtK (fun c => commK c a) K0) Ka) (Nat.ble (lenK Ka) 4))
      (andB (allK (fun c => eqPK (mulK c c) IDK) Ka) (pairsK F Ka)))

@[expose] noncomputable def pairsAK (g0 : Nat) (K0 F : List Nat) (A : List Nat) :
    List (List Nat) → Bool :=
  List.rec (motive := fun _ => List (List Nat) → Bool)
    (fun KA => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) KA)
    (fun a _ ih KA => List.rec (motive := fun _ => Bool) false
      (fun Ka KA' _ => andB (pairAK g0 K0 F a Ka) (ih KA')) KA) A

@[expose] noncomputable def k0K (g0 : Nat) (CT K0 : List Nat) : Bool :=
  andB (beqLK (filtK (fun c => commK c g0) CT) K0) (Nat.beq (lenK K0) 40)

@[expose] noncomputable def constK (a0 g0 tau n0 r0 : Nat) : Bool :=
  andB (andB (andB (simK a0) (simK g0)) (andB (notB (eqPK g0 IDK)) (Nat.beq (pow5K g0) IDK)))
    (andB (andB (andB (simK tau) (eqPK (mulK tau tau) IDK))
        (strictB (mulK g0 g0) fun g2 => strictB (mulK g0 g2) fun g3 =>
          Nat.beq tau (negK (addK (addK g0 g2) (addK g3 (mulK g0 g3))))))
      (andB (andB (simK n0) (eqPK (mulK n0 g0) (mulK (mulK g0 g0) n0))) (simK r0)))

end CFSG.KC.A6CK
