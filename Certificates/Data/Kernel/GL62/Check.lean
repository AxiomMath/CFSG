module

public import Certificates.Data.Kernel.GL62.Lanes

public section

namespace CFSG.KC.GL62

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc

@[expose] noncomputable def ONE : Nat := nat_lit 34630287489

@[expose] noncomputable def ZC : Nat := nat_lit 38959071361

@[expose] noncomputable def T36 : Nat := nat_lit 68719476736

@[expose] noncomputable def allK {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => andB (f x) ih) l

@[expose] noncomputable def anyK {α : Type} (l : List α) (f : α → Bool) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => orB (f x) ih) l

@[expose] noncomputable def nthK {α : Type} (l : List α) (d : α) (i : Nat) : α :=
  List.rec (motive := fun _ => Nat → α) (fun _ => d)
    (fun x _ ih i => Nat.rec (motive := fun _ => α) x (fun j _ => ih j) i) l i

@[expose] noncomputable def zipK {α β : Type} (l : List α) (m : List β) (i₀ : Nat)
    (f : Nat → α → β → Bool) : Bool :=
  List.rec (motive := fun _ => Nat → List β → Bool)
    (fun _ m => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) m)
    (fun x _ ih i m => List.rec (motive := fun _ => Bool) false
      (fun y t _ => andB (f i x y) (letB (Nat.succ i) fun j => ih j t)) m) l i₀ m

@[expose] noncomputable def lenK {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def nilK {α : Type} (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def incK (lo : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih lo => andB (Nat.blt lo x) (andB (Nat.blt x T36) (ih x))) l lo

@[expose] noncomputable def bitsK (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun p _ ih => Nat.lor (Nat.shiftLeft 1 p) ih) l

@[expose] noncomputable def flatK {α : Type} (L : List (List α)) : List α :=
  List.rec (motive := fun _ => List α) List.nil
    (fun l _ ih => List.rec (motive := fun _ => List α) ih (fun x _ ih2 => List.cons x ih2) l) L

@[expose] noncomputable def fstK {β : Type} (l : List (Nat × β)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x _ ih => List.cons (Prod.rec (motive := fun _ => Nat) (fun a _ => a) x) ih) l

@[expose] noncomputable def letterK (BP g a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (laneK BP (Nat.sub a 1)) g (Nat.beq a 0)

@[expose] noncomputable def lettersK (w : List Nat) : Bool := allL w fun a => Nat.ble a 336

@[expose] noncomputable def wordK (BP g : Nat) (w : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun a _ ih acc => letN (cmulK acc (letterK BP g a)) ih) w ONE

@[expose] noncomputable def badW (BP y : Nat) (w : List Nat) : Bool :=
  andB (lettersK w) (letB (wordK BP y w) fun e =>
    andB (Nat.beq (cmulK e ZC) (cmulK ZC e)) (notB (blkK e)))

@[expose] noncomputable def conjL (L Rl Fl BP BIP r : Nat) : Nat :=
  mulL Rl Fl BIP (mulL Rl Fl (Nat.mul r L) BP)

@[expose] noncomputable def stabK (L Y r : Nat) : Nat :=
  Nat.sub 336 (nzL 336 L (Nat.xor Y (Nat.mul r L)))

@[expose] noncomputable def genK (l : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) (nat_lit 9131004162) (nat_lit 34764505281) (Nat.beq l 1))
    ZC (Nat.beq l 0)

@[expose] noncomputable def depthsK (BT : List (Nat × Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun e _ ih => List.cons
    (Prod.rec (motive := fun _ => Nat) (fun _ r => Prod.rec (motive := fun _ => Nat)
      (fun _ d => d) r) e) ih) BT

@[expose] noncomputable def treeK (BL : List Nat) (BP : Nat) (BT : List (Nat × Nat × Nat)) :
    Bool :=
  letB (packL (depthsK BT)) fun DP =>
  zipK BL BT 0 fun _ x e => Prod.rec (motive := fun _ => Bool) (fun par r =>
    Prod.rec (motive := fun _ => Bool) (fun l d => andB (Nat.ble l 2) (andB (Nat.blt d 336)
      (Bool.rec (motive := fun _ => Bool)
        (andB (Nat.blt par 336) (andB (Nat.beq (Nat.succ (laneK DP par)) d)
          (Nat.beq (cmulK (laneK BP par) (genK l)) x)))
        (Nat.beq x ONE) (Nat.beq d 0)))) r) e

@[expose] noncomputable def bK (BL BIL : List Nat) (BP BIP : Nat) (BT : List (Nat × Nat × Nat)) :
    Bool :=
  andB (incK 0 BL) (andB (Nat.beq (lenN BL) 336) (andB (allL BL blkK)
  (andB (Nat.beq (lenN BIL) 336) (andB (allL BIL fun x => Nat.blt x T36)
    (andB (Nat.beq BP (packL BL)) (andB (Nat.beq BIP (packL BIL))
      (letB (lrep 336) fun L => letB (Nat.mul R6 L) fun Rl => letB (Nat.mul 63 L) fun Fl =>
        letB (Nat.mul ONE L) fun OL =>
        andB (Nat.beq (mulL Rl Fl BP BIP) OL) (andB (Nat.beq (mulL Rl Fl BIP BP) OL)
          (treeK BL BP BT)))))))))

@[expose] noncomputable def recK (L Rl Fl BP BIP : Nat) (GR : List Nat)
    (x : Nat × Nat × Nat × Nat × List Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool) (fun r rest => Prod.rec (motive := fun _ => Bool)
    (fun s rest => Prod.rec (motive := fun _ => Bool) (fun g rest =>
      Prod.rec (motive := fun _ => Bool) (fun g' w =>
        andB (Nat.blt r T36) (letB (conjL L Rl Fl BP BIP r) fun Y =>
        andB (Nat.beq (stabK L Y r) s) (andB (geL L Y r)
        (andB (Nat.blt 0 s) (andB (Nat.beq (Nat.mod 336 s) 0)
        (andB (Nat.beq (cmulK (cmulK g ZC) g') r) (andB (Nat.beq (cmulK g g') ONE)
        (andB (Nat.beq (cmulK g' g) ONE)
          (Bool.rec (motive := fun _ => Bool) (badW BP r w) (memN r GR) (nilK w)))))))))) rest)
      rest) rest) x

@[expose] noncomputable def rcK (BP BIP : Nat) (GR : List Nat)
    (ch : List (Nat × Nat × Nat × Nat × List Nat)) : Bool :=
  letB (lrep 336) fun L => letB (Nat.mul R6 L) fun Rl => letB (Nat.mul 63 L) fun Fl =>
    allK ch (recK L Rl Fl BP BIP GR)

@[expose] noncomputable def ordK (RC : List (List (Nat × Nat × Nat × Nat × List Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool)
    (fun _ sum cnt => andB (Nat.beq sum 234360) (Nat.beq cnt 827))
    (fun x _ ih prev sum cnt => Prod.rec (motive := fun _ => Bool) (fun r rest =>
      Prod.rec (motive := fun _ => Bool) (fun s _ => andB (Nat.blt prev r)
        (letB (Nat.add sum (Nat.div 336 s)) fun sum' => letB (Nat.succ cnt) fun cnt' =>
          ih r sum' cnt')) rest) x)
    (flatK RC) 0 0 0

@[expose] noncomputable def headsK (GD : List (Nat × List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun e _ ih => List.cons
    (Prod.rec (motive := fun _ => Nat) (fun _ O => nthK O 0 0) e) ih) GD

@[expose] noncomputable def goodK (BP BIP : Nat) (GD : List (Nat × List Nat)) : Bool :=
  andB (Nat.beq (lenK GD) 17) (andB (Nat.beq (nthK (fstK GD) 0 0) ZC) (andB (nodupN (headsK GD))
  (letB (lrep 336) fun L => letB (Nat.mul R6 L) fun Rl => letB (Nat.mul 63 L) fun Fl =>
    allK GD fun e => Prod.rec (motive := fun _ => Bool) (fun r O =>
      andB (Nat.blt r T36) (andB (Nat.beq (cmulK r r) ONE)
      (letB (conjL L Rl Fl BP BIP r) fun Y => letB (stabK L Y r) fun s =>
      andB (Nat.blt 0 s) (andB (incK 0 O) (andB (Nat.beq (lenN O) (Nat.div 336 s))
        (allL O fun x => Nat.blt (nzL 336 L (Nat.xor Y (Nat.mul x L))) 336)))))) e)))

@[expose] noncomputable def commRow (GD : List (Nat × List Nat)) (ra : Nat) (row : List Nat) :
    Bool :=
  zipK GD row 0 fun _ e c => Prod.rec (motive := fun _ => Bool) (fun _ O =>
    letB (lenN O) fun N => letB (lrep N) fun L => letB (Nat.mul R6 L) fun Rl =>
    letB (Nat.mul 63 L) fun Fl => letB (packL O) fun X => letB (Nat.mul ra L) fun A =>
      andB (Nat.blt 0 N)
        (Nat.beq (Nat.sub N (nzL N L (Nat.xor (mulL Rl Fl A X) (mulL Rl Fl X A)))) c)) e

@[expose] noncomputable def commK (GD : List (Nat × List Nat)) (C : List (List Nat)) : Bool :=
  zipK GD C 0 fun _ e row => Prod.rec (motive := fun _ => Bool) (fun ra _ => commRow GD ra row) e

@[expose] noncomputable def witC (BP : Nat) (W : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor
    (Prod.rec (motive := fun _ => Nat) (fun _ k => laneK BP k) x) (Nat.shiftLeft ih 64)) W

@[expose] noncomputable def witR (RP : Nat) (W : List (Nat × Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun x _ ih => Nat.lor
    (Prod.rec (motive := fun _ => Nat) (fun p _ => laneK RP p) x) (Nat.shiftLeft ih 64)) W

@[expose] noncomputable def witOK (W : List (Nat × Nat)) : Bool :=
  allK W fun x => Prod.rec (motive := fun _ => Bool)
    (fun p k => andB (Nat.blt p 17) (Nat.blt k 336)) x

@[expose] noncomputable def witM (W : List (Nat × Nat)) : Nat := bitsK (fstK W)

@[expose] noncomputable def goodPair (BP RP ra : Nat) (O : List Nat) (h : Nat)
    (W : List (Nat × Nat)) : Bool :=
  letB (lenN O) fun N => andB (Nat.blt 0 N) (andB (Nat.beq (lenK W) N) (andB (witOK W)
  (andB (Nat.beq h (witM W))
  (letB (lrep N) fun L => letB (Nat.mul R6 L) fun Rl => letB (Nat.mul 63 L) fun Fl =>
  letB (packL O) fun X => letB (Nat.mul ra L) fun A =>
  letB (mulL Rl Fl A (mulL Rl Fl X A)) fun Y => letB (witC BP W) fun Cl =>
    Nat.beq (mulL Rl Fl (witR RP W) Cl) (mulL Rl Fl Cl Y)))))

@[expose] noncomputable def hbHas (HB : List (Nat × Nat × Nat × List Nat)) (a b : Nat) : Bool :=
  anyK HB fun x => Prod.rec (motive := fun _ => Bool) (fun a' rest =>
    Prod.rec (motive := fun _ => Bool) (fun b' _ => andB (Nat.beq a a') (Nat.beq b b')) rest) x

@[expose] noncomputable def hitRow (BP RP : Nat) (GD : List (Nat × List Nat))
    (HB : List (Nat × Nat × Nat × List Nat)) (a ra : Nat) (Hrow : List Nat)
    (Wrow : List (List (Nat × Nat))) : Bool :=
  andB (Nat.beq (lenK Hrow) 17) (zipK GD Wrow 0 fun b e W =>
    letB (nthK Hrow 0 b) fun h => Prod.rec (motive := fun _ => Bool) (fun _ O =>
      Bool.rec (motive := fun _ => Bool) (goodPair BP RP ra O h W) (hbHas HB a b)
        (Nat.beq h 131072)) e)

@[expose] noncomputable def hitK (BP : Nat) (GD : List (Nat × List Nat))
    (HB : List (Nat × Nat × Nat × List Nat)) (H : List (List Nat))
    (HW : List (List (List (Nat × Nat)))) (a : Nat) : Bool :=
  andB (Nat.blt a 17) (letB (packL (fstK GD)) fun RP =>
    hitRow BP RP GD HB a (nthK (fstK GD) 0 a) (nthK H List.nil a) (nthK HW List.nil a))

@[expose] noncomputable def hbK (BP : Nat) (GD : List (Nat × List Nat))
    (HB : List (Nat × Nat × Nat × List Nat)) : Bool :=
  allK HB fun e => Prod.rec (motive := fun _ => Bool) (fun a rest =>
    Prod.rec (motive := fun _ => Bool) (fun b rest => Prod.rec (motive := fun _ => Bool)
      (fun x w => andB (Nat.blt a 17) (andB (Nat.blt b 17)
        (andB (memN x (Prod.rec (motive := fun _ => List Nat) (fun _ O => O)
          (nthK GD (0, List.nil) b)))
        (letB (nthK (fstK GD) 0 a) fun ra =>
          badW BP (cmulK (cmulK ra x) ra) w)))) rest) rest) e

@[expose] noncomputable def famSizesK : List (Nat × Nat) :=
  [(1, 1), (9, 3), (127, 360), (16383, 1080), (114691, 168)]

@[expose] noncomputable def bitK (m b : Nat) : Bool := Nat.blt 0 (Nat.land m (Nat.shiftLeft 1 b))

@[expose] noncomputable def rowOr (HT a I : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun b acc => Bool.rec (motive := fun _ => Nat)
    acc (Nat.lor acc (laneK HT (Nat.add (Nat.mul 17 a) b))) (bitK I b)) (nat_lit 17)

@[expose] noncomputable def closeF (HT I : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun a acc => Bool.rec (motive := fun _ => Nat)
    acc (Nat.lor acc (rowOr HT a I)) (bitK I a)) (nat_lit 17)

@[expose] noncomputable def rowSum (CT a I : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun b acc => Bool.rec (motive := fun _ => Nat)
    acc (Nat.add acc (laneK CT (Nat.add (Nat.mul 17 a) b))) (bitK I b)) (nat_lit 17)

@[expose] noncomputable def sizeK (SP I : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun b acc => Bool.rec (motive := fun _ => Nat)
    acc (Nat.add acc (laneK SP b)) (bitK I b)) (nat_lit 17)

@[expose] noncomputable def homK (CT I : Nat) : Bool :=
  letB (rowSum CT 0 I) fun c0 => Nat.rec (motive := fun _ => Bool) true
    (fun a ih => andB (Bool.rec (motive := fun _ => Bool) true
      (Nat.beq (rowSum CT a I) c0) (bitK I a)) ih) (nat_lit 17)

@[expose] noncomputable def famOK (I s : Nat) : Bool :=
  anyK famSizesK fun x => Prod.rec (motive := fun _ => Bool)
    (fun m n => andB (Nat.beq I m) (Nat.beq s n)) x

@[expose] noncomputable def search (HT CT SP fuel : Nat) : Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun _ ih I O => letB (closeF HT I) fun F =>
      Bool.rec (motive := fun _ => Bool)
        (Bool.rec (motive := fun _ => Bool)
          (letB (Nat.lor I O) fun U => Bool.rec (motive := fun _ => Bool)
            (letB (Nat.xor U 131071) fun t => letB (Nat.land t (Nat.xor t (Nat.sub t 1))) fun v =>
              andB (letB (Nat.lor I v) fun I' => ih I' O) (letB (Nat.lor O v) fun O' => ih I O'))
            (orB (notB (homK CT I)) (famOK I (sizeK SP I)))
            (Nat.beq U 131071))
          (letB (Nat.lor I F) fun I' => ih I' O)
          (notB (Nat.beq (Nat.lor I F) I)))
        true (orB (bitK F 17) (Nat.blt 0 (Nat.land F O)))) fuel

@[expose] noncomputable def elimK (GD : List (Nat × List Nat)) (H C : List (List Nat)) : Bool :=
  andB (Nat.beq (lenK H) 17) (andB (allK H fun r => Nat.beq (lenN r) 17)
  (andB (Nat.beq (lenK C) 17) (andB (allK C fun r => Nat.beq (lenN r) 17)
  (andB (allK (flatK H) fun x => Nat.blt x 262144)
  (andB (allK (flatK C) fun x => Nat.blt x 1024)
  (letB (packL (flatK H)) fun HT => letB (packL (flatK C)) fun CT =>
  letB (packL (List.rec (motive := fun _ => List Nat) List.nil
    (fun e _ ih => List.cons (Prod.rec (motive := fun _ => Nat) (fun _ O => lenN O) e) ih) GD))
    fun SP => search HT CT SP 40 1 0))))))

@[expose] noncomputable def famK (BP : Nat) (GD : List (Nat × List Nat))
    (F : List (Nat × Nat × Nat × List (Nat × List Nat))) : Bool :=
  allK F fun f => Prod.rec (motive := fun _ => Bool) (fun mask rest =>
    Prod.rec (motive := fun _ => Bool) (fun q rest => Prod.rec (motive := fun _ => Bool)
      (fun g ents => andB (Nat.blt q 17) (andB (bitK mask q)
        (andB (memN g (Prod.rec (motive := fun _ => List Nat) (fun _ O => O)
          (nthK GD (0, List.nil) q)))
        (andB (Nat.beq mask (bitsK (fstK ents)))
        (allK ents fun pw => Prod.rec (motive := fun _ => Bool) (fun p w =>
          andB (Nat.blt p 17) (andB (lettersK w) (letB (wordK BP g w) fun e =>
            Nat.beq (cmulK e ZC) (cmulK (nthK (fstK GD) 0 p) e)))) pw))))) rest) rest) f

end CFSG.KC.GL62

end
