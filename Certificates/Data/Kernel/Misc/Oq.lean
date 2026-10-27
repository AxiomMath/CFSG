module

public import Certificates.Data.Kernel.LocalQT.Perm

public section

namespace CFSG.KC.Misc.Oq

open CFSG.KC.Ord CFSG.KC.LQT.P

@[expose] noncomputable def fld6 (P i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul 6 i)) 63

@[expose] noncomputable def fld9 (P i : Nat) : Nat :=
  Nat.land (Nat.shiftRight P (Nat.mul 9 i)) 511

@[expose] noncomputable def bit (v j : Nat) : Nat := Nat.land (Nat.shiftRight v j) 1

@[expose] noncomputable def evV (P v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.xor acc (Nat.mul (bit v j) (fld6 P j))) 6

@[expose] noncomputable def evE (B e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun j acc => Nat.xor acc (Nat.mul (bit e j) (fld9 B j))) 9

@[expose] noncomputable def compK (A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (evV A (fld6 B i)) (Nat.mul 6 i))) 6

@[expose] noncomputable def wp (v : Nat) : Nat :=
  Nat.lor (Nat.land v 1) (Nat.lor (Nat.land (Nat.shiftRight v 1) 2) (Nat.land (Nat.shiftRight v 2) 4))

@[expose] noncomputable def xp (v : Nat) : Nat :=
  Nat.lor (Nat.land (Nat.shiftRight v 1) 1) (Nat.lor (Nat.land (Nat.shiftRight v 2) 2)
    (Nat.land (Nat.shiftRight v 3) 4))

@[expose] noncomputable def outK (a b : Nat) : Nat :=
  Nat.xor (Nat.mul (bit a 0) (Nat.land b 7)) (Nat.xor
    (Nat.mul (bit a 1) (Nat.shiftLeft (Nat.land b 7) 3))
    (Nat.mul (bit a 2) (Nat.shiftLeft (Nat.land b 7) 6)))

@[expose] noncomputable def qK (u v : Nat) : Nat :=
  Nat.xor (outK (wp v) (wp v)) (Nat.xor (outK (wp v) (xp v))
    (Nat.mul u (outK (xp v) (xp v))))

@[expose] noncomputable def betaK (u v w : Nat) : Nat :=
  Nat.xor (qK u (Nat.xor v w)) (Nat.xor (qK u v) (qK u w))

@[expose] noncomputable def bEntK (u P k : Nat) : Nat :=
  letN (Nat.div k 3) fun i => letN (Nat.mod k 3) fun j =>
    Bool.rec (motive := fun _ => Nat)
      (Nat.xor (qK u (evV P (Nat.add (Nat.pow 4 i) (Nat.mul 2 (Nat.pow 4 j)))))
        (Nat.xor (qK u (evV P (Nat.pow 4 i))) (Nat.mul u (qK u (evV P (Nat.mul 2 (Nat.pow 4 j)))))))
      (qK u (evV P (Nat.pow 4 i))) (Nat.beq i j)
where
  letN (y : Nat) (k : Nat → Nat) : Nat :=
    Nat.rec (motive := fun _ => Nat) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def bOfK (u P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.lor acc (Nat.shiftLeft (bEntK u P k) (Nat.mul 9 k))) 9

@[expose] noncomputable def idK : Nat := 34630287489

@[expose] noncomputable def idEK : Nat := 1210107565283851686118401

@[expose] noncomputable def omK : Nat := 52079657154

@[expose] noncomputable def om2K : Nat := 17986273347

@[expose] noncomputable def gamK (a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Bool.rec (motive := fun _ => Nat) 2172715524 34630815873 (Nat.beq a 1))
    51811205313 (Nat.beq a 0)

@[expose] noncomputable def eqN (a b : Nat) : Bool := Nat.beq a b

@[expose] noncomputable def isInvK (P : Nat) : Bool :=
  andB (eqN (compK P P) idK) (notB (eqN P idK))

@[expose] noncomputable def presK (u P : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (eqN (wp (evV P 2)) 0) (andB (eqN (wp (evV P 8)) 0) (eqN (wp (evV P 32)) 0)))
    (eqN (compK P omK) (compK omK P)) (Nat.beq u 1)

@[expose] noncomputable def inNl (v : Nat) : Bool := eqN (wp v) 0

@[expose] noncomputable def inNr (v : Nat) : Bool := eqN (wp v) (xp v)

@[expose] noncomputable def sgnK (u P : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (orB
      (andB (andB (inNl (evV P 2)) (andB (inNl (evV P 8)) (inNl (evV P 32))))
        (andB (inNr (evV P 3)) (andB (inNr (evV P 12)) (inNr (evV P 48)))))
      (andB (andB (inNr (evV P 2)) (andB (inNr (evV P 8)) (inNr (evV P 32))))
        (andB (inNl (evV P 3)) (andB (inNl (evV P 12)) (inNl (evV P 48))))))
    (orB (eqN (compK P omK) (compK omK P)) (eqN (compK P omK) (compK om2K P))) (Nat.beq u 1)

@[expose] noncomputable def memK (x : Nat) (L : List Nat) : Bool := anyL L fun y => Nat.beq y x

@[expose] noncomputable def compE9 (A B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.lor acc (Nat.shiftLeft (evE A (fld9 B k)) (Nat.mul 9 k))) 9

@[expose] noncomputable def appK {α : Type} (l₁ l₂ : List α) : List α :=
  List.rec (motive := fun _ => List α) l₂ (fun a _ ih => List.cons a ih) l₁

@[expose] noncomputable def lmRedK (rows : List Nat) (p : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun r _ ih p => letN (Nat.xor p r) fun q =>
      ih (Bool.rec (motive := fun _ => Nat) p q
        (Nat.blt (Nat.shiftRight q 9) (Nat.shiftRight p 9)))) rows p
where
  letN (y : Nat) (k : Nat → Nat) : Nat :=
    Nat.rec (motive := fun _ => Nat) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def oinsK (p : Nat) (rows : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons p List.nil)
    (fun b l ih => Bool.rec (motive := fun _ => List Nat) (List.cons b ih) (List.cons p (List.cons b l))
      (Nat.ble (Nat.shiftRight b 9) (Nat.shiftRight p 9))) rows

@[expose] noncomputable def lmAddK (rows : List Nat) (x y : Nat) : Option (List Nat) :=
  letO (lmRedK rows (Nat.add (Nat.mul x 512) y)) fun p =>
    Bool.rec (motive := fun _ => Option (List Nat)) (some (oinsK p rows))
      (Bool.rec (motive := fun _ => Option (List Nat)) none (some rows) (Nat.beq (Nat.land p 511) 0))
      (Nat.beq (Nat.shiftRight p 9) 0)
where
  letO (y : Nat) (k : Nat → Option (List Nat)) : Option (List Nat) :=
    Nat.rec (motive := fun _ => Option (List Nat)) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def codeK (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => Nat.add (Nat.mul 64 acc) (fld6 P i)) 6

@[expose] noncomputable def sortedK (L : List Nat) : Bool :=
  Prod.snd (List.rec (motive := fun _ => Nat × Bool) (68719476736, true)
    (fun x _ ih => (codeK x, andB (Nat.blt (codeK x) ih.1) ih.2)) L)

@[expose] noncomputable def candsK (u k : Nat) (rows : List Nat) : List Nat :=
  letL (lmRedK rows (Nat.mul (qK u (Nat.pow 2 k)) 512)) fun p =>
    Bool.rec (motive := fun _ => List Nat) (rangeK 64)
      (filterK 64 fun v => Nat.beq (qK u v) (Nat.land p 511)) (Nat.beq (Nat.shiftRight p 9) 0)
where
  letL (y : Nat) (k : Nat → List Nat) : List Nat :=
    Nat.rec (motive := fun _ => List Nat) (k 0) (fun m _ => k (Nat.succ m)) y
  rangeK (n : Nat) : List Nat := filterK n fun _ => true
  filterK (n : Nat) (f : Nat → Bool) : List Nat :=
    Nat.rec (motive := fun _ => List Nat → List Nat) (fun acc => acc)
      (fun v ih acc => ih (Bool.rec (motive := fun _ => List Nat) acc (List.cons v acc) (f v)))
      n List.nil

@[expose] noncomputable def redV (ib : List Nat) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun a => a)
    (fun b _ ih a => ih (Bool.rec (motive := fun _ => Nat) a (Nat.xor a b) (Nat.blt (Nat.xor a b) a)))
    ib a

@[expose] noncomputable def insV (a : Nat) (ib : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) (List.cons a List.nil)
    (fun b l ih => Bool.rec (motive := fun _ => List Nat) (List.cons b ih) (List.cons a (List.cons b l))
      (Nat.ble b a)) ib

@[expose] noncomputable def pairsK (u P k a : Nat) (rows : List Nat) : Option (List Nat) :=
  Nat.rec (motive := fun _ => Option (List Nat))
    (lmAddK rows (qK u (Nat.pow 2 k)) (qK u a))
    (fun j acc => Option.rec (motive := fun _ => Option (List Nat)) none
      (fun rs => lmAddK rs (betaK u (Nat.pow 2 k) (Nat.pow 2 j)) (betaK u a (fld6 P j))) acc) k

@[expose] noncomputable def step2K (u k : Nat) (st : Nat × List Nat × List Nat) :
    List (Nat × List Nat × List Nat) :=
  Prod.rec (motive := fun _ => List (Nat × List Nat × List Nat)) (fun P ri =>
    Prod.rec (motive := fun _ => List (Nat × List Nat × List Nat)) (fun rows ib =>
      List.rec (motive := fun _ => List (Nat × List Nat × List Nat)) List.nil
        (fun a _ ih => letS (redV ib a) fun ra =>
          Bool.rec (motive := fun _ => List (Nat × List Nat × List Nat))
            (Option.rec (motive := fun _ => List (Nat × List Nat × List Nat)) ih
              (fun rs => List.cons (Nat.add P (Nat.shiftLeft a (Nat.mul 6 k)), rs, insV ra ib) ih)
              (pairsK u P k a rows))
            ih (Nat.beq ra 0))
        (candsK u k rows)) ri) st
where
  letS (y : Nat) (k : Nat → List (Nat × List Nat × List Nat)) : List (Nat × List Nat × List Nat) :=
    Nat.rec (motive := fun _ => List (Nat × List Nat × List Nat)) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def level2K (u k : Nat) (L : List (Nat × List Nat × List Nat)) :
    List (Nat × List Nat × List Nat) :=
  List.rec (motive := fun _ => List (Nat × List Nat × List Nat)) List.nil
    (fun st _ ih => appK (step2K u k st) ih) L

@[expose] noncomputable def levels2K (u k₀ : Nat) (L : List (Nat × List Nat × List Nat)) :
    List (Nat × List Nat × List Nat) :=
  Nat.rec (motive := fun _ => List (Nat × List Nat × List Nat) → List (Nat × List Nat × List Nat))
    (fun L => L) (fun j ih L => ih (level2K u (Nat.sub 5 j) L)) (Nat.sub 6 k₀) L

@[expose] noncomputable def fstsK (L : List (Nat × List Nat × List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun st _ ih => List.cons st.1 ih) L

@[expose] noncomputable def initK (u t : Nat) : List (Nat × List Nat × List Nat) :=
  Bool.rec (motive := fun _ => List (Nat × List Nat × List Nat))
    (Option.rec (motive := fun _ => List (Nat × List Nat × List Nat)) List.nil
      (fun rs => List.cons (t, rs, List.cons t List.nil) List.nil) (lmAddK List.nil (qK u 1) (qK u t)))
    List.nil (Nat.beq t 0)

@[expose] noncomputable def search2K (u t : Nat) : List Nat := fstsK (levels2K u 1 (initK u t))

@[expose] noncomputable def lev3K (u : Nat) : List (Nat × List Nat × List Nat) :=
  level2K u 3 (level2K u 2 (level2K u 1 (initK u 1)))

@[expose] noncomputable def dropK {α : Type} (a : Nat) (L : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun L => L)
    (fun _ ih L => ih (List.rec (motive := fun _ => List α) List.nil (fun _ t _ => t) L)) a L

@[expose] noncomputable def takeK {α : Type} (n : Nat) (L : List α) : List α :=
  Nat.rec (motive := fun _ => List α → List α) (fun _ => List.nil)
    (fun _ ih L => List.rec (motive := fun _ => List α) List.nil (fun x t _ => List.cons x (ih t)) L)
    n L

@[expose] noncomputable def isNilK {α : Type} (L : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) L

@[expose] noncomputable def tabK (P : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun x acc => Nat.lor acc (Nat.shiftLeft (evV P x) (Nat.mul 6 x))) 64

@[expose] noncomputable def lk (T x : Nat) : Nat := fld6 T x

@[expose] noncomputable def omTab : Nat := tabK omK

@[expose] noncomputable def om2Tab : Nat := tabK om2K

@[expose] noncomputable def commT (Tr Ts Tk K : Nat) : Bool :=
  allN 6 fun i => eqN (lk Tr (lk Ts (fld6 K i))) (lk Tk (lk Tr (lk Ts (Nat.pow 2 i))))

@[expose] noncomputable def commT2 (Tr Ts : Nat) : Bool :=
  allN 6 fun i => eqN (lk Tr (lk Ts (fld6 omK i))) (lk om2Tab (lk Tr (lk Ts (Nat.pow 2 i))))

@[expose] noncomputable def invT (Tr Ts : Nat) : Bool :=
  andB (allN 6 fun i => eqN (lk Tr (lk Ts (lk Tr (lk Ts (Nat.pow 2 i))))) (Nat.pow 2 i))
    (anyN 6 fun i => notB (eqN (lk Tr (lk Ts (Nat.pow 2 i))) (Nat.pow 2 i)))

@[expose] noncomputable def packT (Tr Ts : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (Nat.shiftLeft (lk Tr (lk Ts (Nat.pow 2 i))) (Nat.mul 6 i))) 6

@[expose] noncomputable def sgnT (u Tr Ts : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (orB
      (andB (andB (inNl (lk Tr (lk Ts 2))) (andB (inNl (lk Tr (lk Ts 8))) (inNl (lk Tr (lk Ts 32)))))
        (andB (inNr (lk Tr (lk Ts 3))) (andB (inNr (lk Tr (lk Ts 12))) (inNr (lk Tr (lk Ts 48))))))
      (andB (andB (inNr (lk Tr (lk Ts 2))) (andB (inNr (lk Tr (lk Ts 8))) (inNr (lk Tr (lk Ts 32)))))
        (andB (inNl (lk Tr (lk Ts 3))) (andB (inNl (lk Tr (lk Ts 12))) (inNl (lk Tr (lk Ts 48)))))))
    (orB (commT Tr Ts omTab omK) (commT2 Tr Ts)) (Nat.beq u 1)

@[expose] noncomputable def presTT (u Tr Ts : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (andB (inNl (lk Tr (lk Ts 2))) (andB (inNl (lk Tr (lk Ts 8))) (inNl (lk Tr (lk Ts 32)))))
    (commT Tr Ts omTab omK) (Nat.beq u 1)

@[expose] noncomputable def kerT (u Tr Ts Bri Bs : Nat) : Bool :=
  impB (andB (Nat.beq u 1) (eqN Bs Bri))
    (letB (packT Tr Ts) fun l => orB (eqN l idK) (orB (eqN l omK) (eqN l om2K)))

@[expose] noncomputable def elemT (u : Nat) (RT : List (Nat × Nat)) (I : List Nat)
    (Ts Bs : Nat) : Bool :=
  allL2 RT fun Tr Bri =>
    andB (kerT u Tr Ts Bri Bs)
      (impB (andB (invT Tr Ts) (presTT u Tr Ts)) (memK (packT Tr Ts) I))
where
  allL2 (L : List (Nat × Nat)) (f : Nat → Nat → Bool) : Bool :=
    List.rec (motive := fun _ => Bool) true
      (fun p _ ih => andB (Prod.rec (motive := fun _ => Bool) f p) ih) L

@[expose] noncomputable def validK (u P : Nat) : Bool :=
  letB (tabK P) fun T => letB (bOfK u P) fun B =>
    andB (Nat.blt P 68719476736)
      (andB (allN 63 fun v => notB (eqN (lk T (Nat.succ v)) 0))
        (allN 64 fun v => eqN (qK u (lk T v)) (evE B (qK u v))))

@[expose] noncomputable def lettersK (w : List Nat) : Bool := allL w fun a => Nat.blt a 3

@[expose] noncomputable def letK (P a : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat) (gamK a) P (Nat.beq a 3)

@[expose] noncomputable def wordK (P : Nat) (w : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun a _ ih acc => letN (compK acc (letK P a)) ih) w
where
  letN (y : Nat) (k : Nat → Nat) : Nat :=
    Nat.rec (motive := fun _ => Nat) (k 0) (fun m _ => k (Nat.succ m)) y

@[expose] noncomputable def conjK (P r : Nat) (w : List Nat) : Bool :=
  andB (lettersK w) (letB (wordK P w idK) fun g => eqN (compK g P) (compK r g))

@[expose] noncomputable def elsK (P : Nat) (ws : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun w _ ih => List.cons (wordK P w idK) ih) ws

@[expose] noncomputable def lenK (L : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ ih => Nat.succ ih) L

@[expose] noncomputable def nodupK (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x t ih => andB (notB (memK x t)) ih) L

@[expose] noncomputable def cntK (N : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun k acc => Nat.add acc (Bool.rec (motive := fun _ => Nat) 0 1 (f k))) N

@[expose] noncomputable def pow2K (n : Nat) : Bool := anyN 9 fun k => Nat.beq n (Nat.pow 2 k)

@[expose] noncomputable def certK (u P : Nat) (ws : List (List Nat)) (v w : Nat) : Bool :=
  letB (bOfK u P) fun B =>
  andB (Nat.blt 0 (lenK (elsK P ws))) (andB (pow2K (lenK (elsK P ws)))
  (andB (nodupK (elsK P ws)) (andB (memK idK (elsK P ws)) (andB (memK P (elsK P ws))
  (andB (allL (elsK P ws) fun a => allL (elsK P ws) fun b => memK (compK a b) (elsK P ws))
  (andB (allL (elsK P ws) fun a => eqN (compK a P) (compK P a))
  (andB (Nat.ble (Nat.mul (cntK 64 fun x => eqN (evV P x) x) (cntK 512 fun e => eqN (evE B e) e))
      (Nat.mul 32 (lenK (elsK P ws))))
  (andB (Nat.blt v 64) (andB (Nat.blt w 64) (andB (eqN (evV P v) v) (andB (eqN (evV P w) w)
  (notB (anyN 512 fun e => eqN (Nat.xor (evE B e) e) (betaK u v w))))))))))))))

@[expose] noncomputable def rtK (R BR : List Nat) : List (Nat × Nat) :=
  List.rec (motive := fun _ => List Nat → List (Nat × Nat)) (fun _ => List.nil)
    (fun r _ ih BR => List.rec (motive := fun _ => List (Nat × Nat)) List.nil
      (fun b t _ => List.cons (tabK r, b) (ih t)) BR) R BR

@[expose] noncomputable def invsK (u : Nat) (R BR : List Nat) : Bool :=
  List.rec (motive := fun _ => List Nat → Bool) (fun BR => isNilK BR)
    (fun r _ ih BR => List.rec (motive := fun _ => Bool) false
      (fun b t _ => andB (andB (Nat.blt b 2417851639229258349412352)
        (eqN (compE9 (bOfK u r) b) idEK)) (ih t)) BR) R BR

@[expose] noncomputable def headK (R : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun r _ ih => List.cons (fld6 r 0) ih) R

@[expose] noncomputable def badK (u : Nat) (R : List Nat) : Bool :=
  allN 64 fun t => impB (notB (memK t (headK R))) (isNilK (search2K u t))

@[expose] noncomputable def getK (L : List Nat) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ _ => x) (dropK k L)

@[expose] noncomputable def fstIK (D : List (Nat × List Nat × Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun e _ ih => List.cons e.1 ih) D

@[expose] noncomputable def conjsK (KR : List Nat) (D : List (Nat × List Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun e _ ih => andB (andB (Nat.blt e.2.2 (lenK KR)) (conjK e.1 (getK KR e.2.2) e.2.1)) ih) D

@[expose] noncomputable def certsK (u : Nat) (KR : List Nat)
    (CD : List (List (List Nat) × Nat × Nat)) : Bool :=
  List.rec (motive := fun _ => List (List (List Nat) × Nat × Nat) → Bool) (fun CD => isNilK CD)
    (fun P _ ih CD => List.rec (motive := fun _ => Bool) false
      (fun c t _ => andB (andB (validK u P) (certK u P c.1 c.2.1 c.2.2)) (ih t)) CD) KR CD

end CFSG.KC.Misc.Oq

end
