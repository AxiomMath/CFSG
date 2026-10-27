module

public import Certificates.Data.Kernel.Misc.O62

public section

namespace CFSG.KC.Misc.Sp6

open CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc CFSG.KC.Misc.O62

@[expose] noncomputable def imgK (A j : Nat) : Nat :=
  Nat.land (Nat.shiftRight A (Nat.mul (nat_lit 6) (Nat.sub (nat_lit 5) j))) (nat_lit 63)

@[expose] noncomputable def codeL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun acc => acc)
    (fun x _ ih acc => ih (Nat.add (Nat.mul (nat_lit 64) acc) x)) l (nat_lit 0)

@[expose] noncomputable def tupOK (l : List Nat) : Bool :=
  andB (Nat.beq (lenN l) (nat_lit 6)) (allL l fun x => Nat.blt x (nat_lit 64))

@[expose] noncomputable def tLo (A : Nat) : Nat := tab3 (imgK A 0) (imgK A 1) (imgK A 2)

@[expose] noncomputable def tHi (A : Nat) : Nat := tab3 (imgK A 3) (imgK A 4) (imgK A 5)

@[expose] noncomputable def compK (A B : Nat) : Nat :=
  letN A fun A => letN B fun B => letN (tLo A) fun T₀ => letN (tHi A) fun T₁ =>
  Nat.lor (Nat.lor (Nat.lor (Nat.shiftLeft (actT T₀ T₁ (imgK B 0)) (nat_lit 30))
      (Nat.shiftLeft (actT T₀ T₁ (imgK B 1)) (nat_lit 24)))
    (Nat.lor (Nat.shiftLeft (actT T₀ T₁ (imgK B 2)) (nat_lit 18))
      (Nat.shiftLeft (actT T₀ T₁ (imgK B 3)) (nat_lit 12))))
    (Nat.lor (Nat.shiftLeft (actT T₀ T₁ (imgK B 4)) (nat_lit 6)) (actT T₀ T₁ (imgK B 5)))

@[expose] noncomputable def idK : Nat := nat_lit 1108378656

@[expose] noncomputable def wK (v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land v (nat_lit 1)) (Nat.land (Nat.shiftRight v (nat_lit 1)) (nat_lit 2)))
    (Nat.land (Nat.shiftRight v (nat_lit 2)) (nat_lit 4))

@[expose] noncomputable def xK (v : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.land (Nat.shiftRight v (nat_lit 1)) (nat_lit 1))
    (Nat.land (Nat.shiftRight v (nat_lit 2)) (nat_lit 2)))
    (Nat.land (Nat.shiftRight v (nat_lit 3)) (nat_lit 4))

@[expose] noncomputable def mkvK (w x : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.lor (Nat.land w (nat_lit 1)) (Nat.shiftLeft (Nat.land w (nat_lit 2)) (nat_lit 1)))
      (Nat.lor (Nat.shiftLeft (Nat.land w (nat_lit 4)) (nat_lit 2))
        (Nat.shiftLeft (Nat.land x (nat_lit 1)) (nat_lit 1))))
    (Nat.lor (Nat.shiftLeft (Nat.land x (nat_lit 2)) (nat_lit 2))
      (Nat.shiftLeft (Nat.land x (nat_lit 4)) (nat_lit 3)))

@[expose] noncomputable def outerK (a b : Nat) : Nat :=
  letN (Nat.land b (nat_lit 7)) fun b =>
  Nat.xor (Nat.xor (Nat.mul (bitK a 0) b) (Nat.mul (bitK a 1) (Nat.shiftLeft b (nat_lit 3))))
    (Nat.mul (bitK a 2) (Nat.shiftLeft b (nat_lit 6)))

@[expose] noncomputable def qK (m v : Nat) : Nat :=
  letN v fun v => letN (wK v) fun w => letN (xK v) fun x =>
    Nat.xor (Nat.xor (outerK w w) (outerK w x)) (Nat.mul m (outerK x x))

@[expose] noncomputable def qImg (m T₀ T₁ v : Nat) : Nat := qK m (actT T₀ T₁ v)

@[expose] noncomputable def bEntry (m T₀ T₁ i j : Nat) : Nat :=
  Bool.rec (motive := fun _ => Nat)
    (Nat.xor (Nat.xor (qImg m T₀ T₁ (mkvK (Nat.shiftLeft 1 i) (Nat.shiftLeft 1 j)))
        (qImg m T₀ T₁ (mkvK (Nat.shiftLeft 1 i) 0)))
      (Nat.mul m (qImg m T₀ T₁ (mkvK 0 (Nat.shiftLeft 1 j)))))
    (qImg m T₀ T₁ (mkvK (Nat.shiftLeft 1 i) 0)) (Nat.beq i j)

@[expose] noncomputable def bTabK (m T₀ T₁ : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.rec (motive := fun _ => Nat) acc
    (fun j acc2 => Nat.lor acc2 (Nat.shiftLeft (bEntry m T₀ T₁ i j)
      (Nat.mul (nat_lit 9) (Nat.add (Nat.mul (nat_lit 3) i) j)))) (nat_lit 3)) (nat_lit 3)

@[expose] noncomputable def lane9 (B k : Nat) : Nat :=
  Nat.land (Nat.shiftRight B (Nat.mul (nat_lit 9) k)) (nat_lit 511)

@[expose] noncomputable def evalEK (B e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun k acc => Nat.xor acc (Nat.mul (bitK e k) (lane9 B k))) (nat_lit 9)

@[expose] noncomputable def validK (m A : Nat) : Bool :=
  letB (tLo A) fun T₀ => letB (tHi A) fun T₁ => letB (bTabK m T₀ T₁) fun B =>
    allN (nat_lit 64) fun v => letB (actT T₀ T₁ v) fun w =>
      andB (orB (Nat.beq v 0) (notB (Nat.beq w 0))) (Nat.beq (qK m w) (evalEK B (qK m v)))

@[expose] noncomputable def qlCnt (Q : Nat) : Nat := Nat.land Q (nat_lit 255)

@[expose] noncomputable def qlAt (Q i : Nat) : Nat :=
  Nat.land (Nat.shiftRight Q (Nat.add (nat_lit 8) (Nat.mul (nat_lit 36) i))) m36

@[expose] noncomputable def qlOfL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun i acc => Nat.add acc i)
    (fun x _ ih i acc => ih (Nat.succ i) (Nat.lor acc (Nat.shiftLeft x (Nat.add (nat_lit 8)
      (Nat.mul (nat_lit 36) i))))) l (nat_lit 0) (nat_lit 0)

@[expose] noncomputable def qlIdx (Q y : Nat) : Nat :=
  letN y fun y => Nat.rec (motive := fun _ => Nat) (qlCnt Q)
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc i (Nat.beq (qlAt Q i) y)) (qlCnt Q)

@[expose] noncomputable def nthN (l : List Nat) (i : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat) x (fun j _ => ih j) i) l i

@[expose] noncomputable def popN (M n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0) (fun i acc => Nat.add acc (bitK M i)) n

@[expose] noncomputable def hasB (M i : Nat) : Bool := Nat.blt 0 (Nat.land M (Nat.shiftLeft 1 i))

@[expose] noncomputable def qlMem (Q y : Nat) : Bool :=
  letB y fun y => anyN (qlCnt Q) fun i => Nat.beq (qlAt Q i) y

@[expose] noncomputable def gensK (G : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil (fun g _ ih => List.cons (codeL g) ih) G

@[expose] noncomputable def treeK (m : Nat) (G : List (List Nat)) (Pl : List Nat) (PQ : Nat)
    (par gen dep : List Nat) : Bool :=
  andB (allLL G tupOK) <| andB (Nat.beq (lenN Pl) 128) <|
  andB (allL Pl fun x => Nat.blt x (Nat.shiftLeft 1 36)) <|
  andB (Nat.beq (qlOfL Pl) PQ) <| andB (Nat.beq (qlCnt PQ) 128) <|
  andB (Nat.beq (qlAt PQ 0) idK) <|
  andB (allN 128 fun k => orB (Nat.beq k 0) (letB (nthN par k) fun p =>
      andB (Nat.blt p k) (andB (Nat.blt (nthN gen k) (lenN (gensK G)))
      (andB (Nat.beq (nthN dep k) (Nat.succ (nthN dep p))) (andB (Nat.ble (nthN dep k) 40)
        (Nat.beq (qlAt PQ k) (compK (qlAt PQ p) (nthN (gensK G) (nthN gen k))))))))) <|
  andB (allL (gensK G) fun g => qlMem PQ g) <|
  andB (allN 128 fun i => allN i fun j => notB (Nat.beq (qlAt PQ i) (qlAt PQ j))) <|
    allN 128 fun i => validK m (qlAt PQ i)

@[expose] noncomputable def closK (PQ lo n : Nat) : Bool :=
  allN n fun d => letB (qlAt PQ (Nat.add lo d)) fun a =>
    allN (qlCnt PQ) fun j => qlMem PQ (compK a (qlAt PQ j))

@[expose] noncomputable def invK (x : Nat) : Bool :=
  andB (Nat.beq (compK x x) idK) (notB (Nat.beq x idK))

@[expose] noncomputable def invsL (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) List.nil
    (fun x _ ih => Bool.rec (motive := fun _ => List Nat) ih (List.cons x ih) (invK x)) l

@[expose] noncomputable def commMask (PQ x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun j acc => letN (qlAt PQ j) fun a => Bool.rec (motive := fun _ => Nat) acc
      (Nat.lor acc (Nat.shiftLeft 1 j)) (Nat.beq (compK x a) (compK a x))) (qlCnt PQ)

@[expose] noncomputable def invChk (Pl : List Nat) (PQ : Nat) (IV IVI CM : List Nat) : Bool :=
  andB (eqLN (invsL Pl) IV) <| andB (Nat.beq (lenN IVI) (lenN IV)) <|
  andB (Nat.beq (lenN CM) (lenN IV)) <|
    allN (lenN IV) fun t => letB (nthN IV t) fun x =>
      andB (Nat.blt (nthN IVI t) 128) (andB (Nat.beq (qlAt PQ (nthN IVI t)) x)
        (Nat.beq (nthN CM t) (commMask PQ x)))

@[expose] noncomputable def adjK (PQ x A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) A
    (fun i acc => Bool.rec (motive := fun _ => Nat) acc
      (Nat.lor acc (Nat.shiftLeft 1 (qlIdx PQ (compK x (qlAt PQ i))))) (hasB A i)) (nat_lit 128)

@[expose] noncomputable def extOK (PQ A : Nat) (IVI CM EL : List Nat) (x t : Nat) : Bool :=
  impB (andB (notB (hasB A (nthN IVI t))) (Nat.beq (Nat.land A (Nat.xor (nthN CM t)
      (nat_lit 340282366920938463463374607431768211455))) 0))
    (letB (adjK PQ x A) fun B => andB (memN B EL) (Nat.blt (popN A 128) (popN B 128)))

@[expose] noncomputable def fixE (XE : Nat → Nat) (B : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (Nat.sub (Nat.shiftLeft 1 512) 1)
    (fun i acc => letN (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun j y => Nat.xor y (Nat.mul (bitK (lane9 B j) i) (XE j))) (nat_lit 9)) fun Y =>
      Nat.land acc (Nat.sub (Nat.sub (Nat.shiftLeft 1 512) 1) (Nat.xor Y (XE i)))) (nat_lit 9)

@[expose] noncomputable def fixV (XV : Nat → Nat) (A : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    (Nat.sub (Nat.shiftLeft 1 64) 1)
    (fun i acc => letN (Nat.rec (motive := fun _ => Nat) (nat_lit 0)
        (fun j y => Nat.xor y (Nat.mul (bitK (imgK A j) i) (XV j))) (nat_lit 6)) fun Y =>
      Nat.land acc (Nat.sub (Nat.sub (Nat.shiftLeft 1 64) 1) (Nat.xor Y (XV i)))) (nat_lit 6)

@[expose] noncomputable def xeK (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun e acc => Nat.lor acc (Nat.mul (bitK e j) (Nat.shiftLeft 1 e))) (nat_lit 512)

@[expose] noncomputable def xvK (j : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v acc => Nat.lor acc (Nat.mul (bitK v j) (Nat.shiftLeft 1 v))) (nat_lit 64)

@[expose] noncomputable def q0K (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun v acc => Bool.rec (motive := fun _ => Nat) acc (Nat.lor acc (Nat.shiftLeft 1 v))
      (Nat.beq (qK m v) 0)) (nat_lit 64)

@[expose] noncomputable def tabsK (m : Nat) (XE XV : Nat → Nat) (Q0 : Nat) : Bool :=
  andB (allN 9 fun j => Nat.beq (XE j) (xeK j)) <| andB (allN 6 fun j => Nat.beq (XV j) (xvK j)) <|
    Nat.beq Q0 (q0K m)

@[expose] noncomputable def boundK (m b : Nat) (XE XV : Nat → Nat) (Q0 PQ A : Nat) : Bool :=
  orB (Nat.beq A 1) <|
  letB (Nat.rec (motive := fun _ => Nat) (Nat.sub (Nat.shiftLeft 1 512) 1)
      (fun i acc => Bool.rec (motive := fun _ => Nat) acc
        (letN (qlAt PQ i) fun a => Nat.land acc (fixE XE (bTabK m (tLo a) (tHi a)))) (hasB A i))
      (nat_lit 128)) fun FE =>
  letB (Nat.rec (motive := fun _ => Nat) Q0
      (fun i acc => Bool.rec (motive := fun _ => Nat) acc
        (Nat.land acc (fixV XV (qlAt PQ i))) (hasB A i)) (nat_lit 128)) fun FV =>
  Nat.blt (Nat.mul (Nat.mul (popN A 128) (popN FE 512)) (popN FV 64)) (Nat.shiftLeft 1 b)

@[expose] noncomputable def eaK (m b : Nat) (XE XV : Nat → Nat) (Q0 PQ : Nat)
    (IV IVI CM EL par ext : List Nat) (k : Nat) : Bool :=
  letB (nthN EL k) fun A =>
  andB (Bool.rec (motive := fun _ => Bool)
      (letB (nthN par k) fun p => letB (nthN ext k) fun x => andB (Nat.blt p k)
        (anyN (lenN IV) fun t => andB (Nat.beq (nthN IV t) x)
          (andB (notB (hasB (nthN EL p) (nthN IVI t))) (andB (Nat.beq (Nat.land (nthN EL p)
            (Nat.xor (nthN CM t) (nat_lit 340282366920938463463374607431768211455))) 0)
            (Nat.beq (adjK PQ x (nthN EL p)) A)))))
      (Nat.beq A 1) (Nat.beq k 0)) <|
  andB (Nat.blt A (Nat.shiftLeft 1 128)) <| andB (hasB A 0) <|
  andB (allN (lenN IV) fun t => extOK PQ A IVI CM EL (nthN IV t) t) <|
    boundK m b XE XV Q0 PQ A

@[expose] noncomputable def eaChunk (m b : Nat) (XE XV : Nat → Nat) (Q0 PQ : Nat)
    (IV IVI CM EL par ext : List Nat) (lo n : Nat) : Bool :=
  allN n fun d => impB (Nat.blt (Nat.add lo d) (lenN EL))
    (eaK m b XE XV Q0 PQ IV IVI CM EL par ext (Nat.add lo d))

end CFSG.KC.Misc.Sp6

end
