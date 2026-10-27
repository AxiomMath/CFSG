module

public import Certificates.Data.Kernel.Misc.BfsK
public import Certificates.Data.Kernel.Sp62Twin

public section

namespace CFSG.KD.Sp6Over

open CFSG.KC.Loop CFSG.KC.Ord CFSG.KC.LQT.P CFSG.KC.Misc.G24 CFSG.KD.Sp62

@[expose] noncomputable def mskN (n : Nat) : Nat := Nat.sub (Nat.shiftLeft 1 n) 1

@[expose] noncomputable def bitN (x i : Nat) : Nat := Nat.land (Nat.shiftRight x i) 1

@[expose] noncomputable def lk16 (x i : Nat) : Nat :=
  Nat.land (Nat.shiftRight x (Nat.mul 16 i)) 65535

@[expose] noncomputable def mulC (n A B : Nat) : Nat := mulF2 n B A

@[expose] noncomputable def mvC (n A v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.xor acc
    (Nat.mul (bitN v j) (Nat.land (Nat.shiftRight A (Nat.mul n j)) (mskN n)))) n

@[expose] noncomputable def trC (n x : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun t acc => Nat.lor acc
    (Nat.shiftLeft (bitN x t) (Nat.add (Nat.mul n (Nat.mod t n)) (Nat.div t n)))) (Nat.mul n n)

@[expose] noncomputable def ONE7 : Nat := 282578800148737

@[expose] noncomputable def powM (mul : Nat → Nat → Nat) (one x k : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) one (fun _ acc => mul acc x) k

@[expose] noncomputable def wordM (mul : Nat → Nat → Nat) (one : Nat) (G : Nat → Nat)
    (len v : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun _ => one)
    (fun _ ih v => mul (G (Nat.land v 3)) (ih (Nat.shiftRight v 2))) len v

@[expose] noncomputable def wordW (mul : Nat → Nat → Nat) (one : Nat) (G : Nat → Nat) (w : Nat) :
    Nat :=
  wordM mul one G (Nat.land w 15) (Nat.shiftRight w 4)

@[expose] noncomputable def relOK (mul : Nat → Nat → Nat) (one : Nat) (G : Nat → Nat) (r : Nat) :
    Bool :=
  letB (wordW mul one G (Nat.shiftRight r 4)) fun W =>
    Nat.beq (powM mul one W (Nat.land r 15)) one

@[expose] noncomputable def allUp (m : Nat) (f : Nat → Bool) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih i => andB (f i) (ih (Nat.succ i))) m 0

@[expose] noncomputable def gen3 (A B C s : Nat) : Nat :=
  nIf(Nat.beq s 0, A, nIf(Nat.beq s 1, B, C))

@[expose] noncomputable def fA (i : Nat) : Nat :=
  Nat.lor (Nat.land i 3) (Nat.shiftLeft (bitN i 2) 4)

@[expose] noncomputable def wV (j : Nat) : Nat :=
  Nat.xor (Nat.xor (Nat.mul (bitN j 0) 4) (Nat.mul (bitN j 1) 8))
    (Nat.xor (Nat.mul (bitN j 2) 48) (Nat.mul (bitN j 3) 80))

@[expose] noncomputable def wCo (c : Nat) : Nat :=
  Nat.lor (Nat.lor (bitN c 2) (Nat.shiftLeft (bitN c 3) 1))
    (Nat.lor (Nat.shiftLeft (bitN c 5) 2) (Nat.shiftLeft (bitN c 6) 3))

@[expose] noncomputable def cand (N2 a u b v : Nat) : Nat :=
  Nat.lor 1 (Nat.lor (Nat.shiftLeft a 7) (Nat.lor (Nat.shiftLeft u 14)
    (Nat.lor (Nat.shiftLeft (mvC 7 N2 u) 21) (Nat.lor (Nat.shiftLeft b 28)
      (Nat.lor (Nat.shiftLeft (Nat.xor v b) 35) (Nat.shiftLeft (Nat.xor (mvC 7 N2 v) b) 42))))))

@[expose] noncomputable def fix6 (C x : Nat) : Bool :=
  Nat.beq (Nat.rec (motive := fun _ => Nat) x (fun _ y => mvC 7 C y) 6) x

@[expose] noncomputable def blockA (N2 i : Nat) : Bool :=
  letB (cand N2 (fA (Nat.div i 8)) 0 (fA (Nat.mod i 8)) 0) fun C => andB (fix6 C 2) (fix6 C 16)

@[expose] noncomputable def blockB (N2 j : Nat) : Bool :=
  letB (cand N2 0 (wV (Nat.div j 16)) 0 (wV (Nat.mod j 16))) fun C =>
    andB (fix6 C 4) (andB (fix6 C 8) (andB (fix6 C 48) (fix6 C 80)))

@[expose] noncomputable def maskOf (m : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0
    (fun i acc => Nat.lor acc (nIf(f i, Nat.shiftLeft 1 i, 0))) m

@[expose] noncomputable def bitB (M i : Nat) : Bool := Nat.beq (bitN M i) 1

@[expose] noncomputable def relsK (R : Nat → Nat) (NG NH C : Nat) : Bool :=
  allUp 13 fun i => relOK (mulC 7) ONE7 (gen3 NG NH C) (R (Nat.add 21 i))

@[expose] noncomputable def pinK (R : Nat → Nat) : Bool :=
  letB (R 17) fun NG => letB (R 18) fun NH => letB (R 19) fun XS => letB (R 20) fun XI =>
  letB (mulC 7 NH NH) fun N2 =>
  andB (allN 128 fun c => impB (Nat.beq (mvC 7 N2 c) c) (Nat.beq (Nat.land c 108) 0))
  (andB (allN 128 fun c =>
      impB (Nat.beq (mvC 7 N2 (mvC 7 N2 c)) (Nat.xor c (mvC 7 N2 c))) (Nat.beq (wV (wCo c)) c))
    (letB (maskOf 64 (blockA N2)) fun MA => letB (maskOf 256 (blockB N2)) fun MW =>
      allN 64 fun i => impB (bitB MA i) (allN 256 fun j => impB (bitB MW j)
        (letB (cand N2 (fA (Nat.div i 8)) (wV (Nat.div j 16)) (fA (Nat.mod i 8))
            (wV (Nat.mod j 16))) fun C =>
          orB (notB (relsK R NG NH C)) (orB (Nat.beq C XS) (Nat.beq C XI))))))

@[expose] noncomputable def posL0 : List Nat := [1, 2, 3, 4, 5]

@[expose] noncomputable def posL1 : List Nat := [8, 9, 10, 11, 15]

@[expose] noncomputable def posL2 : List Nat := [16, 17, 22, 23, 29]

@[expose] noncomputable def symL (l : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun q _ ih => Nat.lor (bitN x q) (Nat.shiftLeft ih 1)) l

@[expose] noncomputable def sym15 (x : Nat) : Nat :=
  Nat.lor (symL posL0 x) (Nat.lor (Nat.shiftLeft (symL posL1 x) 5)
    (Nat.shiftLeft (symL posL2 x) 10))

@[expose] noncomputable def basQ (q : Nat) : Nat :=
  Nat.lor (Nat.shiftLeft 1 q) (Nat.shiftLeft 1 (Nat.add (Nat.mul 6 (Nat.mod q 6)) (Nat.div q 6)))

@[expose] noncomputable def imgF (P Q q : Nat) : Nat := sym15 (MULF (MULF P (basQ q)) Q)

@[expose] noncomputable def rep16 (m : Nat) : Nat :=
  Nat.div (Nat.sub (Nat.shiftLeft 1 (Nat.mul 16 m)) 1) 65535

@[expose] noncomputable def tabL (P Q : Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun t _ => t)
    (fun q _ ih t m => ih (Nat.lor t (Nat.shiftLeft (Nat.xor t (Nat.mul (imgF P Q q) (rep16 m)))
      (Nat.mul 16 m))) (Nat.mul 2 m)) l 0 1

@[expose] noncomputable def tabs (P : Nat) : Nat :=
  strictN (trC 6 P) fun Q => Nat.lor (tabL P Q posL0)
    (Nat.lor (Nat.shiftLeft (tabL P Q posL1) 512) (Nat.shiftLeft (tabL P Q posL2) 1024))

@[expose] noncomputable def lkT (T m v : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.add (Nat.mul 512 m) (Nat.mul 16 v))) 65535

@[expose] noncomputable def actT (T s c : Nat) : Nat :=
  Nat.xor (lkT T (Nat.mul 3 s) (Nat.land c 31))
    (Nat.xor (lkT T (Nat.add (Nat.mul 3 s) 1) (Nat.land (Nat.shiftRight c 5) 31))
      (lkT T (Nat.add (Nat.mul 3 s) 2) (Nat.shiftRight c 10)))

@[expose] noncomputable def packL (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun x _ ih => Nat.lor x (Nat.shiftLeft ih 16)) l

@[expose] noncomputable def M64 : Nat := 18446744073709551615

@[expose] noncomputable def addC (c bits p rc : Nat) (K : Nat → Nat → Nat → Bool) : Bool :=
  andB (Nat.blt 0 c) (andB (Nat.beq (Nat.land bits (Nat.shiftLeft 1 (Nat.add c 64))) 0)
    (letB (Nat.add (Nat.lor bits (Nat.shiftLeft 1 (Nat.add c 64))) 1) fun b' =>
      letB p fun p' => K p' b' rc))

@[expose] noncomputable def walkStep (TAB ROOTS ST r path bits rc : Nat)
    (K : Nat → Nat → Nat → Bool) : Bool :=
  letB (Nat.land r 63) fun d =>
    bIf(Nat.beq d 0,
      andB (Nat.blt rc 6) (andB (Nat.beq (Nat.land bits M64) (lk16 ST rc))
        (letB (lk16 ROOTS rc) fun c => addC c bits c (Nat.succ rc) K)),
      letB (Nat.shiftRight r 6) fun s => andB (Nat.blt s 3)
        (letB (actT TAB s (lk16 path (Nat.pred d))) fun c =>
          addC c bits (Nat.lor (Nat.land path (mskN (Nat.mul 16 d)))
            (Nat.shiftLeft c (Nat.mul 16 d))) rc K))

@[expose] noncomputable def walkChunk (TAB ROOTS ST : Nat) (K : Nat → Nat → Nat → Bool) :
    Nat → Nat → Nat → Nat → Bool :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat → Bool) (fun _ path bits rc => K path bits rc)
    (fun _ ih ch path bits rc => walkStep TAB ROOTS ST (Nat.land ch 255) path bits rc
      (fun p b c => ih (Nat.shiftRight ch 8) p b c)) 64

@[expose] noncomputable def walkAll (TAB ROOTS ST : Nat) (F : List Nat)
    (K : Nat → Nat → Nat → Bool) : Nat → Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Nat → Bool) K
    (fun ch _ ih path bits rc => walkChunk TAB ROOTS ST ih ch path bits rc) F

@[expose] noncomputable def rootsOf (R : Nat → Nat) (W0 : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) W0 (fun r acc => Nat.lor acc
    (Nat.shiftLeft (actT (tabs (R (Nat.add 3 r))) 0 W0) (Nat.mul 16 (Nat.succ r)))) 5

@[expose] noncomputable def formK (R : Nat → Nat) (F : List Nat) (ST : Nat) : Bool :=
  letB (R 16) fun W0 =>
  letB (Nat.lor (tabs (R 0)) (Nat.lor (Nat.shiftLeft (tabs (R 1)) 1536)
    (Nat.shiftLeft (tabs (R 2)) 3072))) fun TAB =>
  andB (allN 3 fun s => Nat.beq (actT TAB s W0) W0)
  (andB (allN 8 fun m => andB (Nat.beq (mulC 6 (R m) (R (Nat.add 8 m))) (oneF2 6))
      (Nat.beq (mulC 6 (R (Nat.add 8 m)) (R m)) (oneF2 6)))
    (letB (rootsOf R W0) fun ROOTS =>
      walkAll TAB ROOTS ST F (fun _ bits rc =>
        andB (Nat.beq rc 6) (Nat.beq (Nat.land bits M64) (lk16 ST 6))) 0 0 0))

@[expose] noncomputable def h6K (R : Nat → Nat) : Bool :=
  letB (R 34) fun A => letB (R 36) fun B => letB (R 38) fun C =>
  letB (wordW MULF ONE (gen3 A B C) (R 56)) fun Y =>
  andB (andB (pairN A (R 35) (trC 6 A)) (andB (pairN B (R 37) (trC 6 B))
      (pairN C (R 39) (trC 6 C))))
    (andB (allUp 13 fun i => relOK MULF ONE (gen3 A B C) (R (Nat.add 21 i)))
    (andB (andB (Nat.beq (PW A 7) ONE) (andB (notB (Nat.beq A ONE)) (Nat.beq (PW B 6) ONE)))
    (andB (andB (Nat.beq (MULF B A) (MULF (PW A 3) B))
        (Nat.beq (MULF C (MULF B B)) (MULF (MULF B B) C)))
    (andB (allN 8 fun i => Nat.beq (wordW MULF ONE (gen3 A B C) (R (Nat.add 48 i)))
        (R (Nat.add 40 i)))
      (andB (Nat.beq (PW Y 5) ONE) (notB (Nat.beq Y ONE)))))))

@[expose] noncomputable def kcK (m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) ONE7
    (fun j acc => Nat.lor acc (Nat.shiftLeft (bitN m j) (Nat.mul 7 (Nat.succ j)))) 6

@[expose] noncomputable def cntN (m : Nat) (f : Nat → Bool) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun i acc => nIf(f i, Nat.succ acc, acc)) m

@[expose] noncomputable def conjSt (NG NH X NGI NHI XI x s : Nat) : Nat :=
  mulC 7 (mulC 7 (gen3 NG NH X s) x) (gen3 NGI NHI XI s)

@[expose] noncomputable def gen5 (A B C D E s : Nat) : Nat :=
  nIf(Nat.beq s 0, A, nIf(Nat.beq s 1, B, nIf(Nat.beq s 2, C, nIf(Nat.beq s 3, D, E))))

@[expose] noncomputable def caseK (R : Nat → Nat) (X kO kW rO n : Nat) : Bool :=
  letB (R 17) fun NG => letB (R 18) fun NH =>
  letB (powM (mulC 7) ONE7 NG 6) fun NGI => letB (powM (mulC 7) ONE7 NH 5) fun NHI =>
  letB (powM (mulC 7) ONE7 X 5) fun XI =>
  letB (wordW (mulC 7) ONE7 (gen3 NG NH X) (R 49)) fun Z =>
  letB (wordW (mulC 7) ONE7 (gen3 NG NH X) (R 57)) fun P1 =>
  letB (kcK 6) fun K6 => letB (kcK 8) fun K8 => letB (kcK 17) fun K17 => letB (kcK 33) fun K33 =>
  andB (allN 3 fun s => andB (Nat.beq (mulC 7 (gen3 NG NH X s) (gen3 NGI NHI XI s)) ONE7)
      (Nat.beq (mulC 7 (gen3 NGI NHI XI s) (gen3 NG NH X s)) ONE7))
  (andB (Nat.beq (CFSG.KD.BfsK.recX R kO 0) (kcK 1))
  (andB (buildG (conjSt NG NH X NGI NHI XI) (CFSG.KD.BfsK.recX R kO) (CFSG.KD.BfsK.recF R kO 0)
      (CFSG.KD.BfsK.recF R kO 1) n 3 1)
  (andB (allN 63 fun m => letB (R (Nat.add kW (Nat.succ m))) fun p =>
      andB (Nat.blt p n) (Nat.beq (CFSG.KD.BfsK.recX R kO p) (kcK (Nat.succ m))))
  (andB (Nat.beq (cntN 128 fun v => Nat.beq (mvC 7 Z v) v) 32)
  (andB (allN 5 fun s => letB (gen5 K6 K8 K17 K33 P1 s) fun g =>
      Nat.beq (mulC 7 g Z) (mulC 7 Z g))
  (andB (allN 4 fun s => letB (gen5 K6 K8 K17 K33 P1 s) fun g => Nat.beq (mulC 7 g g) ONE7)
  (andB (Nat.beq (CFSG.KD.BfsK.recX R rO 0) ONE7)
    (CFSG.KD.BfsK.tableKk R (fun x s => mulC 7 x (gen5 K6 K8 K17 K33 P1 s)) rO 32 5 1 3 1))))))))

@[expose] noncomputable def kK (R : Nat → Nat) (n : Nat) : Bool :=
  andB (letB (R 19) fun X => caseK R X 61 125 189 n)
    (letB (R 20) fun X => caseK R X 222 286 350 n)

@[expose] noncomputable def piK (X : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) 0 (fun j acc => Nat.lor acc (Nat.shiftLeft
    (Nat.shiftRight (Nat.land (Nat.shiftRight X (Nat.mul 7 (Nat.succ j))) 127) 1)
    (Nat.mul 6 j))) 6

@[expose] noncomputable def uK (R : Nat → Nat) : Bool :=
  letB (wordW (mulC 6) ONE (gen3 (R 0) (R 1) (R 2)) (R 49)) fun Z =>
  letB (R 58) fun A => letB (R 59) fun B => letB (R 60) fun C =>
  andB (Nat.beq (piK (R 19)) (piK (R 20)))
  (andB (allN 3 fun s => letB (gen3 A B C s) fun g =>
      andB (Nat.beq (mulC 6 g g) ONE) (Nat.beq (mulC 6 g Z) (mulC 6 Z g)))
  (andB (Nat.beq (CFSG.KD.BfsK.recX R 383 0) ONE)
    (CFSG.KD.BfsK.tableKk R (fun x s => mulC 6 x (gen3 A B C s)) 383 32 3 1 2 1)))

end CFSG.KD.Sp6Over

end
