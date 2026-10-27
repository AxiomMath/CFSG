module

public import Certificates.Data.Kernel.KDenseP.Chunk

public section

namespace CFSG.KC.KDenseP

open CFSG.KC CFSG.KC.MonsterConv.Perm CFSG.KC.Loop CFSG.KC.KDense
open CFSG.Monster.AxisCount

@[expose] noncomputable def monoKeyStepL (n : Nat) (MT : MonoTab) (look : List Nat → Bool × Nat)
    (ok : Bool) (key : List Nat) (X A W : Nat) : St :=
  Prod.rec (motive := fun _ => St) (fun f k => (andB ok f, monoStepN n (MT.ents k) X A W)) (look key)

@[expose] noncomputable def stepNL (n lg : Nat) (F : Fix) (MT : MonoTab) (look : List Nat → Bool × Nat)
    (g : Native.Gen) (s : St) : St :=
  Prod.rec (motive := fun _ => St) (fun ok r => Prod.rec (motive := fun _ => St) (fun X r2 =>
    Prod.rec (motive := fun _ => St) (fun A W =>
      Native.Gen.rec (motive := fun _ => St)
        (fun q => Prod.rec (motive := fun _ => St) (fun qs r3 => Prod.rec (motive := fun _ => St)
          (fun qa qd => Prod.rec (motive := fun _ => St) (fun f r4 => (andB ok f, r4))
            (rhoStepN n F (Bool.rec (motive := fun _ => Nat) (nat_lit 0) (nat_lit 1) qs) qa qd X A W)) r3) q)
        (fun arr => monoKeyStepL n MT look ok (arrList arr) X A W)
        (fun a => monoKeyStepL n MT look ok [a] X A W)
        (Prod.rec (motive := fun _ => St) (fun X' r5 => (ok, X', r5)) (xiStepN n lg F X A W))
        (Prod.rec (motive := fun _ => St) (fun X' r5 => (ok, X', r5)) (tauStepN n lg F X A W)) g) r2) r) s

@[expose] noncomputable def runNL (n lg : Nat) (F : Fix) (MT : MonoTab) (look : List Nat → Bool × Nat)
    (w : List Native.Gen) (i m : Nat) (s : St) : St :=
  List.rec (motive := fun _ => Nat → Nat → St → St) (fun _ _ t => t)
    (fun g _ ih i' m' t => Bool.rec (motive := fun _ => St)
      (Bool.rec (motive := fun _ => St)
        (forceSt (stepNL n lg F MT look g t) (fun t' => ih i' (Nat.sub m' (nat_lit 1)) t')) t
        (Nat.beq m' (nat_lit 0)))
      (ih (Nat.sub i' (nat_lit 1)) m' t) (Nat.blt (nat_lit 0) i')) w i m s

@[expose] noncomputable def chunkOKNL (n lg q : Nat) (F : Fix) (MT : MonoTab)
    (look : List Nat → Bool × Nat) (words : Nat → List Native.Gen) (S : Nat → St) (c : Nat) : Bool :=
  Bool.rec (motive := fun _ => Bool)
    (stEqN n (runNL n lg F MT look (words (f20 c (nat_lit 0))) (f20 c (nat_lit 1)) (f20 c (nat_lit 2))
      (S (f20 c (nat_lit 3)))) (S (f20 c (nat_lit 4))))
    ((fun s t => andB (Nat.blt (f20 c (nat_lit 1)) SX) (andB (flagOf s) (andB (flagOf t)
        (notB (Nat.beq (resXq n q s (f20 c (nat_lit 1))) (resXq n q t (f20 c (nat_lit 1))))))))
      (S (f20 c (nat_lit 3))) (S (f20 c (nat_lit 4))))
    (Nat.beq (f20 c (nat_lit 5)) (nat_lit 1))

theorem chunkOKNL_findIdx (n lg q : Nat) (F : Fix) (MT : MonoTab) (words : Nat → List Native.Gen)
    (S : Nat → St) (c : Nat) :
    chunkOKNL n lg q F MT (fun k => findIdx k MT.keys) words S c = chunkOKN n lg q F MT words S c :=
  rfl

@[expose] noncomputable def kcode (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun a _ acc => Nat.add (Nat.add a (nat_lit 1)) (Nat.mul (nat_lit 32) acc)) l

@[expose] noncomputable def kok (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ acc => andB (Nat.blt a (nat_lit 31)) acc) l

@[expose] noncomputable def fldW (T w i : Nat) : Nat :=
  Nat.land (Nat.shiftRight T (Nat.mul w i)) (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))

@[expose] noncomputable def bsr (SC N x b : Nat) : Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat) (fun p => p)
    (fun j ih p => (fun r => ih (Bool.rec (motive := fun _ => Nat) p r
        (andB (Nat.blt r N) (Nat.ble (fldW SC (nat_lit 128) r) x))))
      (Nat.add p (Nat.shiftLeft (nat_lit 1) j))) b

@[expose] noncomputable def lookT (CT SC PI N : Nat) (ks : List (List Nat)) (l : List Nat) : Bool × Nat :=
  (fun c i => Bool.rec (motive := fun _ => Bool × Nat) (findIdx l ks) (true, i)
      (andB (Nat.blt i N) (andB (kok l) (Nat.beq (fldW CT (nat_lit 128) i) c))))
    (kcode l) (fldW PI (nat_lit 11) (bsr SC N (kcode l) (nat_lit 11) (nat_lit 0)))

@[expose] noncomputable def tabChk (CT SC PI N : Nat) (ks : List (List Nat)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun k _ ih j => andB (andB (kok k) (andB (Nat.beq (fldW CT (nat_lit 128) j) (kcode k))
        (Nat.beq (fldW PI (nat_lit 11) (bsr SC N (kcode k) (nat_lit 11) (nat_lit 0))) j)))
      (ih (Nat.add j (nat_lit 1)))) ks

end CFSG.KC.KDenseP

end
