module

public import CFSG.Certificates.Kernel.Common.Loop

public section

namespace CFSG.KC.WE8K

open CFSG.KC.Loop

@[expose] noncomputable def byteAt (T i : Nat) : Nat := fld(T, Nat.shiftLeft i (nat_lit 3), nat_lit 255)

@[expose] noncomputable def colK (P N D M j cj x i : Nat) : Nat :=
  nIf(Nat.beq i j, byteAt N (byteAt P (Nat.add (Nat.mul (nat_lit 240) j) cj)),
    nIf(Nat.beq (fld(M, Nat.add (Nat.shiftLeft j (nat_lit 3)) i, nat_lit 1)) (nat_lit 1),
      byteAt P (Nat.add (Nat.mul (nat_lit 240) j)
        (byteAt D (Nat.add (Nat.mul (nat_lit 240) (byteAt x i)) cj))),
      byteAt P (Nat.add (Nat.mul (nat_lit 240) j) (byteAt x i))))

@[expose] noncomputable def conjK (P N D M j x : Nat) : Nat :=
  strictN (byteAt x j) fun cj =>
    Nat.rec (motive := fun _ => Nat) (nat_lit 0)
      (fun i acc => Nat.lor (Nat.shiftLeft (colK P N D M j cj x i) (Nat.shiftLeft i (nat_lit 3))) acc)
      (nat_lit 8)

@[expose] noncomputable def strictL (y : Nat) (k : Nat → List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def kidsK (P N D M x m : Nat) (acc : List Nat) : List Nat :=
  Nat.rec (motive := fun _ => List Nat) acc
    (fun j ih => Bool.rec (motive := fun _ => List Nat) ih
      (strictL (conjK P N D M j x) fun y => y :: ih)
      (Nat.beq (fld(m, j, nat_lit 1)) (nat_lit 1))) (nat_lit 8)

@[expose] noncomputable def nextK (P N D M : Nat) (L : List Nat) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih m => kidsK P N D M x (Nat.land m (nat_lit 255)) (ih (Nat.shiftRight m (nat_lit 8)))) L

@[expose] noncomputable def appK (L R : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) R (fun x _ ih => x :: ih) L

@[expose] noncomputable def orbK (P N D M : Nat) (Ms : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun L => L)
    (fun m _ ih L => appK L (ih (nextK P N D M L m))) Ms

@[expose] noncomputable def mergeK (xs : List Nat) : List Nat → List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun ys => ys)
    (fun x _ ih ys => List.rec (motive := fun _ => List Nat) (x :: ih [])
      (fun y ys' w => Bool.rec (motive := fun _ => List Nat) (x :: ih (y :: ys')) (y :: w)
        (Nat.blt y x)) ys) xs

@[expose] noncomputable def pairsK (ls : List (List Nat)) : List (List Nat) :=
  List.rec (motive := fun _ => List Nat → Bool → List (List Nat))
    (fun h b => Bool.rec (motive := fun _ => List (List Nat)) [] [h] b)
    (fun l _ ih h b => Bool.rec (motive := fun _ => List (List Nat)) (ih l true)
      (mergeK h l :: ih [] false) b) ls [] false

@[expose] noncomputable def singlesK (L : List Nat) : List (List Nat) :=
  List.rec (motive := fun _ => List (List Nat)) [] (fun x _ ih => [x] :: ih) L

@[expose] noncomputable def headK (ls : List (List Nat)) : List Nat :=
  List.rec (motive := fun _ => List Nat) [] (fun l _ _ => l) ls

@[expose] noncomputable def sortK (L : List Nat) : List Nat :=
  headK (Nat.rec (motive := fun _ => List (List Nat) → List (List Nat)) (fun ls => ls)
    (fun _ ih ls => ih (pairsK ls)) (nat_lit 18) (singlesK L))

@[expose] noncomputable def strictLen (L : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun x _ ih lo c => nIf(Nat.ble lo x, strictN (Nat.succ c) (ih (Nat.succ x)), nat_lit 0)) L

@[expose] noncomputable def orbOK (P N D M s : Nat) (Ms : List Nat) (n : Nat) : Bool :=
  Nat.beq (strictLen (sortK (orbK P N D M Ms [s])) (nat_lit 0) (nat_lit 0)) n

@[expose] noncomputable def segK (X n : Nat) : Nat :=
  fld(X, Nat.add (nat_lit 64) (Nat.mul (nat_lit 240) n),
    Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 240)) (nat_lit 1))

@[expose] noncomputable def cutK (X R : Nat) : Nat :=
  Nat.xor (Nat.land X R) (Nat.land (Nat.add (Nat.mul (Nat.land X (nat_lit 0xFFFFFFFFFFFFFFFF))
    (nat_lit 0x9E3779B97F4A7C15)) (Nat.land R (nat_lit 0xFFFFFFFFFFFFFFFF)))
    (nat_lit 0xFFFFFFFFFFFFFFFF))

@[expose] noncomputable def pop240 (x : Nat) : Nat :=
  (fun m1 m2 m4 o =>
    (fun a => (fun b => (fun c =>
      fld(Nat.mul c o, nat_lit 232, nat_lit 255))
        (Nat.land (Nat.add b (Nat.shiftRight b (nat_lit 4))) m4))
        (Nat.add (Nat.land a m2) (Nat.land (Nat.shiftRight a (nat_lit 2)) m2)))
      (Nat.sub x (Nat.land (Nat.shiftRight x (nat_lit 1)) m1)))
  (nat_lit 0x555555555555555555555555555555555555555555555555555555555555)
  (nat_lit 0x333333333333333333333333333333333333333333333333333333333333)
  (nat_lit 0x0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f)
  (nat_lit 0x010101010101010101010101010101010101010101010101010101010101)

@[expose] noncomputable def foldBits (f : Nat → Nat → Nat) : Nat → Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat → Nat)
    (fun x base acc => nIf(Nat.beq x (nat_lit 0), acc, f base acc))
    (fun d ih x base acc => nIf(Nat.beq x (nat_lit 0), acc,
      (fun w => strictN (ih (Nat.land x (Nat.sub (Nat.shiftLeft (nat_lit 1) w) (nat_lit 1))) base acc)
        fun a => ih (Nat.shiftRight x w) (Nat.add base w) a) (Nat.shiftLeft (nat_lit 1) d)))

@[expose] noncomputable def dfsK (Qs : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun n X => pop240 (segK X n))
    (fun Q _ ih n X => foldBits (fun b acc => Nat.add acc (ih (Nat.succ n)
        (cutK X (fld(Q, Nat.mul (nat_lit 1984) b,
          Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1984)) (nat_lit 1))))))
      (nat_lit 8) (segK X n) (nat_lit 0) (nat_lit 0)) Qs

@[expose] noncomputable def chunkK (Qs : List Nat) (X lo hi : Nat) : Nat :=
  dfsK Qs (nat_lit 0) (Nat.land X (Nat.add (Nat.sub (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 1984))
    (nat_lit 1)) (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) (nat_lit 240)) (nat_lit 1))
      (nat_lit 64)))
    (Nat.shiftLeft (Nat.sub (Nat.shiftLeft (nat_lit 1) hi) (Nat.shiftLeft (nat_lit 1) lo))
      (nat_lit 64))))

@[expose] noncomputable def nthN (ls : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun l _ ih k => Nat.rec (motive := fun _ => Nat) l (fun k' _ => ih k') k) ls

@[expose] noncomputable def nthL (ls : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun l _ ih k => Nat.rec (motive := fun _ => List Nat) l (fun k' _ => ih k') k) ls

@[expose] noncomputable def orbF (P N D M : Nat) (S : List Nat) (L : List (List Nat))
    (Ns : List Nat) (k : Nat) : Bool :=
  orbOK P N D M (nthN S k) (nthL L k) (nthN Ns k)

@[expose] noncomputable def symF (Qs : List Nat) (X B C k : Nat) : Bool :=
  Nat.beq (chunkK Qs X (byteAt B k) (byteAt B (Nat.succ k)))
    (fld(C, Nat.shiftLeft k (nat_lit 4), nat_lit 0xFFFF))

end CFSG.KC.WE8K

end
