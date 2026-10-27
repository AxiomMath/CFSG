module

public import Certificates.Data.Kernel.Spor.Raw

public section

namespace CFSG.KC.Misc.RuInv

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw

@[expose] noncomputable def idP : Nat := pidn (nat_lit 4060) (nat_lit 12)

@[expose] noncomputable def mulP (p q : Nat) : Nat := pcomp (nat_lit 4060) (nat_lit 12) (nat_lit 4095) p q

@[expose] noncomputable def apP (p i : Nat) : Nat := pg (nat_lit 12) (nat_lit 4095) p i

@[expose] noncomputable def invP (p : Nat) : Nat :=
  foldN (nat_lit 4060) (fun i acc => Nat.lor acc (Nat.shiftLeft i (Nat.mul (nat_lit 12) (apP p i))))
    (nat_lit 0)

@[expose] noncomputable def powP (p e : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) idP (fun _ acc => strictN acc (fun a => mulP p a)) e

@[expose] noncomputable def readS (s : List (Nat × Nat)) (k : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) idP (fun q _ ih => nIf(Nat.beq q.1 k, q.2, ih)) s

@[expose] noncomputable def stepS (s : List (Nat × Nat)) (r : Nat × Nat × Nat × Nat) :
    List (Nat × Nat) :=
  Bool.rec (motive := fun _ => List (Nat × Nat))
    (Bool.rec (motive := fun _ => List (Nat × Nat))
      (List.cons (r.2.2.2, powP (readS s r.2.2.1) r.2.1) s)
      (List.cons (r.2.2.1, invP (readS s r.2.1)) s) (Nat.beq r.1 (nat_lit 1)))
    (List.cons (r.2.2.2, mulP (readS s r.2.1) (readS s r.2.2.1)) s) (Nat.beq r.1 (nat_lit 0))

@[expose] noncomputable def slotK (rows : List (Nat × Nat × Nat × Nat)) (t₁ t₂ : Nat) : Nat × Nat :=
  (fun s => (readS s 1, readS s 2))
    (List.rec (motive := fun _ => List (Nat × Nat) → List (Nat × Nat)) (fun s => s)
      (fun r _ ih s => ih (stepS s r)) rows [(1, t₁), (2, t₂)])

@[expose] noncomputable def conjP (g gi x : Nat) : Nat := mulP (mulP g x) gi

@[expose] noncomputable def hkeyP (x : Nat) : Nat :=
  foldN (nat_lit 64) (fun q h => strictN (fld(x, Nat.mul (nat_lit 768) (Nat.sub (nat_lit 63) q),
      mask (nat_lit 768))) (fun c =>
    Nat.rec (motive := fun _ => Nat → Nat) (fun h => h)
      (fun j ih h => strictN (Nat.add (Nat.mul (nat_lit 64) (Nat.sub (nat_lit 63) q)) (Nat.sub (nat_lit 63) j))
        (fun i => ih (nIf(Nat.blt i (nat_lit 4060),
          Nat.land (Nat.mul (Nat.xor h (fld(c, Nat.mul (nat_lit 12) (Nat.sub (nat_lit 63) j),
            nat_lit 4095))) (nat_lit 1099511628211)) (mask (nat_lit 64)), h))))
      (nat_lit 64) h))
    (nat_lit 14695981039346656037)

@[expose] noncomputable def at11 (X k : Nat) : Nat := fld(X, Nat.mul (nat_lit 11) k, nat_lit 2047)

@[expose] noncomputable def conjK (E G GI : Nat → Nat) (nx s N lo cnt : Nat) : Bool :=
  allN cnt (fun d => strictB (Nat.add lo d) (fun j => strictB (E j) (fun e =>
    allN 2 (fun l => strictB (at11 nx (Nat.add (Nat.mul 2 j) l)) (fun k =>
      bAnd(Nat.ble s k, bAnd(Nat.blt k (Nat.add s N),
        Nat.beq (conjP (G l) (GI l) e) (E k))))))))

@[expose] noncomputable def reachK (nx s N : Nat) : Bool :=
  (fun r => Nat.beq r (Nat.sub (Nat.shiftLeft (nat_lit 1) N) (nat_lit 1)))
  (foldN N (fun d seen => strictN (Nat.sub (Nat.sub N (nat_lit 1)) d) (fun i =>
      nIf(Nat.beq (Nat.land (Nat.shiftRight seen i) (nat_lit 1)) (nat_lit 1),
        Nat.lor seen (Nat.lor
          (Nat.shiftLeft (nat_lit 1) (Nat.sub (at11 nx (Nat.mul 2 (Nat.add s i))) s))
          (Nat.shiftLeft (nat_lit 1) (Nat.sub (at11 nx (Nat.succ (Nat.mul 2 (Nat.add s i)))) s))),
        nat_lit 0)))
    (nat_lit 1))

@[expose] noncomputable def keysK (Hs : Nat → Nat) (P n : Nat) : Bool :=
  bAnd(allN (Nat.sub n (nat_lit 1)) (fun i => Nat.blt (Hs (at11 P i)) (Hs (at11 P (Nat.succ i)))),
  bAnd(allN n (fun i => Nat.blt (at11 P i) n),
    Nat.beq (foldN n (fun i s => Nat.lor s (Nat.shiftLeft (nat_lit 1) (at11 P i))) (nat_lit 0))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) n) (nat_lit 1))))

@[expose] noncomputable def hashE (E Hs : Nat → Nat) (j : Nat) : Bool :=
  bIf(Nat.blt j 1391, Nat.beq (hkeyP (E j)) (Hs j), true)

@[expose] noncomputable def covOne (E : Nat → Nat) (T0 T1 h : Nat) : Bool :=
  bIf(Nat.blt h (nat_lit 1391),
    Nat.beq (E h) (mulP T0 T1),
  bIf(Nat.blt h (nat_lit 5451),
    strictB (Nat.sub h (nat_lit 1391)) (fun x =>
      bIf(Nat.beq (apP T0 (apP T1 (apP T0 (apP T1 x)))) x, false, true)),
    bIf(Nat.beq (foldN (nat_lit 4060) (fun x c => nIf(Nat.beq (apP T0 (apP T1 x)) x, Nat.succ c, c))
      (nat_lit 0)) (nat_lit 92), false, true)))

@[expose] noncomputable def covK (LR TR E : Nat → Nat) (V vb lo cnt : Nat) : Bool :=
  strictB (LR 0) (fun R0 => strictB (LR 1) (fun R1 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) R0) (fun o0 =>
  strictB (roff (nat_lit 4060) (nat_lit 48720) R1) (fun o1 =>
  allN cnt (fun d => strictB (Nat.add lo d) (fun a => strictB (TR (Nat.add o0 a)) (fun T0 =>
    allN 8 (fun b => strictB (TR (Nat.add o1 b)) (fun T1 =>
      covOne E T0 T1 (fld(V, Nat.mul (nat_lit 14) (Nat.add (Nat.mul 8 (Nat.sub a vb)) b),
        nat_lit 16383)))))))))))

@[expose] noncomputable def clsLo (j : Nat) : Nat :=
  nIf(Nat.blt j 1, 0, nIf(Nat.blt j 31, 1, nIf(Nat.blt j 271, 31, nIf(Nat.blt j 751, 271, 751))))

@[expose] noncomputable def clsHi (j : Nat) : Nat :=
  nIf(Nat.blt j 1, 1, nIf(Nat.blt j 31, 31, nIf(Nat.blt j 271, 271, nIf(Nat.blt j 751, 751, 1391))))

@[expose] noncomputable def gen2 (a b l : Nat) : Nat := nIf(Nat.beq l 0, a, b)

@[expose] noncomputable def conjE (E G GI : Nat → Nat) (nx j : Nat) : Bool :=
  bIf(Nat.blt j 1391, conjK E G GI nx (clsLo j) (Nat.sub (clsHi j) (clsLo j)) j 1, true)

@[expose] noncomputable def covA (LR TR E V : Nat → Nat) (a : Nat) : Bool :=
  bIf(Nat.blt a 2048,
    covK LR TR E (V (Nat.shiftRight a 5)) (Nat.mul 32 (Nat.shiftRight a 5)) a 1, true)

@[expose] noncomputable def wordP (G GI : Nat → Nat) (w : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) idP (fun l _ acc => strictN acc (fun a =>
    mulP (Int.rec (motive := fun _ => Nat) (fun k => G (Nat.sub k 1)) (fun k => GI k) l) a)) w

@[expose] def cprogK : List (Nat × Nat × Nat × Nat) :=
  [(0, 1, 2, 3), (0, 3, 2, 4), (0, 3, 4, 5), (0, 3, 5, 6), (0, 6, 3, 7), (0, 7, 4, 8), (1, 5, 6, 0),
   (0, 6, 1, 9), (0, 9, 5, 10), (0, 3, 8, 1), (2, 10, 1, 9), (0, 9, 10, 8), (2, 6, 8, 11),
   (0, 7, 7, 8), (1, 8, 7, 0), (0, 7, 10, 6), (0, 6, 8, 10), (0, 9, 10, 8), (2, 4, 8, 12),
   (0, 11, 12, 2)]

end CFSG.KC.Misc.RuInv

end
