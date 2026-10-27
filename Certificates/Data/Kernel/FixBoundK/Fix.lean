module

public import Certificates.Data.Kernel.FixBoundK.Member

public section

namespace CFSG.KC.FixBoundK

@[expose] noncomputable def bitS (x : Nat) : Bool := Nat.beq (Nat.land x (nat_lit 1)) (nat_lit 1)

@[expose] noncomputable def withN {α : Type} (y : Nat) (k : Nat → α) : α :=
  Nat.rec (motive := fun _ => α) (k (nat_lit 0)) (fun n _ => k (Nat.succ n)) y

@[expose] noncomputable def headS {α : Type} (d : α) (l : List α) : α :=
  List.rec (motive := fun _ => α) d (fun x _ _ => x) l

@[expose] noncomputable def tailS {α : Type} (l : List α) : List α :=
  List.rec (motive := fun _ => List α) [] (fun _ xs _ => xs) l

@[expose] noncomputable def actS (cs : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih x => nIf(Nat.beq x (nat_lit 0), nat_lit 0,
      Nat.xor (nIf(bitS x, c, nat_lit 0)) (ih (Nat.shiftRight x (nat_lit 1)))))
    cs x

@[expose] noncomputable def permS (g : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun a _ ih x => nIf(Nat.beq x (nat_lit 0), nat_lit 0,
      Nat.xor (nIf(bitS x, Nat.shiftLeft (nat_lit 1) a, nat_lit 0))
        (ih (Nat.shiftRight x (nat_lit 1)))))
    g x

@[expose] noncomputable def synK : List Nat :=
  [nat_lit 62, nat_lit 129, nat_lit 65, nat_lit 193, nat_lit 61, nat_lit 514, nat_lit 258,
    nat_lit 770, nat_lit 59, nat_lit 2052, nat_lit 1028, nat_lit 3076, nat_lit 55, nat_lit 2696,
    nat_lit 1352, nat_lit 4040, nat_lit 47, nat_lit 2896, nat_lit 1744, nat_lit 3472, nat_lit 31,
    nat_lit 2528, nat_lit 1952, nat_lit 3680]

@[expose] noncomputable def bmK : List Nat :=
  [nat_lit 1118494, nat_lit 1118689, nat_lit 1121809, nat_lit 1171729, nat_lit 1970449,
    nat_lit 14749969, nat_lit 10928140, nat_lit 7118858, nat_lit 6996160, nat_lit 13017248,
    nat_lit 13421568, nat_lit 11184640]

@[expose] noncomputable def omK : Nat := nat_lit 16777215

@[expose] noncomputable def synS (x : Nat) : Nat := actS synK x

@[expose] noncomputable def fixS (g : List Nat) (x : Nat) : Bool :=
  withN (Nat.xor (permS g x) x) (fun y => bIf(Nat.beq y (nat_lit 0), true, Nat.beq y omK))

@[expose] noncomputable def spanChk (B F : List Nat) (j₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool)
    (fun j => Nat.beq j (Nat.pow (nat_lit 2) (lenS B)))
    (fun f _ ih j => bAnd(Nat.beq f (actS B j), ih (Nat.succ j))) F j₀

@[expose] noncomputable def parV (fl : List Nat) (d s₀ : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun f _ ih s => Nat.lor (Nat.shiftLeft (par24 (Nat.land f d)) s) (ih (Nat.succ s))) fl s₀

@[expose] noncomputable def ycolS (gens : List (List Nat)) (yfT : List (List Nat)) (y : Nat) : Nat :=
  List.rec (motive := fun _ => List (List Nat) → Nat) (fun _ => nat_lit 0)
    (fun g _ ih fl => Nat.xor (withN (Nat.xor (permS g y) y) (fun d => parV (headS [] fl) d (nat_lit 0)))
      (ih (tailS fl)))
    gens yfT

@[expose] noncomputable def ysChk (gens : List (List Nat)) (yfT : List (List Nat)) (ys : List Nat)
    (t₀ : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun y _ ih t => bAnd(Nat.beq (ycolS gens yfT y) (Nat.shiftLeft (nat_lit 1) t), ih (Nat.succ t)))
    ys t₀

@[expose] noncomputable def remS (d : Nat) (l : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat) []
    (fun x _ ih => Bool.rec (motive := fun _ => List Nat) (x :: ih) ih (Nat.beq x d)) l

@[expose] noncomputable def mwsRem (gens : List (List Nat)) (Mws : List Nat) : List Nat :=
  List.rec (motive := fun _ => List Nat → List Nat) (fun rem => rem)
    (fun g _ ih rem => ih
      (List.rec (motive := fun _ => List Nat → List Nat) (fun rem => rem)
        (fun b _ ih2 rem => ih2 (withN (Nat.xor (permS g b) b) (fun d => remS d rem))) bmK rem))
    gens (remS omK Mws)

@[expose] noncomputable def dblS (x w n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun x _ => x)
    (fun _ ih x w => ih (Nat.lor x (Nat.shiftLeft x w)) (Nat.shiftLeft w (nat_lit 1))) n x w

@[expose] noncomputable def genD (K t w : Nat) : Nat :=
  dblS (Nat.shiftLeft (dblS (nat_lit 1) w t) (Nat.mul w (Nat.pow (nat_lit 2) t)))
    (Nat.mul w (Nat.pow (nat_lit 2) (Nat.succ t))) (Nat.sub K (Nat.succ t))

@[expose] noncomputable def idx12 : List Nat :=
  [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5, nat_lit 6, nat_lit 7,
    nat_lit 8, nat_lit 9, nat_lit 10, nat_lit 11]

@[expose] noncomputable def sprS (s W : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun b _ ih s => Nat.lor (nIf(bitS s, Nat.shiftLeft (nat_lit 1) (Nat.mul b W), nat_lit 0))
      (ih (Nat.shiftRight s (nat_lit 1))))
    idx12 s

@[expose] noncomputable def rowU (K W : Nat) (B : List Nat) (c t₀ : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun b _ ih t => Nat.xor (Nat.mul (genD K t (nat_lit 1)) (sprS (synS (Nat.land b c)) W))
      (ih (Nat.succ t)))
    B t₀

@[expose] noncomputable def synMat (K m W : Nat) (B : List Nat) (u₀ : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun c _ ih u => Nat.xor (Nat.mul (rowU K W B c (nat_lit 0)) (genD K u m)) (ih (Nat.succ u)))
    B u₀

@[expose] noncomputable def orLanes (x W : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0)
    (fun b _ ih => Nat.lor (Nat.land (Nat.shiftRight x (Nat.mul b W))
      (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1))) ih)
    idx12

@[expose] noncomputable def packS (bs : List Nat) (m j₀ : Nat) : Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => nat_lit 0)
    (fun b _ ih j => Nat.lor (Nat.shiftLeft b (Nat.mul m j)) (ih (Nat.succ j))) bs j₀

@[expose] noncomputable def basicsW (B bs : List Nat) (K m W : Nat) : Bool :=
  bAnd(Nat.beq (lenS bs) m,
  bAnd(allS (fun b => Nat.beq (Nat.land b (Nat.sub (Nat.shiftLeft (nat_lit 1) m) (nat_lit 1))) b) bs,
    withN (synMat K m W B (nat_lit 0)) (fun x =>
      Nat.beq (Nat.xor (packS bs m (nat_lit 0)) (orLanes x W))
        (Nat.sub (Nat.shiftLeft (nat_lit 1) W) (nat_lit 1)))))

@[expose] noncomputable def basicsOK (B bs : List Nat) : Bool :=
  withN (lenS B) (fun K => withN (Nat.pow (nat_lit 2) K) (fun m =>
    withN (Nat.mul m m) (fun W => basicsW B bs K m W)))

abbrev FixD := List Nat × List Nat × List Nat × List (List Nat)

@[expose] noncomputable def fixRep (p : Rep) (gens : List (List Nat)) (x : FixD) : Bool :=
  bAnd(Nat.beq (lenS gens) p.1,
  bAnd(Nat.beq (Nat.add (lenS x.1) (lenS x.2.2.1)) (nat_lit 12),
  bAnd(allS (fun y => Nat.beq (synS y) (nat_lit 0)) (appS x.1 x.2.2.1),
  bAnd(allS (fun g => allS (fixS g) x.1) gens,
  bAnd(dualS x.1 x.2.1 (nat_lit 0),
  bAnd(spanChk x.1 p.2.1 (nat_lit 0),
  bAnd(allS (allS (fun f => Nat.beq (par24 f) (nat_lit 0))) x.2.2.2,
  bAnd(ysChk gens x.2.2.2 x.2.2.1 (nat_lit 0),
  bAnd(Nat.beq (lenS (mwsRem gens p.2.2.2.1)) (nat_lit 0),
    basicsOK x.1 p.2.2.1)))))))))

@[expose] noncomputable def fixD0 : FixD := ([], [], [], [])

@[expose] noncomputable def fixAt (reps : List Rep) (gens : List (List (List Nat))) (fx : List FixD)
    (i : Nat) : Bool :=
  fixRep (nthS repD reps i) (nthS [] gens i) (nthS fixD0 fx i)

end CFSG.KC.FixBoundK

end
