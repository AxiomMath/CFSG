module

public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.LyGlue

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def letT (T TI : Nat → Nat) (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => T (Nat.sub k 1)) (fun k => TI k) l

@[expose] noncomputable def wpt (w m : Nat) (L : Int → Nat) (ws : List Int) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) a (fun l _ ih => pg w m (L l) ih) ws

@[expose] noncomputable def wprod (n w m : Nat) (L : Int → Nat) (ws : List Int) : Nat :=
  List.rec (motive := fun _ => Nat) (pidn n w)
    (fun l _ ih => strictN ih (fun q => pcomp n w m (L l) q)) ws

@[expose] noncomputable def blkOK (deg n ng wH : Nat) (F : Nat → Nat) (gpt : Nat → Nat → Nat)
    (H : Nat → Nat) : Bool :=
  allN deg (fun a => strictB (F a) (fun v => bIf(Nat.beq v (nat_lit 65535), true,
    bAnd(Nat.blt v n, allN ng (fun k => Nat.beq (F (gpt k a)) (pg wH (mask wH) (H k) v))))))

@[expose] noncomputable def secOK (deg n : Nat) (F S : Nat → Nat) : Bool :=
  allN n (fun j => bAnd(Nat.blt (S j) deg, Nat.beq (F (S j)) j))

@[expose] noncomputable def imgOK (n wA : Nat) (F S : Nat → Nat) (apt : Nat → Nat) (A : Nat) :
    Bool :=
  allN n (fun j => Nat.beq (F (apt (S j))) (pg wA (mask wA) A j))

@[expose] noncomputable def lcode (l : Int) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => nIf(Nat.beq k 1, nat_lit 0, nat_lit 2))
    (fun k => nIf(Nat.beq k 0, nat_lit 1, nat_lit 3)) l

@[expose] noncomputable def encW (ws : List Int) : Nat :=
  List.foldl (fun acc l => Nat.add (Nat.mul acc 4) (lcode l)) 0 ws

@[expose] noncomputable def letE (cF dF : Nat → Nat) (x a : Nat) : Nat :=
  nIf(Nat.blt x 2, cF a, nIf(Nat.beq x 2, dF a, dF (dF a)))

@[expose] noncomputable def wptE (cF dF : Nat → Nat) (len code a : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ a => a)
    (fun _ ih c a => ih (Nat.shiftRight c 2) (letE cF dF (Nat.land c 3) a)) len code a

@[expose] noncomputable def letPF (G GI : Nat → Nat → Nat) (l : Int) (a : Nat) : Nat :=
  Int.rec (motive := fun _ => Nat) (fun k => G (Nat.sub k 1) a) (fun k => GI k a) l

@[expose] noncomputable def wptG (G GI : Nat → Nat → Nat) (ws : List Int) (a : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) a (fun l _ ih => letPF G GI l ih) ws

@[expose] noncomputable def appL (T : Nat → Nat → Nat) (ls : List Nat) (x : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) x (fun k _ ih => T k ih) ls

@[expose] noncomputable def stepPt (n : Nat) (T : Nat → Nat → Nat) (s : Nat × Nat × List Nat) :
    Bool :=
  allN n (fun a => Nat.beq (T s.1 a) (appL T s.2.2 (T s.2.1 a)))

@[expose] def findStep (S : List (Nat × Nat × List Nat)) (k : Nat) : Nat × Nat × List Nat :=
  (S.find? fun s => s.1 == k).getD (k, 0, [])

@[expose] def flat (S : List (Nat × Nat × List Nat)) (nb : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | f + 1, k => if k = 0 then [] else if k < nb then [k] else
      ((findStep S k).2.2.flatMap (flat S nb f)) ++ flat S nb f (findStep S k).2.1

@[expose] def progOK (S : List (Nat × Nat × List Nat)) (nb : Nat) : Bool :=
  S.all fun s => decide (nb ≤ s.1) && decide (s.2.1 < s.1) && s.2.2.all (fun l => decide (l < s.1)) &&
    (s.2.1 :: s.2.2).all fun l => decide (l < nb) || S.any fun t => t.1 == l

end CFSG.KC.LyGlue

end
