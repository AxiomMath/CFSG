module

public import Certificates.Data.Kernel.Spor.Raw
public import Certificates.Data.Kernel.Spor.Mathieu
public import CFSG.Sporadic.Co2Cert.Types
public import Mathlib.GroupTheory.Schreier

public section

namespace CFSG.KS.Co2Shape

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.Sporadic.Co2Cert CFSG.Monster.B.Mathieu

@[expose] noncomputable def lenL {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) l

@[expose] noncomputable def allL {α : Type} (f : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun x _ ih => bAnd(f x, ih)) l

@[expose] noncomputable def eqNL (a : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => bAnd(Nat.beq x y, ih ys)) b) a

@[expose] noncomputable def eqIL (a : List Int) : List Int → Bool :=
  List.rec (motive := fun _ => List Int → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y ys _ => bAnd(Nat.beq (CFSG.KS.Mathieu.icode x) (CFSG.KS.Mathieu.icode y), ih ys)) b)
    a

@[expose] noncomputable def distinctL (n : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih M => bAnd(Nat.blt x n, bAnd(bIf(hasBit M x, false, true),
      strictB (Nat.lor M (Nat.shiftLeft (nat_lit 1) x)) ih))) l

@[expose] noncomputable def permL (n : Nat) (l : List Nat) : Bool :=
  bAnd(Nat.beq (lenL l) n, distinctL n l (nat_lit 0))

@[expose] noncomputable def wordsL (k : Nat) (D : List (List Int)) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih j => bAnd(lettersK (Nat.add j k) w, ih (Nat.succ j))) D

@[expose] noncomputable def chainK (c : ChainRecord) (n k r : Nat) (base : List Nat) : Bool :=
  bAnd(Nat.beq c.degree n, bAnd(Nat.beq (lenL c.generators) k,
  bAnd(Nat.beq (lenL c.strongGenerators) r, bAnd(Nat.beq (lenL c.derivations) (Nat.sub r k),
  bAnd(allL (permL n) c.generators, bAnd(allL (permL n) c.strongGenerators,
  bAnd(eqNL c.base base, wordsL k c.derivations (nat_lit 0))))))))

@[expose] noncomputable def incL (n : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun x _ ih p => bAnd(Nat.blt x n, bAnd(Nat.ble p x, ih (Nat.succ x)))) l

@[expose] noncomputable def tripleK (t : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun i t1 _ =>
    List.rec (motive := fun _ => Bool) false (fun u t2 _ =>
      List.rec (motive := fun _ => Bool) false (fun v t3 _ =>
        bAnd(List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) t3,
          bAnd(Nat.blt i (nat_lit 2), bAnd(Nat.blt u (nat_lit 2300), Nat.blt v (nat_lit 2300)))))
        t2) t1) t

@[expose] noncomputable def co2ShapeK (r : Co2CertFile) : Bool :=
  bAnd(Nat.beq r.schemaVersion (nat_lit 1), bAnd(Nat.beq r.prime (nat_lit 2),
  bAnd(Nat.beq r.dimension (nat_lit 22),
  bAnd(Nat.beq (lenL r.vectors) (nat_lit 2300),
  bAnd(allL (fun v => bAnd(Nat.beq (lenL v) (nat_lit 22), allL (fun x => Nat.blt x (nat_lit 2)) v))
    r.vectors,
  bAnd(eqNL r.basisIndices [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5,
    nat_lit 6, nat_lit 7, nat_lit 8, nat_lit 9, nat_lit 10, nat_lit 11, nat_lit 12, nat_lit 13,
    nat_lit 14, nat_lit 15, nat_lit 17, nat_lit 18, nat_lit 23, nat_lit 28, nat_lit 41, nat_lit 61],
  bAnd(chainK r.chain (nat_lit 2300) (nat_lit 2) (nat_lit 11)
    [nat_lit 0, nat_lit 1, nat_lit 2, nat_lit 3, nat_lit 5, nat_lit 4],
  bAnd(chainK r.coprimeChain (nat_lit 2300) (nat_lit 2) (nat_lit 17)
    [nat_lit 0, nat_lit 1, nat_lit 3, nat_lit 2, nat_lit 5, nat_lit 4],
  bAnd(eqIL r.coprimeConjugator [-1, 2, 2, 1, 2, -1],
  bAnd(Nat.beq r.point (nat_lit 0),
  bAnd(eqNL r.stabilizerGeneratorIndices [nat_lit 0, nat_lit 2, nat_lit 3, nat_lit 4, nat_lit 5,
    nat_lit 6, nat_lit 7, nat_lit 8, nat_lit 9, nat_lit 10],
  bAnd(eqNL (List.rec (motive := fun _ => List Nat) [] (fun o _ ih => List.cons (lenL o) ih)
      r.stabilizerOrbits) [nat_lit 1, nat_lit 1408, nat_lit 891],
  bAnd(allL (fun o => incL (nat_lit 2300) o (nat_lit 0)) r.stabilizerOrbits,
  bAnd(eqNL (List.rec (motive := fun _ => List Nat) [] (fun m _ ih => List.cons m.representative ih)
      r.merges) [nat_lit 1, nat_lit 3],
  bAnd(eqNL (List.rec (motive := fun _ => List Nat) []
      (fun m _ ih => List.cons (lenL m.instructions) ih) r.merges) [nat_lit 2298, nat_lit 2298],
    allL (fun m => allL tripleK m.instructions) r.merges)))))))))))))))

end CFSG.KS.Co2Shape

end
