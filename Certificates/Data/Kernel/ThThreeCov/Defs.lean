module

public import CFSG.Certificates.Kernel.Th.Expr
public import CFSG.Sporadic.Th.Max3.Data

public section

namespace CFSG.KC.ThThreeCov

open CFSG.KC.Th CFSG.KC.Th.Expr

@[expose] noncomputable def prodR (k : K) (R : Nat → Nat) (l : List Nat) : Nat :=
  List.rec (motive := fun _ => Nat) k.ONE (fun r _ acc => k.mul (R r) acc) l

@[expose] noncomputable def allLt (n : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun r _ acc => CFSG.KC.Th.andB (Nat.blt r n) acc) l

@[expose] noncomputable def lenR {α : Type} (l : List α) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun _ _ acc => Nat.succ acc) l

@[expose] noncomputable def memB (x : Nat) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun r _ acc => CFSG.KC.Th.orB (Nat.beq r x) acc) l

@[expose] noncomputable def seedsOK (k : K) (R : Nat → Nat) : Bool :=
  CFSG.KC.Th.andB (Nat.beq (R 0) (TE.a.pk k)) (CFSG.KC.Th.andB (Nat.beq (R 1) (TE.b.pk k))
    (CFSG.KC.Th.andB (Nat.beq (R 2) (TE.x.pk k)) (CFSG.KC.Th.andB (Nat.beq (R 3) (TE.y.pk k))
      (Nat.beq (R 4) ((TE.pow .y 5).pk k)))))

@[expose] noncomputable def defOK (k : K) (R : Nat → Nat) (i : Nat) (d : List Nat) : Bool :=
  CFSG.KC.Th.andB (allLt (5 + i) d) (Nat.beq (R (5 + i)) (prodR k R d))

@[expose] noncomputable def defsChunk (k : K) (R : Nat → Nat) (D : List (List Nat)) (c : Nat) :
    Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun j acc => CFSG.KC.Th.andB acc (Bool.rec true (defOK k R (16 * c + j) (D.getD (16 * c + j) []))
      (Nat.blt (16 * c + j) (lenR D)))) 16

@[expose] noncomputable def freshLt (n : Nat) (l : List Nat) : Nat → Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun o _ ih m => CFSG.KC.Th.andB (Nat.blt o n) (CFSG.KC.Th.andB (Nat.beq (Nat.land (Nat.shiftRight m o) 1) 0)
      (ih (Nat.lor m (Nat.shiftLeft 1 o))))) l

@[expose] def genR (g1 g2 i : Nat) : Nat := Bool.rec g2 g1 (Nat.beq i 0)

@[expose] noncomputable def tabGlobal (k : K) (R : Nat → Nat) (n tb g1 g2 : Nat)
    (ord : List Nat) : Bool :=
  CFSG.KC.Th.andB (Nat.ble (tb + 81) n) (CFSG.KC.Th.andB (Nat.blt g1 n) (CFSG.KC.Th.andB (Nat.blt g2 n)
    (CFSG.KC.Th.andB (Nat.beq (R tb) k.ONE) (CFSG.KC.Th.andB (Nat.beq (lenR ord) 81) (freshLt 81 ord 0)))))

@[expose] noncomputable def tabRow (k : K) (R : Nat → Nat) (tb g1 g2 kv : Nat)
    (tpar tgen cl ord : List Nat) (j : Nat) : Bool :=
  CFSG.KC.Th.andB (Bool.rec (CFSG.KC.Th.andB (Nat.blt (tpar.getD j 0) j) (CFSG.KC.Th.andB (Nat.blt (tgen.getD j 0) 2)
      (Nat.beq (R (tb + j)) (k.mul (R (tb + tpar.getD j 0)) (R (genR g1 g2 (tgen.getD j 0)))))))
      true (Nat.beq j 0))
    (CFSG.KC.Th.andB (CFSG.KC.Th.andB (Nat.blt (cl.getD (2 * j) 0) 81)
        (Nat.beq (k.mul (R (tb + j)) (R g1)) (R (tb + cl.getD (2 * j) 0))))
      (CFSG.KC.Th.andB (CFSG.KC.Th.andB (Nat.blt (cl.getD (2 * j + 1) 0) 81)
          (Nat.beq (k.mul (R (tb + j)) (R g2)) (R (tb + cl.getD (2 * j + 1) 0))))
        (Bool.rec true
          (Nat.blt (vecB k.rm kv (R (tb + ord.getD j 0)))
            (vecB k.rm kv (R (tb + ord.getD (j + 1) 0))))
          (Nat.blt j 80))))

@[expose] noncomputable def invsOK (k : K) (R : Nat → Nat) (n : Nat) (I : List (Nat × Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun p _ acc => CFSG.KC.Th.andB (CFSG.KC.Th.andB (Nat.blt p.1 n) (CFSG.KC.Th.andB (Nat.blt p.2 n)
      (Nat.beq (k.mul (R p.1) (R p.2)) k.ONE))) acc) I

@[expose] noncomputable def commOK (k : K) (R : Nat → Nat) (n t : Nat) (zs : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun z _ acc => CFSG.KC.Th.andB (CFSG.KC.Th.andB (Nat.blt z n) (Nat.beq (k.mul (R z) t) (k.mul t (R z)))) acc) zs

@[expose] noncomputable def entOK (k : K) (R : Nat → Nat) (n tb rep : Nat)
    (e : Nat × Nat × List Nat) : Bool :=
  CFSG.KC.Th.andB (Nat.blt e.1 81) (CFSG.KC.Th.andB (Nat.blt e.2.1 n)
    (CFSG.KC.Th.andB (Nat.beq (k.mul (R rep) (R e.2.1)) (k.mul (R e.2.1) (R (tb + e.1))))
      (commOK k R n (R (tb + e.1)) e.2.2)))

@[expose] noncomputable def memE (x : Nat) (E : List (Nat × Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun e _ acc => CFSG.KC.Th.orB (memB x e.2.2) acc) E

@[expose] noncomputable def inZs (I : List (Nat × Nat)) (E : List (Nat × Nat × List Nat))
    (l : Nat) : Bool :=
  CFSG.KC.Th.orB (memE l E) (List.rec (motive := fun _ => Bool) false
    (fun p _ acc => CFSG.KC.Th.orB (CFSG.KC.Th.andB (Nat.beq p.2 l) (memE p.1 E)) acc) I)

@[expose] noncomputable def wordIn (I : List (Nat × Nat)) (E : List (Nat × Nat × List Nat))
    (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ acc => CFSG.KC.Th.andB (inZs I E l) acc) w

@[expose] noncomputable def clsOK (k : K) (R : Nat → Nat) (n tb : Nat) (I : List (Nat × Nat))
    (c : Nat × List (Nat × Nat × List Nat) × List Nat × List Nat) : Bool :=
  CFSG.KC.Th.andB (Nat.blt c.1 n)
    (CFSG.KC.Th.andB (List.rec (motive := fun _ => Bool) true
        (fun e _ acc => CFSG.KC.Th.andB (entOK k R n tb c.1 e) acc) c.2.1)
      (CFSG.KC.Th.andB (CFSG.KC.Th.andB (wordIn I c.2.1 c.2.2.1) (wordIn I c.2.1 c.2.2.2))
        (CFSG.KC.Th.andB (Nat.beq (prodR k R c.2.2.1) (R 2)) (Nat.beq (prodR k R c.2.2.2) (R 3)))))

end CFSG.KC.ThThreeCov

end
