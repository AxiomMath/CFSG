module

public import Certificates.Data.Kernel.Co1BW
public import CFSG.Certificates.Kernel.Enum.Defs

public section

namespace CFSG.KC.Co1Cl

open CFSG.KC.Enum CFSG.KC.Co1F2 CFSG.KC.Co1B

@[expose] noncomputable def refK (S : List Nat) (ns lo r : Nat) : Nat :=
  nIf(Nat.blt r ns, getL (nat_lit 0) S r, Nat.add lo (Nat.sub r ns))

@[expose] noncomputable def okRefK (ns lo k r : Nat) : Bool :=
  bIf(Nat.blt r ns, true, Nat.blt (Nat.add lo (Nat.sub r ns)) k)

@[expose] noncomputable def recK (TS : Nat → Nat) (S : List Nat) (lo k c : Nat) : Bool :=
  strictB (lenL S) fun ns =>
  strictB (fld(c, nat_lit 1, nat_lit 1048575)) fun r₁ =>
  strictB (Nat.shiftRight c (nat_lit 21)) fun r₂ =>
  strictB (TS k) fun W =>
  bAnd(canK W, bAnd(okRefK ns lo k r₁,
    Bool.rec (motive := fun _ => Bool)
      (bAnd(okRefK ns lo k r₂,
        Nat.beq W (mulWK (TS (refK S ns lo r₁)) (TS (refK S ns lo r₂)))))
      (Nat.beq (mulWK W (TS (refK S ns lo r₁))) oneK)
      (Nat.beq (Nat.land c (nat_lit 1)) (nat_lit 1))))

@[expose] noncomputable def runK (TS : Nat → Nat) (S : List Nat) (lo : Nat) : Nat → List Nat → Bool :=
  fun k cs => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun c _ ih k => strictB k fun k => bAnd(recK TS S lo k c, ih (Nat.succ k))) cs k

@[expose] noncomputable def chGet (CH : List (Nat × Nat × List Nat)) : Nat → Nat × Nat × List Nat :=
  List.rec (motive := fun _ => Nat → Nat × Nat × List Nat) (fun _ => (0, 0, []))
    (fun x _ ih i => Nat.rec (motive := fun _ => Nat × Nat × List Nat) x (fun j _ => ih j) i) CH

@[expose] noncomputable def chunkK (TS : Nat → Nat) (CH : List (Nat × Nat × List Nat))
    (WL : Nat → List Nat) (i : Nat) : Bool :=
  Prod.rec (motive := fun _ => Bool)
    (fun st r => Prod.rec (motive := fun _ => Bool) (fun lo S => runK TS S lo st (WL i)) r)
    (chGet CH i)

@[expose] noncomputable def eqLK : List Nat → List Nat → Bool :=
  fun a => List.rec (motive := fun _ => List Nat → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ ih b => List.rec (motive := fun _ => Bool) false
      (fun y t _ => bAnd(Nat.beq x y, ih t)) b) a

@[expose] noncomputable def layFromK (WL : Nat → List Nat) (N : Nat) :
    List (Nat × Nat × List Nat) → Nat → Nat → Nat → List Nat → Bool :=
  fun CH => List.rec (motive := fun _ => Nat → Nat → Nat → List Nat → Bool)
    (fun _ s _ _ => Nat.beq s N)
    (fun x _ ih i s plo pS => strictB i fun i => strictB s fun s =>
      Prod.rec (motive := fun _ => Bool) (fun st r => Prod.rec (motive := fun _ => Bool)
        (fun lo S => bAnd(Nat.beq st s,
          bAnd(bIf(Nat.beq lo st, true, bAnd(Nat.beq lo plo, eqLK S pS)),
            ih (Nat.succ i) (Nat.add st (lenL (WL i))) lo S))) r) x) CH

@[expose] noncomputable def layoutK (CH : List (Nat × Nat × List Nat)) (WL : Nat → List Nat)
    (n₀ N : Nat) : Bool :=
  layFromK WL N CH (nat_lit 0) n₀ n₀ []

@[expose] noncomputable def epK (TS : Nat → Nat) (p : Nat) (G : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun g _ ih v acc => strictN (Nat.mod v p) fun e =>
      strictN (Nat.rec (motive := fun _ => Nat) acc
        (fun _ a => strictN a fun a => mulWK a (TS g)) e) fun acc' => ih (Nat.div v p) acc') G

@[expose] noncomputable def getLL (L : List (List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) x (fun j _ => ih j) i) L

@[expose] noncomputable def termK (TS : Nat → Nat) (p : Nat) (GL : List (List Nat)) (t : Nat) : Nat :=
  nIf(Nat.beq (Nat.land t (nat_lit 1)) (nat_lit 0), TS (Nat.shiftRight t (nat_lit 1)),
    epK TS p (getLL GL (fld(t, nat_lit 1, nat_lit 3))) (Nat.shiftRight t (nat_lit 3)) oneK)

@[expose] noncomputable def eqK (TS : Nat → Nat) (p : Nat) (GL : List (List Nat)) (q : List Nat) : Bool :=
  bAnd(Nat.beq (lenL q) (nat_lit 4),
    Nat.beq (mulWK (termK TS p GL (getL (nat_lit 0) q (nat_lit 0))) (termK TS p GL (getL (nat_lit 0) q (nat_lit 1))))
      (mulWK (termK TS p GL (getL (nat_lit 0) q (nat_lit 2))) (termK TS p GL (getL (nat_lit 0) q (nat_lit 3)))))

@[expose] noncomputable def eqsK (TS : Nat → Nat) (p : Nat) (GL : List (List Nat)) (Q : List (List Nat)) :
    Bool :=
  List.rec (motive := fun _ => Bool) true (fun q _ ih => bAnd(eqK TS p GL q, ih)) Q

@[expose] noncomputable def getLLL (L : List (List (List Nat))) : Nat → List (List Nat) :=
  List.rec (motive := fun _ => Nat → List (List Nat)) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List (List Nat)) x (fun j _ => ih j) i) L

@[expose] noncomputable def normRowsK (TS : Nat → Nat) (p : Nat) (G : List Nat) (g : Nat) :
    List Nat → Nat → Bool :=
  fun rows => List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun v _ ih j => strictB j fun j =>
      bAnd(Nat.beq (mulWK (TS (getL (nat_lit 0) G j)) (TS g)) (mulWK (TS g) (epK TS p G v oneK)),
        ih (Nat.succ j))) rows

@[expose] noncomputable def normK (TS : Nat → Nat) (p : Nat) (GL : List (List Nat))
    (NZ : List (Nat × List Nat)) : Bool :=
  List.rec (motive := fun _ => Bool) true
    (fun x _ ih => Prod.rec (motive := fun _ => Bool) (fun g rows =>
      bAnd(Nat.beq (lenL rows) (lenL (getLL GL (nat_lit 0))),
        bAnd(normRowsK TS p (getLL GL (nat_lit 0)) g rows (nat_lit 0), ih))) x) NZ

@[expose] noncomputable def addVK (p : Nat) : Nat → Nat → Nat → Nat :=
  Nat.rec (motive := fun _ => Nat → Nat → Nat) (fun _ _ => nat_lit 0)
    (fun _ ih x y => Nat.add (Nat.mod (Nat.add (Nat.mod x p) (Nat.mod y p)) p)
      (Nat.mul p (ih (Nat.div x p) (Nat.div y p))))

@[expose] noncomputable def actK (p n : Nat) (rows : List Nat) : Nat → Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ acc => acc)
    (fun r _ ih v acc => strictN (Nat.mod v p) fun e =>
      strictN (Nat.rec (motive := fun _ => Nat) acc (fun _ a => strictN a fun a => addVK p n a r) e)
        fun acc' => ih (Nat.div v p) acc') rows

@[expose] noncomputable def nzRows (NZ : List (Nat × List Nat)) : Nat → List Nat :=
  List.rec (motive := fun _ => Nat → List Nat) (fun _ => [])
    (fun x _ ih i => Nat.rec (motive := fun _ => List Nat) (Prod.rec (motive := fun _ => List Nat)
      (fun _ r => r) x) (fun j _ => ih j) i) NZ

@[expose] noncomputable def nzLen (NZ : List (Nat × List Nat)) : Nat :=
  List.rec (motive := fun _ => Nat) (nat_lit 0) (fun _ _ ih => Nat.succ ih) NZ

@[expose] noncomputable def memK (c : Nat) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun x _ ih => bIf(Nat.beq x c, true, ih)) L

@[expose] noncomputable def depK (DP c : Nat) : Nat := fld(DP, Nat.mul (nat_lit 8) c, nat_lit 255)

@[expose] noncomputable def forFromK (p n P : Nat) (NZ : List (Nat × List Nat)) (RT : List Nat)
    (DP : Nat) : List Nat → Nat → Bool :=
  fun FT => List.rec (motive := fun _ => Nat → Bool) (fun c => Nat.beq c P)
    (fun e _ ih c => strictB c fun c => strictB (depK DP c) fun d =>
      bAnd(bIf(Nat.beq d (nat_lit 0), memK c RT,
        strictB (Nat.mod e P) fun pc => strictB (Nat.div e P) fun g =>
          bAnd(Nat.blt g (nzLen NZ), bAnd(Nat.beq (Nat.succ (depK DP pc)) d,
            Nat.beq (actK p n (nzRows NZ g) pc (nat_lit 0)) c))),
        ih (Nat.succ c))) FT

@[expose] noncomputable def forestK (p n : Nat) (NZ : List (Nat × List Nat)) (RT : List Nat) (DP : Nat)
    (FT : List Nat) : Bool :=
  strictB (Nat.pow p n) fun P => forFromK p n P NZ RT DP FT (nat_lit 1)

@[expose] noncomputable def canAllK (TS : Nat → Nat) (n : Nat) : Bool := allN n fun k => canK (TS k)

end CFSG.KC.Co1Cl

end
