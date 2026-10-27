module

public import CFSG.RankThree.PartOne.KE.E7ThreeLatticeInputs

public section

namespace CFSG.KC.E7T3

open CFSG.RankThree.PartOne.KE CFSG.RankThree.Lattice CFSG.Blueprint.Chevalley

@[expose] def bandK (a b : Bool) : Bool := Bool.rec false b a

@[expose] def beqB (a b : Bool) : Bool := Bool.rec (Bool.rec true false b) b a

@[expose] def allL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ r => bandK (p a) r) l

@[expose] def anyL {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => Bool.rec r true (p a)) l

@[expose] def allNK (n : ℕ) (f : ℕ → Bool) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k r => bandK (f k) r) n

@[expose] def memK (x : ℕ) (l : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun a _ r => Bool.rec r true (Nat.beq x a)) l

@[expose] def listEqK (a b : List ℕ) : Bool :=
  List.rec (motive := fun _ => List ℕ → Bool)
    (fun b => List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) b)
    (fun x _ r b =>
      List.rec (motive := fun _ => Bool) false (fun y t _ => bandK (Nat.beq x y) (r t)) b)
    a b

@[expose] def BAD : ℕ := 72057594037927936

@[expose] def lnK (x s : ℕ) : ℕ := Nat.land (Nat.shiftRight x s) 255

@[expose] def loK (q : ℕ) : ℕ := Nat.land q 72057594037927935

@[expose] def hiK (q : ℕ) : ℕ := Nat.shiftRight q 56

@[expose] def updK (x s old nw : ℕ) : ℕ :=
  Nat.add (Nat.sub x (Nat.shiftLeft old s)) (Nat.shiftLeft nw s)

@[expose] def setK (x s old c plus : ℕ) : ℕ :=
  Bool.rec BAD
    (Bool.rec BAD
      (Bool.rec BAD (updK x s old (Nat.sub plus (Nat.add old c)))
        (Nat.blt (Nat.sub plus (Nat.add old c)) 256))
      (Nat.ble (Nat.add old c) plus))
    (Nat.blt x BAD)

@[expose] def stepK (i x : ℕ) : ℕ :=
  Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec (Bool.rec
    (setK x 48 (lnK x 48) 0 (Nat.add (lnK x 40) 128))
    (setK x 40 (lnK x 40) 0 (Nat.add (lnK x 32) (lnK x 48))) (Nat.beq i 5))
    (setK x 32 (lnK x 32) 0 (Nat.add (lnK x 24) (lnK x 40))) (Nat.beq i 4))
    (setK x 24 (lnK x 24) 128 (Nat.add (Nat.add (lnK x 8) (lnK x 16)) (lnK x 32))) (Nat.beq i 3))
    (setK x 16 (lnK x 16) 0 (Nat.add (lnK x 0) (lnK x 24))) (Nat.beq i 2))
    (setK x 8 (lnK x 8) 0 (Nat.add (lnK x 24) 128)) (Nat.beq i 1))
    (setK x 0 (lnK x 0) 0 (Nat.add (lnK x 16) 128)) (Nat.beq i 0)

@[expose] def actK (w : List (Fin Tag.E7.rank)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ) x (fun i _ r => stepK i.val r) w

@[expose] def actRevK (w : List (Fin Tag.E7.rank)) (x : ℕ) : ℕ :=
  List.rec (motive := fun _ => ℕ → ℕ) (fun y => y) (fun i _ r y => r (stepK i.val y)) w x

@[expose] def perm3K (x a b c : ℕ) : ℕ :=
  updK (updK (updK x a (lnK x a) (lnK x c)) b (lnK x b) (lnK x a)) c (lnK x c) (lnK x b)

@[expose] def permK (kind : ℕ) (rot : Bool) (x : ℕ) : ℕ :=
  Bool.rec
    (Bool.rec x (Bool.rec (perm3K x 8 16 32) (perm3K x 8 32 16) rot) (Nat.beq kind 2))
    (Bool.rec (perm3K x 8 32 48) (perm3K x 8 48 32) rot) (Nat.beq kind 1)

@[expose] def stdSel (s0 s1 s2 s3 : List ℕ) (k : ℕ) : List ℕ :=
  Bool.rec (Bool.rec (Bool.rec s3 s2 (Nat.beq k 2)) s1 (Nat.beq k 1)) s0 (Nat.beq k 0)

@[expose] def toV (x : ℕ) (j : Fin Tag.E7.rank) : ℤ := ((lnK x (8 * j.val) : ℕ) : ℤ) - 128

@[expose] def decL (x : ℕ) : List ℤ := vofFn Tag.E7.rank (toV x)

@[expose] def compK (S : List ℕ) (w : List (Fin Tag.E7.rank)) (cm : E7T3Comp) : Bool :=
  bandK (decide ((∀ x ∈ cm.u, x.val ∈ e7T3Nodes cm.kind) ∧ cm.kind < 4 ∧ (cm.kind = 1 → cm.u = [])))
    (allL (fun p => bandK (Nat.blt (actRevK w (actK e7T3Word (actK w p))) BAD)
      (Nat.beq (actRevK w (actK e7T3Word (actK w p))) (actK cm.u (permK cm.kind cm.rot p)))) S)

@[expose] def rlK (s0 s1 s2 s3 : List ℕ) (w : List (Fin Tag.E7.rank)) (comps : List E7T3Comp) :
    List ℕ :=
  comps.flatMap fun cm => (stdSel s0 s1 s2 s3 cm.kind).map (actK w)

@[expose] def memLoK (e : ℕ) (roots : List ℕ) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun q _ r => Bool.rec r true (Nat.beq e (loK q))) roots

@[expose] def goodK (s0 s1 s2 s3 roots : List ℕ) (c : E7T3Cert) (R : List ℕ) : Bool :=
  bandK (decide (∀ i ∈ c.cls, i < 21))
    (bandK (allL (fun cm => compK (stdSel s0 s1 s2 s3 cm.kind) c.w cm) c.comps)
      (bandK (listEqK (rlK s0 s1 s2 s3 c.w c.comps) R)
        (bandK (allL (fun e => memLoK e roots) R)
          (allL (fun q => beqB (memK (hiK q) c.cls) (memK (loK q) R)) roots))))

@[expose] def classOK (cl : ℕ) (ρ : ERow) : Bool :=
  bandK (Nat.blt cl 21)
    (allNK 21 fun i => beqB (decide (∃ u ∈ eUnits, ρ = escale u (e7T3G i))) (Nat.beq i cl))

@[expose] def rootsK (roots : List ℕ) : Bool :=
  allL (fun q => bandK (Nat.blt (loK q) BAD) (classOK (hiK q) (e7T3Row (decL (loK q))))) roots

@[expose] def validK (S : List ℕ) : Bool := allL (fun p => Nat.blt p BAD) S

@[expose] def flatK (x : ERow) : Bool :=
  anyL (fun c => allNK 21 fun l =>
    beqB (decide (edot (e7T3G l) x = (0, 0))) (memK l c.cls)) e7T3Certs

@[expose] def flatsK : Bool :=
  allNK 21 fun j => allNK j fun i => flatK (ecross (e7T3G i) (e7T3G j))

end CFSG.KC.E7T3

end
