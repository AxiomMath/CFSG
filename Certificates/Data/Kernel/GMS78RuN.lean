module

public import Certificates.Data.Kernel.GMS78Ru

public section

namespace CFSG.KC.GMS

open CFSG.KLie.CT CFSG.KC.Loop

@[expose] noncomputable def SB : Nat := nat_lit 1494337263381065744
@[expose] noncomputable def NBT : Nat := nat_lit 75798666671354321874364325909332658246753232101891375104
@[expose] noncomputable def NCOLS : Nat := nat_lit 6535852264626716467
@[expose] noncomputable def NBAS : Nat := nat_lit 1494337263381065744
@[expose] noncomputable def DC : Nat := nat_lit 3705952237598512919313
@[expose] noncomputable def TWD : Nat := nat_lit 0

@[expose] noncomputable def xs8K (c : Nat) (f : Nat → Nat) : Nat :=
  xorN (nat_lit 8) fun i => nIf(bit c i, f i, nat_lit 0)

@[expose] noncomputable def bCK (QT m n : Nat) : Nat :=
  Nat.xor (Nat.xor (fget QT (Nat.xor m n) (nat_lit 3)) (fget QT m (nat_lit 3))) (fget QT n (nat_lit 3))

@[expose] noncomputable def sMaskNK (c n : Nat) : Nat :=
  xorN n fun i => nIf(bit c i, fget SB i (nat_lit 8), nat_lit 0)

@[expose] noncomputable def gamK (QT c c' : Nat) : Nat :=
  xorN (nat_lit 8) fun n => nIf(bit c n, bCK QT (fget SB n (nat_lit 8)) (sMaskNK c' n), nat_lit 0)

@[expose] noncomputable def dMulK (d e : Nat) : Nat :=
  Nat.add (Nat.mul (nat_lit 2) (Nat.mod (nIf(Nat.beq (Nat.mod d (nat_lit 2)) (nat_lit 0),
      Nat.add (Nat.div d (nat_lit 2)) (Nat.div e (nat_lit 2)),
      Nat.sub (Nat.add (Nat.div d (nat_lit 2)) (nat_lit 4)) (Nat.div e (nat_lit 2)))) (nat_lit 4)))
    (Nat.mod (Nat.add d e) (nat_lit 2))

@[expose] noncomputable def dPartK (QT d c : Nat) : Nat :=
  foldUp (nat_lit 8) (fun n s => nIf(bit c n,
    (fun a t b => Nat.lor (Nat.xor a b) (Nat.shiftLeft (Nat.xor t (gamK QT a b)) (nat_lit 8)))
      (Nat.land s (nat_lit 255)) (Nat.shiftRight s (nat_lit 8)) (pw2 (dMulK d n)), s)) (nat_lit 0)

@[expose] noncomputable def nBetaK (m n : Nat) : Nat :=
  (fun cm cn => xs8K cm fun j => xs8K cn fun i => fget NBT (Nat.add (Nat.mul (nat_lit 8) j) i) (nat_lit 3))
    (maskAppK NCOLS m) (maskAppK NCOLS n)

@[expose] noncomputable def gamTab (R A : Nat) : Nat :=
  orN (nat_lit 64) fun ij => (fun i j => Nat.shiftLeft (nIf(Nat.blt i j,
      (fun bi bj => Nat.xor (nBetaK (maskAppK A bi) (maskAppK A bj)) (linAppK R (nBetaK bi bj)))
        (fget NBAS i (nat_lit 8)) (fget NBAS j (nat_lit 8)), nat_lit 0)) (Nat.mul (nat_lit 3) ij))
    (Nat.div ij (nat_lit 8)) (Nat.mod ij (nat_lit 8))

@[expose] noncomputable def nTauK (d G m : Nat) : Nat :=
  (fun c => Nat.xor (xs8K c fun j => fget TWD (Nat.add (Nat.mul (nat_lit 8) d) j) (nat_lit 3))
      (xs8K c fun j => xs8K c fun i => fget G (Nat.add (Nat.mul (nat_lit 8) i) j) (nat_lit 3)))
    (maskAppK NCOLS m)

@[expose] noncomputable def kGamCol (QT : Nat) : Bool :=
  allN (nat_lit 8) fun j => allN (nat_lit 256) fun c =>
    Nat.beq (xs8K c fun i => fget NBT (Nat.add (Nat.mul (nat_lit 8) j) i) (nat_lit 3))
      (bCK QT (fget SB j (nat_lit 8)) (sMaskNK c j))

@[expose] noncomputable def kDPart (QT INV d : Nat) : Bool :=
  (fun R => strictB (adK R (fget INV R (nat_lit 9))) fun A => strictB (gamTab R A) fun G =>
      allN (nat_lit 256) fun c => strictB (dPartK QT d c) fun s =>
        andB (Nat.beq (sMaskNK (Nat.land s (nat_lit 255)) (nat_lit 8)) (maskAppK A (sMaskNK c (nat_lit 8))))
          (Nat.beq (Nat.shiftRight s (nat_lit 8)) (nTauK d G (sMaskNK c (nat_lit 8)))))
    (fget DC d (nat_lit 9))

@[expose] noncomputable def invTabOK (INV : Nat) : Bool :=
  allN (nat_lit 512) fun R => orB (notB (glK R)) ((fun I => andB (glK I) (Nat.beq (linCompK R I) LINID))
    (fget INV R (nat_lit 9)))

@[expose] noncomputable def bindRows (L : List (List (Fin 8))) (T n k : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun i => Nat.beq i k)
    (fun row _ ih i => andB (bindFin8 row (Nat.shiftRight T (Nat.mul (Nat.mul (nat_lit 3) n) i)) n) (ih (Nat.succ i)))
    L (nat_lit 0)

@[expose] noncomputable def rowAt (L : List (List (Fin 8))) (i T n : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => false)
    (fun row _ ih i => bIf(Nat.beq i (nat_lit 0), bindFin8 row T n, ih (Nat.sub i (nat_lit 1)))) L i

@[expose] noncomputable def nIdxK (R : Nat) : Nat :=
  Nat.add (Nat.add (Nat.mul (nat_lit 64) (fget R (nat_lit 0) (nat_lit 3))) (Nat.mul (nat_lit 8) (fget R (nat_lit 1) (nat_lit 3))))
    (fget R (nat_lit 2) (nat_lit 3))

@[expose] noncomputable def unIdx (k : Nat) : Nat :=
  Nat.lor (Nat.lor (Nat.div k (nat_lit 64)) (Nat.shiftLeft (Nat.mod (Nat.div k (nat_lit 8)) (nat_lit 8)) (nat_lit 3)))
    (Nat.shiftLeft (Nat.mod k (nat_lit 8)) (nat_lit 6))

@[expose] noncomputable def glIdxK (R : Nat) : Nat :=
  sumN (nat_lit 512) fun k => nIf(andB (glK (unIdx k)) (Nat.blt k (nIdxK R)), nat_lit 1, nat_lit 0)

@[expose] noncomputable def bindNC (sb : List Nat) (nbt : List (List (Fin 8))) (nc nb : List Nat)
    (dct : List (Fin 8 × Fin 8 × Fin 8)) (ntw : List (List (Fin 8))) : Bool :=
  andB (bindList (fun n => n) sb SB (nat_lit 8) (nat_lit 8))
  (andB (bindRows nbt NBT (nat_lit 8) (nat_lit 8))
  (andB (bindList (fun n => n) nc NCOLS (nat_lit 8) (nat_lit 8))
  (andB (bindList (fun n => n) nb NBAS (nat_lit 8) (nat_lit 8))
  (andB (bindList packV dct DC (nat_lit 9) (nat_lit 8))
    (allN (nat_lit 8) fun d => rowAt ntw (glIdxK (fget DC d (nat_lit 9)))
      (Nat.shiftRight TWD (Nat.mul (nat_lit 24) d)) (nat_lit 8))))))

end CFSG.KC.GMS

end
