
module

public import CFSG.Monster.B.Fischer.InducedChecksInputs
public import Certificates.Data.Kernel.SortTree

public section

namespace CFSG.KC.Ind3034

open CFSG.KLie.CT CFSG.KC.SortTree CFSG.Monster.B.Fischer CFSG.Monster.B.TwoA

@[expose] noncomputable def zFibK (G : ℕ → ℕ) (g i : ℕ) : ℕ :=
  Nat.div (Nat.sub (fget (G g) (Nat.add 1046 (Nat.mul 32 i)) 12) 1046) 32

@[expose] def kappaW (j g i : ℕ) : List ℤ := invWord (blockWord j) ++ [genLetter g] ++ blockWord i

@[expose] def wordL (w : List ℤ) : List ℕ :=
  w.foldr (fun z acc => acc.map fun x => (letterCat z).toList.getD x 0) (List.range 22)

@[expose] noncomputable def zShiftK (T : ℕ → ℕ) (t i : ℕ) : ℕ :=
  Nat.sub (fget (T t) (Nat.add 1046 (Nat.mul 32 i)) 12) (Nat.add 1046 (Nat.mul 32 i))

@[expose] noncomputable def eqPre (c : ℕ) : List ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun i => Nat.beq i 22)
    (fun a _ ih i => andB (Nat.beq (fget c (Nat.add 32 i) 5) a) (ih (Nat.succ i)))

@[expose] noncomputable def chkX (G : ℕ → ℕ) : Bool :=
  allN 2 fun g => allN 22 fun t => Nat.beq (fget (G g) t 12) (genAB' g t)

@[expose] noncomputable def chkW (G : ℕ → ℕ) : Bool :=
  allN 2 fun g => allN 1024 fun u => Nat.beq (fget (G g) (Nat.add 22 u) 12) (Nat.add 22 (linW g u))

@[expose] noncomputable def chkT (T : ℕ → ℕ) : Bool :=
  allN 10 fun t =>
    andB (allN 22 fun n => Nat.beq (fget (T t) n 12) n)
      (andB (allN 1024 fun u => Nat.beq (fget (T t) (Nat.add 22 u) 12) (Nat.add 22 (u ^^^ 2 ^ t)))
        (allN 77 fun i => andB (Nat.blt (zShiftK T t i) 32)
          (allN 32 fun q => Nat.beq (fget (T t) (Nat.add (Nat.add 1046 (Nat.mul 32 i)) q) 12)
            (Nat.add (Nat.add 1046 (Nat.mul 32 i)) (q ^^^ zShiftK T t i)))))

@[expose] noncomputable def chkS (T : ℕ → ℕ) : Bool :=
  allN 10 fun t => allN 77 fun i =>
    Nat.beq (red 17 pivQ rowQ (wordMask (invWord (blockWord i)) (spreadW (2 ^ t)) ^^^
      spreadQ (zShiftK T t i))) 0

@[expose] noncomputable def zOne (G rec : ℕ → ℕ) (g i r : ℕ) : Bool :=
  andB (Nat.blt r 5760) (andB (Nat.blt (zFibK G g i) 77)
    (andB (eqPre (valF 270 (rec r)) (wordL (kappaW (zFibK G g i) g i)) 0)
      (allN 32 fun q => Nat.beq (fget (G g) (Nat.add (Nat.add 1046 (Nat.mul 32 i)) q) 12)
        (Nat.add (Nat.add 1046 (Nat.mul 32 (zFibK G g i))) (fget (valF 270 (rec r)) q 5)))))

@[expose] noncomputable def zFrom (G rec : ℕ → ℕ) : List ℕ → ℕ → Bool :=
  List.rec (motive := fun _ => ℕ → Bool) (fun n => Nat.beq n 154)
    (fun r _ ih n => andB (zOne G rec (Nat.div n 77) (Nat.mod n 77) r) (ih (Nat.succ n)))

end CFSG.KC.Ind3034

end
