module

public import Certificates.Data.Kernel.Co1BW
public import CFSG.Certificates.Kernel.Common.StrSplit
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1PairData

public section

namespace CFSG.KC.Co1BPair

open CFSG.KC.Loop CFSG.KC.M1F2 CFSG.KC.Co1F2 CFSG.KC.Co1B CFSG.KLie.CT
  CFSG.EvenSporadicStandard.Co1Pair

@[expose] def numsOf (cs : List Char) : List Nat :=
  (cs.splitOn ' ').map fun p => CFSG.KC.Str.decVal (p.filter Char.isDigit)

@[expose] def goodP (p : List Char) : Bool :=
  (!p.isEmpty && p.all Char.isDigit) ||
    (p.getLast?.any (fun c => c.toNat == 10) && !p.dropLast.isEmpty && p.dropLast.all Char.isDigit)

@[expose] def encW (ws : List (List Nat)) : List Nat := ws.flatMap fun w => w.length :: w

@[expose] noncomputable def lettersK (lo hi : Nat) (w : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun l _ ih => CFSG.KLie.CT.andB (Nat.ble lo l) (CFSG.KLie.CT.andB (Nat.blt l hi) ih)) w

@[expose] noncomputable def wordsK (M : Nat → Nat) (G : List Nat) (lo hi off : Nat) (ws : List (List Nat))
    (t : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun w _ ih t => CFSG.KLie.CT.andB (lettersK lo hi w)
      (CFSG.KLie.CT.andB (eqK (M (Nat.add off t)) (gwordFrom G w oneK)) (strictB (Nat.succ t) ih))) ws t

@[expose] def offK (i : Nat) : Nat := [7, 1372, 2396].getD i 0

@[expose] noncomputable def tmK (M : Nat → Nat) (i k : Nat) : Nat :=
  nIf(Nat.blt i (nat_lit 3), M (Nat.add (offK i) k), oneK)

@[expose] noncomputable def chkK (M : Nat → Nat) (i t p : Nat) : Bool :=
  let g := 7 - cpF i
  CFSG.KLie.CT.andB (Nat.blt (p / cpN i / cpN (i + 1)) (cpN (i + 2)))
    (eqK (mulWK (M (cpF i + t % g)) (tmK M i (t / g)))
      (mulWK (tmK M i (p % cpN i))
        (mulWK (tmK M (i + 1) (p / cpN i % cpN (i + 1))) (tmK M (i + 2) (p / cpN i / cpN (i + 1))))))

@[expose] noncomputable def levK (M : Nat → Nat) (i : Nat) (D : List Nat) (t : Nat) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun p _ ih t => CFSG.KLie.CT.andB (chkK M i t p) (strictB (Nat.succ t) ih)) D t

end CFSG.KC.Co1BPair

end
