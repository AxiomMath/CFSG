module

public import Certificates.Data.Kernel.LocalComp.Replay
public import CFSG.RankThree.Asc83Table.MatCertDefs

public section

namespace CFSG.KC.LocalComp.FactsV

open CFSG.KC.LQT CFSG.KC.LocalComp.Replay CFSG.SectionRank.Native
open CFSG.RankThree.Asc83Table.Native

@[expose] def fld (h i : Nat) : Nat := Nat.land (Nat.shiftRight h (Nat.mul 20 i)) 1048575

@[expose] noncomputable def wordRV (P : Nat → Nat) (N : Nat) (R : Nat → Nat) : Word → Nat → Bool
  | [], t => Nat.beq t 2
  | [(r, e)], t => decide (t < N) && decide (e < expoFail) && Nat.beq (expoK P (R r) 64 t) e
  | (r, e) :: w, t => decide (3 ≤ t) && decide (t < N) && decide (e < expoFail) &&
      Nat.beq (expoK P (R r) 64 (Nat.shiftRight (P t) 20)) e &&
      wordRV P N R w (Nat.land (P t) 1048575)

@[expose] noncomputable def wordV (P : Nat → Nat) (N : Nat) (R : Nat → Nat) (w : Word) (t : Nat) :
    Bool :=
  wordRV P N R w.reverse t

@[expose] noncomputable def rowV (c : Lay) (X t : Nat) : Nat :=
  Nat.land (Nat.shiftRight X (Nat.mul c.S t)) c.RM

@[expose] noncomputable def factV (c : Lay) (V P : Nat → Nat) (N : Nat) (R : Nat → Nat)
    (n h : Nat) : MFact → Bool
  | .ord r e => decide (r < n) && decide (0 < e) && wordV P N R [(r, e)] (fld h 0) &&
      Nat.beq (V (fld h 0)) c.ONE
  | .conj g u w => decide (g < n) && wordLt n u && wordLt n w &&
      wordV P N R ((g, 1) :: u) (fld h 0) && wordV P N R (w ++ [(g, 1)]) (fld h 1) &&
      Nat.beq (V (fld h 0)) (V (fld h 1))
  | .ne w₁ w₂ t => wordLt n w₁ && wordLt n w₂ && decide (t < c.d) &&
      wordV P N R w₁ (fld h 0) && wordV P N R w₂ (fld h 1) &&
      !Nat.beq (rowV c (V (fld h 0)) t) (rowV c (V (fld h 1)) t)
  | .eq w₁ w₂ => wordLt n w₁ && wordLt n w₂ && wordV P N R w₁ (fld h 0) &&
      wordV P N R w₂ (fld h 1) && Nat.beq (V (fld h 0)) (V (fld h 1))

@[expose] def initK (n : Nat) : List Nat :=
  (List.range n).map fun x => if x = 0 then 0 else if x = 1 then 1 else 2

@[expose] def listIs (Rf : Nat → Nat) : List Nat → Nat → Bool
  | [], _ => true
  | a :: l, i => Nat.beq a (Rf i) && listIs Rf l (i + 1)

@[expose] noncomputable def regsV (c : Lay) (V P T : Nat → Nat) (N n : Nat) (prog : List Op)
    (Rf : Nat → Nat) : Bool :=
  let r := replayK c V P T N prog 0 (initK n)
  decide (N ≤ 1048576) && decide (2 ≤ n) && prog.all (Op.lt n) && r.1 && listIs Rf r.2 0

@[expose] noncomputable def factsFrom (c : Lay) (V P : Nat → Nat) (N : Nat) (R : Nat → Nat)
    (n : Nat) (H : Nat → Nat) (sel : MFact → Bool) : List MFact → Nat → Bool
  | [], _ => true
  | f :: fs, j => (!sel f || factV c V P N R n (H j) f) && factsFrom c V P N R n H sel fs (j + 1)

@[expose] noncomputable def chunkV (c : Lay) (V P : Nat → Nat) (N : Nat) (R : Nat → Nat) (n : Nat)
    (fs : List MFact) (H : Nat → Nat) (sel : MFact → Bool) (k i : Nat) : Bool :=
  factsFrom c V P N R n H sel ((fs.drop (i * k)).take k) (i * k)

end CFSG.KC.LocalComp.FactsV

end
