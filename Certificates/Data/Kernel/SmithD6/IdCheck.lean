module

public import Certificates.Data.SmithD6IdCv
public import Certificates.Data.SmithD6IdQa
public import Certificates.Data.Kernel.SmithD6.WtCheck
public import Certificates.Data.Kernel.SmithD6.Trees

public section

namespace CFSG.KD.SmithD6

open CFSG.SmithD6 CFSG.KC.KeyTree

@[expose] noncomputable def unexGo (x : Nat) (es : List Nat) : Nat → Nat :=
  List.rec (motive := fun _ => Nat → Nat) (fun _ => 0)
    (fun e _ ih k => Nat.lor (Nat.shiftLeft (Nat.land (Nat.shiftRight x e) 1) k) (ih (Nat.succ k)))
    es

@[expose] noncomputable def unexC (x : Nat) : Nat := unexGo x evL 0

@[expose] def rev32 (d : Nat) : Nat := xorFold 32 fun t => bif d.testBit (31 - t) then 2 ^ t else 0

@[expose] def pfold (k x : Nat) : Nat := Nat.xor x (Nat.shiftRight x k)

@[expose] def fBK (s r : Nat) : Bool :=
  Nat.testBit (pfold 1 (pfold 2 (pfold 4 (pfold 8 (pfold 16 (Nat.land s r)))))) 0

@[expose] noncomputable def id7VecK (u w x : Nat) : Nat := unexC (rhoK u (rhoK w (exC x)))

@[expose] noncomputable def id7VecOK (u w x : Nat) : Bool :=
  bAnd(Nat.blt (id7VecK u w x) 4294967296,
    Nat.beq (exC (id7VecK u w x)) (rhoK u (rhoK w (exC x))))

@[expose] noncomputable def id7FLineK (u w : Nat) : Bool :=
  decide (u < 4096) && decide (w < 4096) && (u &&& 63 == 0) && (w &&& 63 == 0) &&
    lineTree.memB (4096 * u + w)

@[expose] noncomputable def id7CvGenK (g : Nat × Nat × Nat) : Bool :=
  id7FLineK g.1 g.2.1 && decide (g.2.2 < 32) && id7VecOK g.1 g.2.1 (2 ^ g.2.2)

@[expose] noncomputable def id7CvVecsK (gs : List (Nat × Nat × Nat)) : Array Nat :=
  (gs.map fun g => id7VecK g.1 g.2.1 (2 ^ g.2.2)).toArray

@[expose] noncomputable def id7CvProjK (gs : List (Nat × Nat × Nat)) (D : Array Nat) (w : Nat) :
    Nat :=
  (List.range 31).foldl (fun acc t => if fB w (id7CvVecsK gs)[t]! then acc ^^^ D[t]! else acc) 0

@[expose] noncomputable def id7CvChkG (gs : List (Nat × Nat × Nat)) (D : Array Nat) : Bool :=
  gs.length == 31 && D.toList.length == 31 && gs.all id7CvGenK &&
    (List.range 32).all fun m =>
      2 ^ m ^^^ id7CvProjK gs D (2 ^ m) == 0 || 2 ^ m ^^^ id7CvProjK gs D (2 ^ m) == 1

@[expose] noncomputable def id7ChkCvK : Bool := id7CvChkG id7CvGens.toList id7CvDual

@[expose] noncomputable def id7WtK (k : Nat) : Nat := (nthC J.wtC (k / 2048)).getD (k % 2048) 0

@[expose] noncomputable def id7QaGenK (g : Nat × Nat × Nat) : Bool :=
  id7FLineK g.1 g.2.1 && decide (g.2.2 < 75735) &&
    Nat.beq (wtTree.find (id7WtK g.2.2)) (g.2.2 + 1) && decide (id7WtK g.2.2 < 4294967296) &&
    !fB 1 (id7WtK g.2.2) && id7VecOK g.1 g.2.1 (id7WtK g.2.2)

@[expose] noncomputable def id7QaVecsK (gs : List (Nat × Nat × Nat)) : Array Nat :=
  (gs.map fun g => id7VecK g.1 g.2.1 (id7WtK g.2.2)).toArray

@[expose] noncomputable def id7QaHeadG (gs : List (Nat × Nat × Nat)) (D : Array Nat) : Bool :=
  gs.length == 16 && D.toList.length == 16 && gs.all id7QaGenK && Nat.beq (wtTree.find 1) 1 &&
    (List.range 16).all fun s => (List.range 16).all fun t =>
      fB (id7QaVecsK gs)[s]! D[t]! == (s == t)

@[expose] noncomputable def id7QaHeadK : Bool := id7QaHeadG id7QaGens.toList id7QaDual

@[expose] noncomputable def id7QaPairs : List (Nat × Nat) :=
  (List.range 16).map fun t => (rev32 id7QaDual[t]!, (id7QaVecsK id7QaGens.toList)[t]!)

@[expose] noncomputable def id7ProjP (ps : List (Nat × Nat)) (s : Nat) : Nat :=
  List.rec (motive := fun _ => Nat) 0 (fun p _ ih => Nat.xor (nIf(fBK s p.1, p.2, 0)) ih) ps

@[expose] noncomputable def id7QaWtOK (ps : List (Nat × Nat)) (s : Nat) : Bool :=
  bIf(bIf(Nat.beq s 1, true, KT.memB (Nat.xor 1 s) wtTree),
    Nat.beq (id7ProjP ps s) s, bIf(Nat.beq (id7ProjP ps s) s, false, true))

@[expose] noncomputable def id7QaGo (ps : List (Nat × Nat)) (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun s _ ih => bAnd(id7QaWtOK ps s, ih)) l

@[expose] noncomputable def id7QaChunkOK (c : Nat) : Bool := id7QaGo id7QaPairs (nthC J.wtC c)

end CFSG.KD.SmithD6

end
