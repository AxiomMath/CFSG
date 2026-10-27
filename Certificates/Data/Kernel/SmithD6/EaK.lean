module

public import Certificates.Data.Kernel.SmithD6.StabTreeK
public import Certificates.Data.Kernel.SmithD6.EaData
public import Certificates.Data.Kernel.SmithD6.RepsK
public import Certificates.Data.SmithD6E23a

public section

namespace CFSG.KD.SmithD6Ea

open CFSG.SmithD6 CFSG.KC.KeyTree CFSG.KD.SmithD6 CFSG.KD.SmithD6Stab CFSG.KD.SmithD6ST
  CFSG.KD.SmithD6Reps

@[expose] noncomputable def eaInK (k : Nat) : Bool :=
  bAnd(Nat.beq (imgN k 4098) 4098, Nat.beq (imgN k 262272) 262272)

@[expose] noncomputable def isNilL (l : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun _ _ _ => false) l

@[expose] noncomputable def eaGo (l : List Nat) : List Nat → Bool :=
  List.rec (motive := fun _ => List Nat → Bool) isNilL
    (fun k _ ih ps => bIf(eaInK k,
      List.rec (motive := fun _ => Bool) false (fun h t _ => bAnd(Nat.beq h k, ih t)) ps,
      ih ps)) l

@[expose] noncomputable def eaChunkOK (c : Nat) : Bool :=
  eaGo (nthC J.lineKeysC c) (nthC JEA.eaKC c)

@[expose] def eaRestr (pr : Nat × Nat) : List Nat :=
  ea7Bits.map fun m => applyCols (tvColsP pr) (2 ^ m)

@[expose] def packL (l : List Nat) : Nat := l.foldl (fun a r => a * 4294967296 + r) 0

@[expose] noncomputable def eaF4Go : List Nat → Nat → Bool
  | [], _ => true
  | k :: ks, prev => lineTree.memB k && eaInK k && decide (prev < packL (eaRestr (pairK k))) &&
      eaF4Go ks (packL (eaRestr (pairK k)))

@[expose] noncomputable def eaF4OK : Bool := JEA.eaQ.length == 1578 && eaF4Go JEA.eaQ 0

@[expose] noncomputable def eaF3OK (k : Nat) (r : List Nat) : Bool :=
  wtTree.memB (r.getD 0 0) &&
  applyCols (tvColsP (1, 2)) (r.getD 0 0) == r.getD 0 0 &&
  applyCols (tvColsP (64, 128)) (r.getD 0 0) == r.getD 0 0 &&
  decide (r.getD 1 0 < 2 ^ 32) &&
  (applyCols (tvColsP (pairK k)) (r.getD 1 0) ^^^ r.getD 1 0) == r.getD 0 0

@[expose] noncomputable def eaF3All : Bool :=
  JEA.eaF3.length == JEA.eaQ.length && (JEA.eaQ.zip JEA.eaF3).all fun x => eaF3OK x.1 x.2

@[expose] def eaDiffP (p : Nat × Nat) (m : Nat) : Nat := (tvColsP p)[m]! ^^^ 2 ^ m

@[expose] def eaPivotP (p : Nat × Nat) : Bool :=
  (List.range 32).all fun m₀ => eaDiffP p m₀ == 0 ||
    (List.range 32).any fun j => (eaDiffP p m₀).testBit j &&
      (List.range 32).all fun m => m == m₀ || !(eaDiffP p m).testBit j

@[expose] noncomputable def eaCBWOK : Bool :=
  eaPivotP (1, 2) && eaPivotP (64, 128) &&
  ((List.range 32).all fun m => ea7Bits.contains m == (eaDiffP (1, 2) m == 0 &&
    eaDiffP (64, 128) m == 0)) &&
  ea7Bits.all fun m => wtTree.memB (2 ^ m)

@[expose] noncomputable def keyAt (p : Nat) : Nat := (nthC J.lineKeysC (p / 2048)).getD (p % 2048) 0

@[expose] noncomputable def eaInF0K (p : Nat) : Bool :=
  p == 0 || p == 31899 || (decide (p < 365211) && eaInK (keyAt p))

@[expose] def eaRigP (inF0 : Nat → Bool) (pair : Nat → Nat × Nat) : Bool :=
  (List.range 12).all (fun i => ea7RigData.any fun t => t.1 == 2 ^ i) &&
  ea7RigData.all fun t => inF0 t.2.1 && inF0 t.2.2 &&
    [(pair t.2.1).1, (pair t.2.1).2, (pair t.2.1).1 ^^^ (pair t.2.1).2].contains t.1 &&
    [(pair t.2.2).1, (pair t.2.2).2, (pair t.2.2).1 ^^^ (pair t.2.2).2].contains t.1 &&
    [(pair t.2.1).1, (pair t.2.1).2, (pair t.2.1).1 ^^^ (pair t.2.1).2].all fun y =>
      ![(pair t.2.2).1, (pair t.2.2).2, (pair t.2.2).1 ^^^ (pair t.2.2).2].contains y || y == t.1

@[expose] def eaBaseK : List Nat := [2230296, 67876, 6424848, 4224, 12480]

@[expose] noncomputable def eaInYK (bs : List Nat) (g : Nat) : Bool :=
  eaInK g && bs.all fun b => imgN g b == b

@[expose] noncomputable def eaEdge (t g a b : Nat) : Bool :=
  lineTree.memB g && eaInYK (eaBaseK.take t) g && lineTree.memB a && lineTree.memB b &&
    imgN g a == b

@[expose] def eaRec (l : List Nat) : Nat × Nat × Nat × Nat :=
  (l.getD 0 0, l.getD 1 0, l.getD 2 0, l.getD 3 0)

@[expose] def eaIncr : List Nat → Nat → Bool
  | [], _ => true
  | k :: ks, prev => decide (prev < k) && eaIncr ks k

@[expose] noncomputable def eaLvOK (t : Nat) : Bool :=
  let rs := (JEA.eaLv.getD t []).map eaRec
  rs.length == ea7Sizes.getD t 0 && eaIncr (rs.map (·.1)) 0 &&
    reachK (fun x => x == eaBaseK.getD t 0) (eaEdge t) (KT.ofList rs.length (depths rs)) rs

@[expose] def eaAK : List Nat := [4224, 8256, 12480]

@[expose] noncomputable def eaAOK : Bool :=
  JEA.eaQ.all fun q => eaAK.all fun a => eaAK.contains (imgN q a)

end CFSG.KD.SmithD6Ea

end
