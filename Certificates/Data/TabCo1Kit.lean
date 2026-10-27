module

public import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public import CFSG.Sporadic.Schreier.Co1StabData
public import CFSG.Sporadic.Schreier.Co1AutData
public import CFSG.Sporadic.Co1Block.PermData
public import Certificates.Data.CFSGNative.Co1Schreier.Base
public import Certificates.Data.CFSGNative.Co1.TwoB
public import Std.Data.HashSet
public meta import CFSG.Sporadic.Schreier.Co1ThreeLocalInputs
public meta import CFSG.Sporadic.Schreier.Co1StabData
public meta import CFSG.Sporadic.Schreier.Co1AutData
public meta import CFSG.Sporadic.Co1Block.PermData
public meta import Certificates.Data.CFSGNative.Co1Schreier.Base
public meta import Certificates.Data.CFSGNative.Co1.TwoB
public meta import Std.Data.HashSet

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Schreier.Data
  CFSG.Sporadic.Co1Block

@[expose] def shiftL (w : List Int) : List Int :=
  w.map fun l => if 0 < l then l + 2 else l - 2

@[expose] def chainDerivs (_ : Unit := ()) : List (List Int) :=
  [stabWord0.map (fun n : Nat => (n : Int)), stabWord1.map (fun n : Nat => (n : Int))] ++
    stabDerivs.map shiftL

@[expose] def kDag (ext : List (List Int)) : List Rows × List Rows × Bool :=
  dag [aR, bR] (chainDerivs () ++ ext)

@[expose] def nd (D : List Rows × List Rows × Bool) (i : Nat) : Rows := D.1.getD (i - 1) (one ())

@[expose] def ndI (D : List Rows × List Rows × Bool) (i : Nat) : Rows := D.2.1.getD (i - 1) (one ())

@[expose] def evalW (D : List Rows × List Rows × Bool) (idx : List Nat) (w : List Int) : Rows :=
  word (idx.map (nd D)) (idx.map (ndI D)) w

@[expose] def xsSet (_ : Unit := ()) : Std.HashSet Nat := Std.HashSet.ofList certVecs.toList

@[expose] def typN (xs : Std.HashSet Nat) (v : Nat) : Nat :=
  if v == 0 then 0 else if xs.contains v then 2 else 3

abbrev Cond := List Nat × List (Nat × Nat)

@[expose] def slotN (cs : Array (Array Nat)) (base : List Nat) (s : Nat × Nat) : Nat :=
  vecMulN 24 (cs.getD s.2 #[]) (base.getD s.1 0)

@[expose] def fN (cs : Array (Array Nat)) (base : List Nat) (F : List (Nat × Nat)) : Nat :=
  F.foldl (fun acc s => acc ^^^ slotN cs base s) 0

@[expose] def combN (cs : Array (Array Nat)) (S : List Nat) (F x : Nat) : Nat :=
  S.foldl (fun acc a => acc ^^^ vecMulN 24 (cs.getD a #[]) x) F

@[expose] def candList (xs : Std.HashSet Nat) (cs : Array (Array Nat)) (base : List Nat) (u : Nat)
    (conds : List Cond) : List Nat :=
  conds.foldl (fun cand c =>
    cand.filter fun x =>
      typN xs (combN cs c.1 (fN cs base c.2) x) == typN xs (combN cs c.1 (fN cs base c.2) u))
    certVecs.toList

@[expose] def lvlOK (xs : Std.HashSet Nat) (cs : Array (Array Nat)) (base : List Nat) (i : Nat)
    (conds : List Cond) (cnt : Nat) : Bool :=
  xs.contains (base.getD i 0) &&
    decide ((candList xs cs (base.take i) (base.getD i 0) conds).length ≤ cnt)

@[expose] def spanOK (cs : Array (Array Nat)) (nb : Nat) (base : List Nat)
    (span : List (Nat × Nat)) (comb : List Nat) : Bool :=
  decide (span.length = 24) && decide (comb.length = 24) &&
    span.all (fun s => decide (s.1 < base.length) && decide (s.2 < nb)) &&
    (List.range 24).all fun l =>
      vecMulN 24 (span.map (slotN cs base)).toArray (comb.getD l 0) == 1 <<< l

@[expose] def colsOf (rs : List Rows) : Array (Array Nat) := rs.toArray.map (transposeRows 24)

@[expose] def powList (kR : Rows) (n : Nat) : List Rows := (List.range n).map (pow kR)

@[expose] def boundOK (cs : Array (Array Nat)) (nb : Nat) (base : List Nat)
    (conds : List (List Cond)) (cnts : List Nat) (span : List (Nat × Nat))
    (comb : List Nat) : Bool :=
  let xs := xsSet ()
  decide (cs.size = nb) && decide (conds.length = base.length) &&
    decide (cnts.length = base.length) &&
    (List.range base.length).all (fun i => lvlOK xs cs base i (conds.getD i []) (cnts.getD i 0)) &&
    spanOK cs nb base span comb

end CFSG.HardMathSupport.Dickson.I271.TabCo1
