module

public import Certificates.Data.TabCo1Kit
public meta import Certificates.Data.TabCo1Kit

public section

namespace CFSG.HardMathSupport.Dickson.I271.TabCo1

open CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1Schreier.Native CFSG.Sporadic.Co1Block

@[expose] def lvlOKF (xs : Std.HashSet Nat) (cs : Array (Array Nat)) (base : List Nat)
    (nfix i : Nat) (conds : List Cond) (cnt : Nat) : Bool :=
  xs.contains (base.getD i 0) &&
    (if i < nfix then decide (cnt = 1)
     else decide ((candList xs cs (base.take i) (base.getD i 0) conds).length ≤ cnt))

@[expose] def boundOKF (cs : Array (Array Nat)) (nb : Nat) (base : List Nat) (nfix : Nat)
    (conds : List (List Cond)) (cnts : List Nat) (span : List (Nat × Nat))
    (comb : List Nat) : Bool :=
  let xs := xsSet ()
  decide (cs.size = nb) && decide (conds.length = base.length) &&
    decide (cnts.length = base.length) &&
    (List.range base.length).all
      (fun i => lvlOKF xs cs base nfix i (conds.getD i []) (cnts.getD i 0)) &&
    spanOK cs nb base span comb

@[expose] def xFixList (R : Rows) : List Nat := certVecs.toList.filter fun v => act R v == v

@[expose] def fixesAll (R : Rows) (F : List Nat) : Bool := F.all fun v => act R v == v

end CFSG.HardMathSupport.Dickson.I271.TabCo1
