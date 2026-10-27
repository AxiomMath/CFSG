module

public import Certificates.Data.CFSGNative.SporadicSchreier.Classes

public section

namespace CFSG.SectionRank.QTK.Insp443.PermKit.Native

open CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native

@[expose] def compEqN (n : Nat) (T b u : Table) : Bool :=
  allIn 0 n fun i => ap T (ap b i) == ap u (ap T i)

@[expose] def commT2 (n : Nat) (S T : Table) : Bool := tblEq n (compT n S T) (compT n T S)

@[expose] def commAllT (n : Nat) (bs : List Table) (T : Table) : Bool :=
  bs.all fun b => commT2 n T b

@[expose] def inSp (n : Nat) (sp : List Table) (T : Table) : Bool := sp.any fun u => tblEq n u T

@[expose] def conjIn (n : Nat) (bs sp : List Table) (T : Table) : Bool :=
  bs.all fun b => sp.any fun u => compEqN n T b u

@[expose] def centTestS (n : Nat) (us spW : List Table) (T : Table) : Bool :=
  commAllT n us T && !(inSp n spW T)

@[expose] def sixTestS (n : Nat) (ws spW : List Table) (ds spD : List (List Table)) (T : Table) :
    Bool :=
  conjIn n ws spW T &&
    (!((List.range 6).all fun r => (List.range 6).any fun s =>
        conjIn n (ds.getD r []) (spD.getD s []) T) ||
      (((List.range 6).all fun r => conjIn n (ds.getD r []) (spD.getD r []) T) &&
        !(inSp n spW T)))

@[expose] def bsum : List Nat → Nat → Nat → Bool
  | [], _, _ => false
  | r :: rs, m, p => xor (m % 2 == 1 && r.testBit p) (bsum rs (m / 2) p)

@[expose] def dot3 (d p : Nat) : Bool :=
  xor (xor (d.testBit 0 && p.testBit 0) (d.testBit 1 && p.testBit 1)) (d.testBit 2 && p.testBit 2)

@[expose] def mtp (d0 d1 d2 p : Nat) : Nat :=
  (if dot3 d0 p then 1 else 0) + (if dot3 d1 p then 2 else 0) + (if dot3 d2 p then 4 else 0)

@[expose] def fanoEqOK (n : Nat) (ws spW as spA : List Table) (rows : List Nat) (T : Table) :
    Bool :=
  allIn 0 spA.length fun d0 => !(compEqN n T (as.getD 0 #[]) (spA.getD d0 #[])) ||
    allIn 0 spA.length fun d1 => !(compEqN n T (as.getD 1 #[]) (spA.getD d1 #[])) ||
      allIn 0 spA.length fun d2 => !(compEqN n T (as.getD 2 #[]) (spA.getD d2 #[])) ||
        allIn 0 ws.length fun j => allIn 0 spW.length fun m =>
          !(compEqN n T (ws.getD j #[]) (spW.getD m #[])) ||
            allIn 1 8 fun p => bsum rows m p == (rows.getD j 0).testBit (mtp d0 d1 d2 p)

@[expose] def fanoTestS (n : Nat) (ws spW as spA : List Table) (rows : List Nat) (T : Table) :
    Bool :=
  conjIn n ws spW T && (!(conjIn n as spA T) || !(fanoEqOK n ws spW as spA rows T))

@[expose] def anyTest (ts : List (Table → Bool)) (T : Table) : Bool := ts.any fun t => t T

end CFSG.SectionRank.QTK.Insp443.PermKit.Native

end
