module

public import Certificates.Data.Kernel.SmithL6K
public import Certificates.Data.Kernel.SmithL6Coll
public import Certificates.Data.SmithL6Orbit

public section

namespace CFSG.SmithL6.K

open CFSG.SmithL6 CFSG.SmithL6.CollK

@[expose] def parT : Nat := 7608434000728254870

@[expose] def conjF (p q : Nat) : Nat :=
  64 * (if parT.testBit (p % 64 &&& q / 64) then q / 64 ^^^ p / 64 else q / 64) +
    (if parT.testBit (q % 64 &&& p / 64) then q % 64 ^^^ p % 64 else q % 64)

@[expose] noncomputable def uaWC : List Nat → Nat → Nat → Nat :=
  fun G => List.rec (motive := fun _ => Nat → Nat → Nat) (fun _ c => c)
    (fun g _ ih a c => bif a.testBit 0 then conjF g (ih (a / 2) c) else ih (a / 2) c) G

@[expose] def ugC (T : List Nat) : List Nat := ugens.toList.map (T.getD · 0)

@[expose] def uaRC (T P : List Nat) : List (Nat × Nat) := uco.toList.zip (P.map (T.getD · 0))

@[expose] def uaFixC (T P : List Nat) : Bool :=
  let PC := P.map (T.getD · 0)
  PC.all fun p => PC.all fun q => conjF p q == q

@[expose] noncomputable def uaRowsC (G T : List Nat) (R : List (Nat × Nat)) : Bool :=
  R.all fun r => T.all fun c => uaWC G r.1 c == conjF r.2 c

@[expose] noncomputable def uaMoveC (G T : List Nat) : Bool :=
  (List.range 512).all fun a => a == 0 || T.any fun c => uaWC G a c != c

@[expose] def uaCommC (T P : List Nat) : Bool :=
  let PC := P.map (T.getD · 0)
  T.zipIdx.all fun r => !(PC.all fun p => conjF p r.1 == r.1) || P.contains r.2

@[expose] def uaPlanesK (PL : List (List Nat)) (W : List Nat) : Bool :=
  (List.range 1395).all fun j => j == 0 || PL.any fun L => apK L (W.getD j 0) != W.getD j 0

end CFSG.SmithL6.K
