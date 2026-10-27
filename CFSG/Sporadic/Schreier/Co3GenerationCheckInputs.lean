module

public import CFSG.Sporadic.Schreier.Co3SecondCheck
public import CFSG.Sporadic.Schreier.M12Data
public import CFSG.Sporadic.Schreier.CountSpec
public import Certificates.Data.CFSGNative.SporadicSchreier.Count
public meta import CFSG.Sporadic.Schreier.Co3SecondCheck
public meta import CFSG.Sporadic.Schreier.M12Data
public meta import CFSG.Sporadic.Schreier.CountSpec
public meta import Certificates.Data.CFSGNative.SporadicSchreier.Count
public meta import CFSG.Sporadic.Schreier.ImagePairs
public import CFSG.Sporadic.Schreier.ImagePairs

public section

namespace CFSG.Sporadic.Schreier.Co3

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.Schreier.Co3.Native
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Schreier

@[expose] def co3JointBaseArr : Array Nat :=
  ((co3FinList 276 (by decide) co3JointBase).map Fin.val).toArray

@[expose] def co3MM1Gens : Array (Array Nat) := co3MArrs.extract 0 7 ++ co3M1Arrs.extract 0 6

@[expose] def co3D0Kappa1 : Array (Array Nat) :=
  Array.ofFn (n := 5) fun k => renameA 12 co3C12Arr (restrictA co3ItArr co3D0Arrs[k.val]!)

@[expose] def co3ToT (a : Array Nat) : Table := a.map UInt32.ofNat

@[expose] def co3D0Test (T : Table) : Bool :=
  allLt 5 fun k => allLt 12 fun i =>
    ap (compT 12 T (co3ToT co3D0Kappa1[k]!)) i == ap (compT 12 (co3ToT co3D0Kappa1[k]!) T) i

end CFSG.Sporadic.Schreier.Co3
