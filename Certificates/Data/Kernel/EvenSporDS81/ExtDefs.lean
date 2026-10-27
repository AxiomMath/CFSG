module

public import Certificates.Data.Kernel.EvenSporDS81.FCDefs

public section

namespace CFSG.KC.EvenSporDS81

open CFSG.EvenSporadicStandard.TwoFi22.DS81

@[expose] def extOKG (T : List (List Nat)) (e n : Nat) (F fam : List (List Nat)) : Bool :=
  F.all fun Y => (List.range n).all fun y =>
    !(getT T y y == e && !Y.contains y && Y.all fun x => getT T y x == getT T x y) ||
      fam.contains (extL T Y y)

@[expose] def axHeadL (ms : List (Array Nat)) (fam : List (List Nat)) : Bool :=
  let e := idxL ms idColsK
  decide (ms.length = 2 ^ 8) && ms.all fcColsLt && decide (e < ms.length) && fam.contains [e]

end CFSG.KC.EvenSporDS81
