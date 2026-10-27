module

public import CFSG.Quasithin.H13.A5M12Inputs
public import CFSG.Quasithin.Vol2.Ch10SecQ1M12Data

public section

namespace CFSG.Quasithin.H13.A5.M12

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.Vol2.Ch10.SecA.C10P01

@[expose] def okPair (a b : Array ℕ) : Bool :=
  autArrOK a b &&
    (permM a dodecadMask == dodecadMask || permM a dodecadMask == dodecadMask ^^^ (2 ^ 24 - 1))

@[expose] def T12s2 : PT 24 := PT.ofGens 24
  [#[21, 9, 4, 3, 7, 5, 12, 16, 22, 19, 14, 23, 11, 18, 10, 15, 2, 1, 13, 17, 20, 8, 0, 6],
    #[12, 2, 1, 5, 9, 3, 22, 19, 23, 4, 14, 21, 0, 18, 10, 20, 17, 16, 13, 7, 15, 11, 6, 8],
    #[7, 23, 21, 13, 0, 10, 19, 22, 2, 6, 15, 1, 9, 20, 3, 18, 8, 11, 5, 12, 14, 16, 4, 17],
    #[21, 17, 7, 15, 4, 5, 11, 2, 22, 19, 14, 6, 12, 13, 10, 3, 16, 1, 18, 9, 20, 0, 8, 23]] 64

@[expose] def T12s3 : PT 24 := PT.ofGens 24
  [#[12, 16, 4, 1, 19, 17, 23, 9, 13, 15, 11, 21, 14, 18, 0, 7, 3, 20, 8, 2, 5, 10, 6, 22],
    #[12, 16, 19, 9, 2, 7, 18, 20, 21, 15, 22, 10, 14, 8, 0, 3, 17, 1, 23, 4, 5, 13, 11, 6]] 32

@[expose] def T12s5 : PT 24 := PT.ofGens 24
  [#[0, 3, 4, 20, 17, 15, 10, 2, 8, 9, 21, 6, 13, 18, 11, 1, 7, 16, 23, 19, 5, 14, 12, 22]] 16

@[expose] def T12s11 : PT 24 := PT.ofGens 24
  [#[8, 4, 19, 9, 7, 1, 18, 3, 11, 2, 12, 21, 14, 13, 6, 17, 16, 5, 22, 20, 15, 23, 0, 10]] 16

@[expose] def matsOf12 (T : PT 24) : Array (List ℕ) := T.elems.map fun a => matOf 10 (actC12 a)

end CFSG.Quasithin.H13.A5.M12
