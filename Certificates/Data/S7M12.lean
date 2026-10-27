module

public import Certificates.Data.S5RowsM12
public import Certificates.Data.S7Q8

public section

namespace Certificates.S7M12

open CFSG.Blueprint CFSG.Sporadic.Mathieu CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf
  Certificates.S5Rows Certificates.S5RowsM12 Certificates.S7Q8

@[expose] def i1 : NativeSporadic.M12 := M12Model.eltM 27

@[expose] def j1 : NativeSporadic.M12 := M12Model.eltM 48

@[expose] def i2 : NativeSporadic.M12 := M12Model.eltM 4

@[expose] def j2 : NativeSporadic.M12 := M12Model.eltM 38

@[expose] def conjL (_ : Unit := ()) : List NativeSporadic.M12 :=
  [M12Model.wM [], M12Model.wM [2, 0, 2, 0, 1], M12Model.wM [2, 0, 1, 0, 1]]

@[expose] def edgeE (_ : Unit := ()) : NativeSporadic.M12 :=
  M12Model.wM [2, 0, 1, 0, 1]

@[expose] def factAL (_ : Unit := ()) : List NativeSporadic.M12 :=
  let e := edgeE ()
  let d := M12Model.d0
  [e, d, e⁻¹, M12Model.eltM 1, d, e⁻¹, d, e, d, e⁻¹, M12Model.eltM 3, d, e⁻¹, d]

@[expose] def factBL (_ : Unit := ()) : List NativeSporadic.M12 :=
  let e := edgeE ()
  let d := M12Model.d0
  [d, e⁻¹, d, e, d, e⁻¹, d, e]

@[expose] def m12S7Basic (_ : Unit := ()) : Bool :=
  q8RelB i1 j1 && q8RelB i2 j2 && decide (i1 * i1 = M12Model.eltM 22) &&
    decide (i2 * i2 = M12Model.eltM 22) &&
    (q8Span i2 j2).all fun x => M12Model.fp x != M12Model.fp i1

@[expose] def m12S7Class1 (_ : Unit := ()) : Bool :=
  classCheck i1 j1 (sylowL ()) (conjL ())

@[expose] def m12S7Class2 (_ : Unit := ()) : Bool :=
  classCheck i2 j2 (sylowL ()) (conjL ())

@[expose] def m12S7Norm (_ : Unit := ()) : Bool :=
  let c := czL ()
  normAllB i1 j1 c && normAllB i2 j2 c

@[expose] def m12S7Q8 (_ : Unit := ()) : Bool :=
  q8InCheck (sylowL ()) i1 j1 i2 j2 && q8InCheck (czL ()) i1 j1 i2 j2

@[expose] def m12S7Edge (_ : Unit := ()) : Bool :=
  let e := edgeE ()
  edgeB i1 j1 i2 j2 e && factB i1 j1 i2 j2 [e] m12a (factAL ()) &&
    factB i1 j1 i2 j2 [e] m12b (factBL ())

end Certificates.S7M12
