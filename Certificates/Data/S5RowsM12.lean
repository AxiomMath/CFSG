module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf45M12Model
public import Certificates.Data.S5Rows
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace Certificates.S5RowsM12

open CFSG.Blueprint CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.FrameAEmptyPf Certificates.S5Rows

@[expose] def sylowL (_ : Unit := ()) : List NativeSporadic.M12 :=
  (List.range 64).map M12Model.eltM

@[expose] def czL (_ : Unit := ()) : List NativeSporadic.M12 :=
  (List.range 64).flatMap fun x =>
    [M12Model.eltM x, M12Model.eltM x * M12Model.d0, M12Model.eltM x * M12Model.d0 * M12Model.d0]

@[expose] def m12RowsF2a (_ : Unit := ()) : Bool :=
  threeCycCheck (sylowL ()) (czL ()) fun _ => true

@[expose] def m12RowsF2b (_ : Unit := ()) : Bool :=
  invPairCheck (sylowL ()) M12Model.fp

end Certificates.S5RowsM12
