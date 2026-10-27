module

public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import CFSG.Quasithin.Background.HSporLatInputs

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.Quasithin.H.MathieuLat CFSG.QuasithinUnique.Ch1.SporLat
  CFSG.QuasithinUnique.K1.SporadicPerm

@[expose] def m22Wit : Idx3Wit where
  p := 2
  xw := [3, 1]
  rw := [[], [0], [2], [2, 0], [0, 0]]
  ri := [[], [0, 0, 0], [2], [0, 2, 0, 0], [0, 0]]
  czv := [true, false, false, false, true]

@[expose] def m22Check : Prop :=
  m22Wit.Ok 22 (codeSetAct 22) m22Delta m22Lat m22SLP[163]!

instance : Decidable m22Check :=
  inferInstanceAs (Decidable (m22Wit.Ok 22 (codeSetAct 22) m22Delta m22Lat m22SLP[163]!))

end CFSG.Quasithin.S151S9T
