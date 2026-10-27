module

public import CFSG.Quasithin.EmptyFaithful.S151S9TData
public import CFSG.Quasithin.Background.HSporLatInputs

public section

namespace CFSG.Quasithin.S151S9T

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.H.MathieuLat

@[expose] def m23Wit : Idx3Wit where
  p := 10
  xw := [3]
  rw := [[], [0], [1, 2], [1, 1], [2, 1]]
  ri := [[], [0], [1, 1, 2, 1], [2, 1, 1, 2], [0, 2, 1, 0]]
  czv := [true, false, false, false, true, false, false, false, false, false, false, true, true,
    false, false, false]

@[expose] def m23Check : Prop :=
  m23Wit.Ok 23 (codeSetAct 23) m23Delta m23Lat m23SLP[159]!

instance : Decidable m23Check :=
  inferInstanceAs (Decidable (m23Wit.Ok 23 (codeSetAct 23) m23Delta m23Lat m23SLP[159]!))

end CFSG.Quasithin.S151S9T
