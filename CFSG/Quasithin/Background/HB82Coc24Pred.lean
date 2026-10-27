module

public import CFSG.Quasithin.Background.HMathieuSyl24Base

public section

namespace CFSG.Quasithin.H.Coc24

open CFSG.Quasithin.H.Mathieu CFSG.QuasithinUnique.Setup.X1

@[expose] def uTMasks : List ℕ := [0, 39, 219, 252, 1108, 1139, 1167, 1192]

@[expose] def predKT (l : List T24s2.Elem) : Bool :=
  l.length != 6 || (fixMasks24 l).length != 8 || fixMasks24 l == uTMasks

@[expose] def t24PresUT : Bool :=
  (List.finRange T24s2.n).all fun i =>
    uTMasks.all fun m => uTMasks.contains (act24s2 (T24s2.elemEquiv.symm i) m)

@[expose] def t24Fix : Bool :=
  ((List.range (2 ^ 11)).filter fun m =>
    (List.finRange T24s2.n).all fun i => act24s2 (T24s2.elemEquiv.symm i) m == m) == [0, 1192]

end CFSG.Quasithin.H.Coc24
