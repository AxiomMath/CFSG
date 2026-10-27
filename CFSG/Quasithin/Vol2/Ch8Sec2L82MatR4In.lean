module

public import CFSG.Quasithin.Background.HB82Coc24Pred

public section

namespace CFSG.Quasithin.H13.Mat

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Coc24 CFSG.QuasithinUnique.Setup.X1

@[expose] def r4L9 : List ℕ := [2015, 1642, 1113, 1245, 1350, 1359, 1596, 922, 1288]

@[expose] def chainCommIn24 (B : List ℕ) (s : T24s2.Elem) : Bool :=
  (List.range 11).all fun j => (combos B).contains (act24s2 s (2 ^ j) ^^^ 2 ^ j)

@[expose] def predMB24 (l : List T24s2.Elem) : Bool :=
  predKT l && (l.length != 6 || (fixMasks24 l).length != 8 || l.all (chainCommIn24 r4L9))

end CFSG.Quasithin.H13.Mat
