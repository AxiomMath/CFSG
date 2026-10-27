module

public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Monster.Code.Basis

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

@[expose] def gens22s2 : List (Array ℕ) :=
  [#[1, 0, 11, 23, 7, 21, 9, 4, 18, 6, 14, 2, 20, 19, 10, 17, 22, 15, 8, 13, 12, 5, 16, 3],
    #[0, 1, 14, 12, 4, 18, 16, 7, 23, 22, 9, 10, 5, 19, 6, 17, 2, 15, 3, 13, 21, 8, 11, 20],
    #[0, 1, 11, 9, 7, 21, 23, 4, 20, 6, 22, 5, 18, 19, 12, 15, 14, 17, 16, 13, 10, 2, 8, 3],
    #[0, 1, 18, 22, 17, 14, 20, 15, 11, 16, 21, 10, 9, 13, 2, 7, 23, 4, 5, 19, 3, 8, 6, 12]]

@[expose] def T22s2 : PT 24 := PT.ofGens 24 gens22s2 64

@[expose] def T22s3 : PT 24 := PT.ofGens 24
  [#[0, 1, 16, 18, 15, 5, 6, 13, 10, 11, 21, 22, 4, 14, 7, 12, 19, 3, 17, 2, 20, 8, 9, 23],
    #[0, 1, 19, 18, 7, 6, 20, 21, 15, 9, 12, 11, 14, 8, 10, 13, 2, 3, 17, 16, 5, 4, 22, 23]] 16

@[expose] def T22s5 : PT 24 := PT.ofGens 24
  [#[0, 1, 8, 11, 10, 9, 3, 2, 19, 16, 6, 4, 7, 5, 17, 18, 21, 20, 14, 12, 15, 13, 22, 23]] 16

@[expose] def T22s7 : PT 24 := PT.ofGens 24
  [#[0, 1, 6, 18, 7, 21, 20, 19, 3, 8, 22, 12, 13, 16, 15, 5, 17, 10, 4, 9, 14, 2, 11, 23]] 16

@[expose] def T22s11 : PT 24 := PT.ofGens 24
  [#[0, 1, 23, 16, 13, 10, 2, 4, 7, 6, 17, 22, 11, 12, 3, 5, 18, 8, 20, 9, 19, 14, 15, 21]] 16

end CFSG.Quasithin.H.Mathieu
