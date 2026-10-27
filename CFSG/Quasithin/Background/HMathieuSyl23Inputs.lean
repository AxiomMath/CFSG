module

public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuPred
public meta import CFSG.Monster.Code.Basis

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

@[expose] def T23s2 : PT 24 := PT.ofGens 24
  [#[0, 22, 2, 7, 16, 10, 12, 3, 1, 18, 9, 13, 21, 11, 6, 8, 19, 17, 5, 20, 4, 14, 15, 23],
    #[0, 16, 17, 3, 15, 14, 5, 7, 6, 12, 4, 13, 22, 11, 8, 20, 18, 2, 19, 1, 10, 9, 21, 23],
    #[0, 21, 7, 2, 1, 14, 10, 17, 20, 12, 4, 13, 8, 11, 22, 6, 9, 3, 19, 15, 5, 18, 16, 23]] 64

@[expose] def T23s3 : PT 24 := PT.ofGens 24
  [#[0, 19, 14, 6, 2, 16, 13, 7, 17, 1, 5, 12, 18, 3, 4, 15, 10, 21, 11, 9, 20, 8, 22, 23],
    #[0, 19, 12, 3, 11, 2, 6, 20, 21, 1, 4, 10, 5, 13, 18, 7, 14, 8, 16, 9, 15, 17, 22, 23]] 16

@[expose] def T23s5 : PT 24 := PT.ofGens 24
  [#[0, 11, 17, 5, 18, 7, 1, 8, 9, 3, 4, 19, 6, 16, 10, 2, 15, 13, 20, 12, 14, 21, 22, 23]] 16

@[expose] def T23s7 : PT 24 := PT.ofGens 24
  [#[0, 9, 12, 1, 11, 19, 15, 18, 4, 5, 8, 13, 3, 17, 7, 20, 6, 21, 16, 2, 14, 10, 22, 23]] 16

@[expose] def T23s11 : PT 24 := PT.ofGens 24
  [#[0, 9, 19, 6, 10, 14, 21, 11, 2, 18, 8, 5, 16, 15, 20, 17, 4, 7, 12, 22, 3, 13, 1, 23]] 16

@[expose] def T23s23 : PT 24 := PT.ofGens 24
  [#[0, 12, 20, 5, 22, 4, 14, 3, 9, 19, 21, 23, 7, 6, 16, 8, 10, 18, 2, 1, 13, 15, 11, 17]] 32

end CFSG.Quasithin.H.Mathieu
