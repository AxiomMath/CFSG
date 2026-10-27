module

public import CFSG.Quasithin.Background.HMathieuPT24
public import CFSG.Quasithin.Background.HMathieuAvoid
public import CFSG.Quasithin.Background.HMathieuEnumAll
public meta import CFSG.Quasithin.Background.HMathieuPT24
public meta import CFSG.Quasithin.Background.HMathieuAvoid
public meta import CFSG.Quasithin.Background.HMathieuEnumAll
public meta import CFSG.Monster.Code.Basis

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

@[expose] def T24s2 : PT 24 := PT.ofGens 24
  [#[22, 7, 4, 21, 1, 16, 19, 2, 14, 10, 12, 11, 15, 13, 8, 9, 3, 18, 17, 0, 20, 5, 6, 23],
    #[7, 5, 10, 0, 1, 9, 19, 16, 17, 4, 12, 23, 22, 14, 18, 6, 3, 11, 20, 21, 13, 15, 2, 8],
    #[1, 21, 16, 19, 4, 22, 2, 7, 13, 6, 10, 17, 0, 14, 23, 15, 9, 20, 11, 3, 18, 12, 5, 8],
    #[12, 0, 6, 22, 7, 19, 9, 4, 11, 16, 15, 14, 21, 17, 20, 10, 2, 23, 13, 5, 8, 1, 3, 18]] 64

@[expose] def T24s3 : PT 24 := PT.ofGens 24
  [#[6, 2, 5, 0, 4, 1, 3, 7, 8, 9, 19, 18, 23, 22, 12, 13, 11, 10, 16, 17, 20, 21, 15, 14],
    #[1, 23, 6, 3, 22, 5, 14, 15, 20, 8, 7, 11, 12, 17, 2, 10, 16, 21, 18, 4, 9, 13, 19, 0]] 32

@[expose] def T24s5 : PT 24 := PT.ofGens 24
  [#[5, 7, 6, 4, 11, 10, 9, 8, 14, 13, 15, 12, 17, 19, 18, 16, 0, 3, 1, 2, 20, 21, 22, 23]] 16

@[expose] def T24s7 : PT 24 := PT.ofGens 24
  [#[12, 13, 20, 14, 5, 2, 19, 8, 3, 11, 16, 7, 10, 4, 17, 1, 18, 9, 6, 0, 15, 21, 22, 23]] 16

@[expose] def T24s11 : PT 24 := PT.ofGens 24
  [#[20, 3, 15, 18, 7, 17, 11, 19, 21, 16, 12, 0, 6, 2, 9, 1, 5, 13, 14, 10, 8, 4, 22, 23]] 16

@[expose] def T24s23 : PT 24 := PT.ofGens 24
  [#[4, 0, 22, 15, 6, 8, 17, 5, 1, 16, 3, 9, 19, 11, 20, 21, 10, 12, 13, 18, 2, 14, 7, 23]] 32

end CFSG.Quasithin.H.Mathieu
