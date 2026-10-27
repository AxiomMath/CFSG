module

public import CFSG.Quasithin.Background.HMathieuCent
public import CFSG.Monster.B.TwoA.Base.M22
public import CFSG.Monster.CodeAut.Bridge
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.M24
public meta import CFSG.Quasithin.Background.HMathieuCent
public meta import CFSG.Monster.Code.Basis
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.Blueprint

@[expose] def m23AArr : Array ℕ :=
  #[0, 2, 1, 4, 3, 5, 6, 7, 8, 21, 18, 15, 12, 17, 22, 11, 16, 13, 10, 23, 20, 9, 14, 19]

@[expose] def m23BArr : Array ℕ :=
  #[0, 17, 10, 1, 5, 22, 3, 13, 19, 20, 23, 11, 2, 7, 14, 21, 4, 6, 18, 9, 8, 15, 16, 12]

end CFSG.Quasithin.H.Mathieu
