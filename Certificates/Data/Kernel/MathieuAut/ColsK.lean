module

public import Certificates.Data.Kernel.MathieuAut.InAutK
public import CFSG.Quasithin.Background.HMathieuCodeMask

public section

namespace CFSG.KS.MathieuAut

open CFSG.Quasithin.H.Mathieu

@[expose] def colsOf (κ lift l : List ℕ) : List ℕ :=
  lift.map fun c => actM κ (actM (l.map (2 ^ ·)) c)

@[expose] def cols10 (l : List ℕ) : List ℕ := colsOf cc10Cols lift10Cols l

@[expose] def cols11 (l : List ℕ) : List ℕ := colsOf ccECols liftECols l

@[expose] def colsC10 (l : List ℕ) : List ℕ := colsOf κC22Cols lift22Cols l

@[expose] def colsC11 (l : List ℕ) : List ℕ := colsOf κCCols liftCCols l

@[expose] def fixAll (Ms : List (List ℕ)) (N : ℕ) (rel : ℕ → ℕ → Bool) (ok : ℕ → Bool) : Bool :=
  (List.range N).all fun m => !(Ms.all fun M => rel (actM M m) m) || ok m

@[expose] def spanAll (N : ℕ) (l : List ℕ) : Bool := orMask (combos l) == 2 ^ N - 1

@[expose] def transOK (S : List ℕ) : Bool :=
  S.all fun s => (s ^^^ S.headD 0) == 0 ||
    S.any fun t => !((orMask S).testBit (t ^^^ (s ^^^ S.headD 0)))

end CFSG.KS.MathieuAut

end
