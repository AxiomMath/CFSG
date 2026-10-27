module

public import CFSG.Quasithin.Background.HMathieuCentInputs

public section

namespace CFSG.KS.MathieuAut

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

@[expose] def orMask : List ℕ → ℕ
  | [] => 0
  | x :: xs => 2 ^ x ||| orMask xs

@[expose] def autFwd (cs : List ℕ) : Bool :=
  (List.range 12).all fun i => syndM (actM cs (Bmask i)) == 0

@[expose] def inAutKL (l : List ℕ) : Bool :=
  l.length == 24 && l.all (· < 24) && orMask l == 2 ^ 24 - 1 && autFwd (l.map (2 ^ ·))

@[expose] def inAutK (a : Array ℕ) : Bool :=
  if a.size = 24 then inAutKL a.toList else inAutOK a

end CFSG.KS.MathieuAut

end
