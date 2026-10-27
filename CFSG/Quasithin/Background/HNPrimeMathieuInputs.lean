module

public import CFSG.Quasithin.H13.A5M22HatInputs

public section

namespace CFSG.Quasithin.H.MathieuLat

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat

@[expose] def permThreeOK (T : PT 24) (a : Array ℕ) : Bool :=
  pow24 a 3 == id24 && a != id24 &&
    (List.range T.n).all fun p =>
      T.elems.contains (comp24 a T.elems[p]!) ||
        T.elems.contains (comp24 (comp24 a T.elems[p]!) (invArr a)) ||
        T.elems.contains (comp24 (comp24 a T.elems[p]!) (pow24 (invArr a) 2))

@[expose] def y22 : Array ℕ :=
  #[0, 1, 9, 2, 17, 23, 5, 15, 8, 3, 10, 11, 14, 4, 20, 19, 18, 13, 22, 7, 12, 21, 16, 6]

@[expose] def y12 : Array ℕ :=
  #[23, 4, 20, 19, 15, 17, 14, 5, 12, 2, 22, 10, 13, 8, 21, 1, 3, 7, 0, 16, 9, 6, 11, 18]

end CFSG.Quasithin.H.MathieuLat
