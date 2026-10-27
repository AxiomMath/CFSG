module

public import Certificates.Data.Kernel.B45Ind.Defs
public import Certificates.Data.SmithB45MatIndM23

public section

namespace CFSG.KC.B45Ind

open CFSG.Quasithin.B45Mat.Ind CFSG.Quasithin.H.Mathieu

@[expose] def ts23L : List (List ℕ) :=
  (m23CosC.map decW).map (wordL m23AArr.toList m23BArr.toList)

@[expose] def gen23L (z : Bool) : List ℕ :=
  if z then m23BArr.toList else m23AArr.toList

@[expose] def k23L (i : ℕ) (z : Bool) : List ℕ :=
  indColsL (m23Xd i) (m23Xc i) ts23L (gen23L z) 1

@[expose] def coset23L : Bool :=
  cosetOKL m23AArr.toList m23BArr.toList ts23L 23 1

@[expose] def flag23L (i : ℕ) : Bool :=
  flagCore (23 * m23Xd i) (k23L i) (m23P i) (invColsL (23 * m23Xd i) (m23P i)) (m23Ns i)
    fun j => m23Std ((m23Typs i).getD j 0)

end CFSG.KC.B45Ind
