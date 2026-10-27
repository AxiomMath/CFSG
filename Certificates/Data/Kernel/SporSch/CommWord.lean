module

public import Mathlib.Data.Int.Basic

public section

namespace CFSG.KS.SporSch.CommWord

@[expose] def invW (w : List ℤ) : List ℤ := (w.map Neg.neg).reverse

@[expose] def cpWord : List (List ℤ × List ℤ) → List ℤ
  | [] => []
  | p :: r => p.1 ++ (p.2 ++ (invW p.1 ++ (invW p.2 ++ cpWord r)))

end CFSG.KS.SporSch.CommWord

end
