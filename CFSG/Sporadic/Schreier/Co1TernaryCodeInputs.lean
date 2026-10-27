module

public import CFSG.Sporadic.Schreier.Co1EigenModules
public meta import CFSG.Sporadic.Schreier.Co1ElemData
public meta import CFSG.Sporadic.Schreier.Co1ElemThreeData

public section

namespace CFSG.Sporadic.Co1Schreier

open ElemThree Matrix

@[expose] def tsupp (v : Fin 12 → ZMod 3) : Finset (Fin 12) := Finset.univ.filter fun j => v j ≠ 0

@[expose] def weightCount (n : ℕ) : ℕ :=
  if n = 0 then 1 else if n = 6 then 264 else if n = 9 then 440 else if n = 12 then 24 else 0

@[expose] def sixSupports : Finset (Finset (Fin 12)) :=
  (Finset.univ.filter fun b : Fin 6 → ZMod 3 => (tsupp (b ᵥ* R)).card = 6).image
    fun b => tsupp (b ᵥ* R)

end CFSG.Sporadic.Co1Schreier
