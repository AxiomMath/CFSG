
module

public import CFSG.Sporadic.ON.SetupBase
public import CFSG.Sporadic.ON.VecSpec

@[expose] public section

namespace CFSG.Sporadic.ON

open Native Matrix
open CFSG.F3.Native CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
open CFSG.Perm.Native

abbrev Vec : Type := Fin 154 → ZMod 3

noncomputable abbrev P (i : ℕ) : Vec := vecOf orb.keys[i]!

noncomputable abbrev ptSet : Set Vec := P '' Set.Iio nPts

noncomputable abbrev Umat : Matrix (Fin 154) (Fin 154) (ZMod 3) := toMat 154 (toVM basisR)

noncomputable abbrev Xmat : Matrix (Fin 154) (Fin 154) (ZMod 3) := toMat 154 (toVM basisX)

end CFSG.Sporadic.ON
