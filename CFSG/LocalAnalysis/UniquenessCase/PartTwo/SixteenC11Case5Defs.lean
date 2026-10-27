module

public import CFSG.Quasithin.Background.HOm4Norm

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin.H.Om4

@[expose] noncomputable def s16c11C5Scal (K : Type) [Field K] : Subgroup (MulAut (VM K)) :=
  Subgroup.closure {x | ∃ c : Kˣ,
    x = lr (Units.map (Matrix.scalar (Fin 2) (α := K)).toMonoidHom c) 1}

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
