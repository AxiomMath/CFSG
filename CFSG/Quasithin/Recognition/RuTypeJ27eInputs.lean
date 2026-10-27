module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsCore
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic

public section

namespace CFSG.Quasithin.RuType

open CFSG.QuasithinUnique

@[expose] def cpow (c : List ℕ) : ℕ → List ℕ
  | 0 => A6Facts.Core.cid
  | n + 1 => A6Facts.Core.cmul (cpow c n) c

@[expose] def x5 : Equiv.Perm (Fin 10) := A6Models.tAdd * A6Models.tSq * A6Models.tInv

end CFSG.Quasithin.RuType
