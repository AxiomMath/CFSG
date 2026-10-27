module

public import CFSG.Quasithin.Recognition.SzVBOdd
public import CFSG.Quasithin.Recognition.F112WLocal

public section

namespace CFSG.Quasithin.SzVB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

structure GeoCtx (G₀ G₁ G₂ T V : Subgroup G) (z : G) : Prop where
  hyp : AmalgamHypV G₀ G₁ G₂ T V
  natS3 : F112W.IsNaturalS3 G₁ V
  inf_eq : G₁ ⊓ G₂ = T
  index3 : T.relIndex G₁ = 3
  klein : KleinData G₂ V z

structure EvenCtx (G₀ G₁ G₂ T V : Subgroup G) (z : G) : Prop extends GeoCtx G₀ G₁ G₂ T V z where
  bender : BenderLocalFacts G₂ T V

end CFSG.Quasithin.SzVB
