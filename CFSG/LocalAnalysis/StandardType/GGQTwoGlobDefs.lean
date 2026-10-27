module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveJoinPrimed
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRMModuleDefs

public section

namespace CFSG.StandardType.QTwo

noncomputable abbrev qTwoBarA
    {G : Type} [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) :
    Subgroup (V ≃ₗ[ZMod 3] V) :=
  (ggAInf 3 B Bs x L D J).map (ggLin (p := 3) ι)

noncomputable abbrev qTwoBarU
    {G : Type} [Group G] [Finite G] (B Bs L D J : Subgroup G) (x : G)
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) :
    Submodule (ZMod 3) V :=
  ggLinCom (qTwoBarA B Bs L D J x ι : Set (V ≃ₗ[ZMod 3] V))

@[expose] def qTwoPolar {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (Q : QuadraticForm (ZMod 3) U) : LinearMap.BilinForm (ZMod 3) U :=
  @QuadraticMap.polarBilin (ZMod 3) U (ZMod 3) _ _ _ _
    (inferInstance : Module (ZMod 3) (ZMod 3)) Q

end CFSG.StandardType.QTwo

end
