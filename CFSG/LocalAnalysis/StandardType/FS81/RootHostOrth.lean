module

public import CFSG.LocalAnalysis.StandardType.FS81.Defs
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteFSInputs
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneMarking
public import CFSG.LocalAnalysis.StandardType.FS81.RowElemAbOrth
public import CFSG.LocalAnalysis.StandardType.FS81.OrthInner
public import CFSG.LocalAnalysis.StandardType.FS81.LocalOrthModels
public import CFSG.GroupTheory.ConjTransport

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly

theorem isRow_D6_map_conj {G : Type} [Group G] {K : Subgroup G} (hK : IsRow Row.D6 K)
    (g : G) : IsRow Row.D6 (K.map (MulAut.conj g).toMonoidHom) := by
  let e := Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  exact CFSG.StandardType.largeEvenMarking_of_mulEquiv e.symm hK

theorem center_map_conj_eq_bot {G : Type} [Group G] {K : Subgroup G}
    (hZ : Subgroup.center K = ⊥) (g : G) :
    Subgroup.center (K.map (MulAut.conj g).toMonoidHom) = ⊥ := by
  let e := Subgroup.equivMapOfInjective K (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective
  exact CFSG.StandardType.center_eq_bot_of_mulEquiv e.symm hZ

end CFSG.StandardType.FrameRoute.FS81

end
