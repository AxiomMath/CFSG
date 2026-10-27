module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.Fitting.WholeGroupConstruction

public section

namespace CFSG.Open

@[expose] def genFittingFitting (G : Type*) [Group G] : Subgroup G :=
  CFSG.fittingSubgroup G

theorem genFittingFitting.eq_sSup (G : Type*) [Group G] :
    genFittingFitting G = sSup {N : Subgroup G | N.Normal ∧ Group.IsNilpotent N} :=
  rfl

attribute [eqns genFittingFitting.eq_sSup] genFittingFitting

@[expose] def genFittingLayer (G : Type*) [Group G] : Subgroup G :=
  CFSG.WholeGroup.layerOf fun L : Subgroup G => IsComponentOf L ⊤

theorem genFittingLayer.eq_sSup (G : Type*) [Group G] :
    genFittingLayer G = sSup {L : Subgroup G | IsComponentOf L ⊤} :=
  rfl

attribute [eqns genFittingLayer.eq_sSup] genFittingLayer

@[expose] def genFittingFStar (G : Type*) [Group G] : Subgroup G :=
  CFSG.WholeGroup.fstarOf (genFittingLayer G)

theorem genFittingFStar.eq_sup (G : Type*) [Group G] :
    genFittingFStar G = genFittingFitting G ⊔ genFittingLayer G :=
  rfl

attribute [eqns genFittingFStar.eq_sup] genFittingFStar

end CFSG.Open
