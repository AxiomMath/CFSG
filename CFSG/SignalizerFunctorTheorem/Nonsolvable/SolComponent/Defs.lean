module

public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.Radical

public section

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

@[expose] def IsSolComponent (K : Subgroup G) : Prop :=
  Group.IsPerfect K ∧ K.IsSubnormal ∧
    CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.solvableRadical G)))

variable (G) in
@[expose] def solLayer : Subgroup G :=
  sSup {K : Subgroup G | IsSolComponent K}

variable (G) in
@[expose] def oStar : Subgroup G :=
  CFSG.solvableRadical G ⊔ solLayer G

namespace IsSolComponent

variable {K : Subgroup G}

theorem isPerfect (h : IsSolComponent K) : Group.IsPerfect K :=
  h.1

theorem isSubnormal (h : IsSolComponent K) : K.IsSubnormal :=
  h.2.1

theorem isComponent_map (h : IsSolComponent K) :
    CFSG.IsComponent (K.map (QuotientGroup.mk' (CFSG.solvableRadical G))) :=
  h.2.2

end IsSolComponent

theorem le_solLayer {K : Subgroup G} (hK : IsSolComponent K) : K ≤ solLayer G :=
  le_sSup hK

theorem solvableRadical_le_oStar : CFSG.solvableRadical G ≤ oStar G :=
  le_sup_left

theorem solLayer_le_oStar : solLayer G ≤ oStar G :=
  le_sup_right

theorem le_oStar {K : Subgroup G} (hK : IsSolComponent K) : K ≤ oStar G :=
  (le_solLayer hK).trans solLayer_le_oStar

end CFSG.SignalizerFunctorTheorem.Nonsolvable
