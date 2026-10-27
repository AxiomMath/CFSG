module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.A3ComponentsBasic
public import CFSG.Quasithin.Background.B6Defs

public section

namespace CFSG.Quasithin.H13

open CFSG.Open

variable {G : Type} [Group G]

@[expose] def ch82I (V : Subgroup G) (h : G) : Subgroup G := V ⊔ B6.conjSub h V

@[expose] def ch82A (V : Subgroup G) (h : G) : Subgroup G :=
  B6.conjSub h V ⊓ pCoreOf 2 (ch82I V h)

@[expose] def ch82B (V : Subgroup G) (h : G) : Subgroup G := V ⊓ pCoreOf 2 (ch82I V h)

@[expose] def ch82ZI (V : Subgroup G) (h : G) : Subgroup G := V ⊓ B6.conjSub h V

@[expose] def ch82U (V : Subgroup G) (h : G) : Subgroup G :=
  V ⊓ Subgroup.centralizer (ch82A V h : Set G)

@[expose] def ch82LU (L U : Subgroup G) : Subgroup G :=
  perfectCore (L ⊓ Subgroup.normalizer (U : Set G))

end CFSG.Quasithin.H13
