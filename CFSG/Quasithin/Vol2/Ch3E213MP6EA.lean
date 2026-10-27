module

public import CFSG.Quasithin.Vol2.Ch3E213MDefs

public section

namespace CFSG.Quasithin.Ch3E213M

open CFSG.Open CFSG.QuasithinUnique B6

@[expose] def PkgSp4One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (H T M V K : Subgroup G), Setting H T M V K →
    Case2 H T M K → E2.IsSp4Prime 1 ↥(E2.star M H K) →
    E2.IsDiagramNontrivial (E2.star M H T) (E2.star M H K) (E2.star M H (T ⊓ K)) →
    E2.IsBorelIn (E2.star M H K) (E2.star M H (M ⊓ K)) → E213Concl H T M V

end CFSG.Quasithin.Ch3E213M
