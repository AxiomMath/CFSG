module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.B2FactorizationBridge
public import CFSG.Quasithin.Background.D2Fitting
public import CFSG.Quasithin.EmptyFaithful.Vocabulary
public import CFSG.Quasithin.QTFE14Cat

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

section Aut

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def ExcShape (X A : Subgroup (MulAut V)) : Prop :=
  rk A = 2 ∧ rAV A = 2 ∧
    rk (commV (fittingOf (Jhat X))) = rk ↥(commV (fittingOf (Jhat X)) ⊓ fixV A) + 3 ∧
    rk (fixV (fittingOf (Jhat X))) = rk ↥(fixV (fittingOf (Jhat X)) ⊓ fixV A) + 1

end Aut

@[expose] def Row24Residual : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), quasithinQTFE14Cat G T Mc →
    IsMf T Mc M → ∀ hVe : IsElemAbelian 2 (VZ T M),
      ∀ A ∈ QhatStar (autI hVe M), ¬ ExcShape (autI hVe M) A

end CFSG.Quasithin
