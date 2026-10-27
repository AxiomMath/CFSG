module

public import CFSG.LocalAnalysis.StandardType.GGSecFivePresOfPsiFacts
public import CFSG.LocalAnalysis.StandardType.GGPresentationWeyl
public import CFSG.LieType.HighestRoot.GenBasic

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}

theorem ggHasWeylLift_of_ctGroupDatum
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hsq : ∀ i, n i * n i = 1) : GGHasWeylLift D :=
  ⟨ggWeylLiftOf hct hsq, ggWeylLiftOf_spec hct hsq⟩

theorem ggRootGroupsRigid_of_steinberg
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) : GGRootGroupsRigid D :=
  fun _ hγ _ h => CFSG.LieType.HighestRoot.weylAction_eq_of_rootGroup_eq hct hext hγ h

end CFSG.StandardType

end
