module

public import CFSG.LocalAnalysis.StandardType.GGExcKGSFDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

section Universal

private theorem finite_adjointGroup_of_finite (τ : CFSG.Blueprint.Chevalley.Tag) (K : Type*)
    [Field K] [Finite K] : Finite (CFSG.Blueprint.Chevalley.adjointGroup τ K) := by
  have : Finite (Module.End K (CFSG.Blueprint.Chevalley.RootModule τ K)) :=
    Module.finite_of_finite K
  infer_instance

private theorem finite_minGroup_of_finite {τ : CFSG.Blueprint.Chevalley.Tag}
    {D : CFSG.LieType.Steinberg.Minuscule.MinData τ} (hV : D.Valid) (K : Type*) [Field K]
    [Finite K] : Finite ↥(hV.minGroup K) := by
  have : Finite (Module.End K (Fin D.d →₀ K)) := Module.finite_of_finite K
  infer_instance

theorem ggU_finite_exc {t : StatedLieTag} (ht : GGExcFive t) {n f : ℕ}
    (hadm : GGKnownAdm t n f) : Finite (ggU t n f).K := by
  rcases ht with rfl | rfl | rfl | rfl | rfl
  · change Finite (CFSG.Blueprint.Chevalley.adjointGroup .F4 (GaloisField 2 f))
    exact finite_adjointGroup_of_finite _ _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.e6UniversalGroup 2 f)
    exact finite_minGroup_of_finite (D := CFSG.LieType.Steinberg.Minuscule.e6Data)
      CFSG.LieType.Steinberg.Minuscule.e6Data_valid _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.e7UniversalGroup 2 f)
    exact finite_minGroup_of_finite (D := CFSG.LieType.Steinberg.Minuscule.e7Data)
      CFSG.LieType.Steinberg.Minuscule.e7Data_valid _
  · change Finite (CFSG.Blueprint.Chevalley.adjointGroup .E8 (GaloisField 2 f))
    exact finite_adjointGroup_of_finite _ _
  · change Finite (CFSG.LieType.Steinberg.Exceptional.twistedE6Group 2 f)
    have hfin : Finite ↥(CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup
        (GaloisField 2 (2 * f))) :=
      finite_minGroup_of_finite (D := CFSG.LieType.Steinberg.Minuscule.e6Data)
        CFSG.LieType.Steinberg.Minuscule.e6Data_valid _
    infer_instance

end Universal

end CFSG.StandardType
