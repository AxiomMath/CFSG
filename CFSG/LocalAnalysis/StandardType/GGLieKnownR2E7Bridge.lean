module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionCore
public import CFSG.LocalAnalysis.SeitzReduction.E8PilotLevi
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.LieType.Chevalley.AdjointCenter
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

namespace CFSG.StandardType.LieKnownR2.E7

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.Blueprint.Chevalley

theorem map_e7MinEquivAdjoint_rootGroup
    {K : Type} [Field K] [Finite K] [CharP K 2]
    {β : Fin (Tag.rank .E7) → ℤ} (hβ : IsRoot .E7 β) :
    ((e7Datum K).rootGroup β).map (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom =
      (adjDatum (rootOperatorFamily .E7) K).rootGroup β := by
  have he : (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint K).toMonoidHom = e7Isogeny K :=
    MonoidHom.ext fun g => CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint_apply g
  rw [he]
  exact CFSG.ClassicalInvolution.ModelFacts.map_e7Isogeny_rootGroup (k := K) hβ

theorem rootGroup_isPGroup_E7
    {n f : ℕ} {β : Fin (ggU .E7 n f).D.rank → ℤ}
    (u : (ggU .E7 n f).K) {Rr : Subgroup (ggU .E7 n f).K}
    (hRr : Rr = ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u) :
    IsPGroup 2 Rr := by
  subst hRr
  have h : IsPGroup 2 ((e7Datum (GaloisField 2 f)).rootGroup β) :=
    isPGroup_two_range_of_charTwo (e7Data_valid.xHom (GaloisField 2 f) β)
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

theorem center_eq_bot_E7
    {n f : ℕ} : Subgroup.center (ggU .E7 n f).K = ⊥ := by
  have h := Subgroup.map_center_eq
    (CFSG.SeitzReduction.E8Pilot.e7MinEquivAdjoint (GaloisField 2 f)).symm
  rw [center_adjointGroup_eq_bot (τ := .E7) (K := GaloisField 2 f), Subgroup.map_bot] at h
  exact h.symm

end CFSG.StandardType.LieKnownR2.E7
