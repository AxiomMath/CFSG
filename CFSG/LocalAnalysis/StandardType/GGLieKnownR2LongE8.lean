module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcDatum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcC2
public import CFSG.LieType.Steinberg.Adjoint.Perfect
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType.LieKnownR2.E8

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.HighestRoot CFSG.LieType.TitsSimplicity CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction
open scoped commutatorElement

private theorem l10se8e_ggLongRoot
    (K : Type) [Field K]
    {β : Fin (e8Datum K).rank → ℤ} (hβ : β ∈ (e8Datum K).roots) : GGLongRoot (e8Datum K) β := by
  have hsym : ∀ i j, (e8Datum K).cartan i j = (e8Datum K).cartan j i := cartanE_symm 8
  exact ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E8 hsym rfl hβ

theorem rootGroup_isPGroup_E8
    {n f : ℕ}
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) {Rr : Subgroup (ggU .E8 n f).K}
    (hRr : Rr = ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u) :
    IsPGroup 2 Rr := by
  subst hRr
  have h : IsPGroup 2 ((e8Datum (GaloisField 2 f)).rootGroup β) :=
    Exc.isPGroup_two_rootGroup_adj .E8 (GaloisField 2 f) hβ
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

theorem coreOne_E8
    {n f : ℕ}
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) {Rr Rm Q : Subgroup (ggU .E8 n f).K}
    (hRr : Rr = ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .E8 n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  exact coreOne_long_of
    (adjDatum_isCTGroupDatum (CFSG.LieType.Chevalley.rootOperatorFamily .E8) (GaloisField 2 f))
    (e8_steinbergExtras (GaloisField 2 f))
    rfl CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E8
    (fun γ hγ => Exc.isPGroup_two_rootGroup_adj .E8 (GaloisField 2 f) hγ)
    (Exc.isHighestRoot_adj .E8 (Or.inr (Or.inr rfl)) (GaloisField 2 f))
    (fun γ₀ hγ₀ hmax =>
      Exc.eq_highRoot_of_maxHeight_adj .E8 (Or.inr (Or.inr rfl)) (GaloisField 2 f) hγ₀ hmax)
    (l10se8e_ggLongRoot (GaloisField 2 f) hβ) u hRr hRm hQ

theorem coreFour_E8
    {n f : ℕ}
    {β : Fin (ggU .E8 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E8 n f).D.roots)
    (u : (ggU .E8 n f).K) {Rr Q : Subgroup (ggU .E8 n f).K}
    (hRr : Rr = ggRootSub (ggU .E8 n f).D (MonoidHom.id (ggU .E8 n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .E8 n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .E8 n f).K) := by
  exact coreFour_long_of
    (adjDatum_isCTGroupDatum (CFSG.LieType.Chevalley.rootOperatorFamily .E8) (GaloisField 2 f))
    (e8_steinbergExtras (GaloisField 2 f))
    (rootGroupCommutators_e8 (GaloisField 2 f))
    rfl
    (Exc.isHighestRoot_adj .E8 (Or.inr (Or.inr rfl)) (GaloisField 2 f))
    (fun γ₀ hγ₀ hmax =>
      Exc.eq_highRoot_of_maxHeight_adj .E8 (Or.inr (Or.inr rfl)) (GaloisField 2 f) hγ₀ hmax)
    (Exc.pCoreOf_normalizer_rootGroup_highRoot_adj .E8 (Or.inr (Or.inr rfl)) (GaloisField 2 f)).le
    (l10se8e_ggLongRoot (GaloisField 2 f) hβ) u hRr hQ

end CFSG.StandardType.LieKnownR2.E8
