module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4Datum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongF4C2
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs

public section

namespace CFSG.StandardType.LieKnownR2.Short

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.HighestRoot CFSG.LieType.TitsSimplicity CFSG.Blueprint.Chevalley
  CFSG.SeitzReduction
open scoped commutatorElement

open CFSG.ClassicalInvolution.ModelFacts in
private theorem longF4_isIrreducible_cartan : IsIrreducible (Tag.cartan .F4) :=
  @isIrreducible_of_parent (Fin 4) _ (Tag.cartan .F4) (0 : Fin 4) ![0, 0, 1, 2] ![0, 1, 2, 3]
    (by decide)

theorem rootGroup_isPGroup_F4
    {n f : ℕ}
    {β : Fin (ggU .F4 n f).D.rank → ℤ} (hβ : β ∈ (ggU .F4 n f).D.roots)
    (u : (ggU .F4 n f).K) {Rr : Subgroup (ggU .F4 n f).K}
    (hRr : Rr = ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u) :
    IsPGroup 2 Rr := by
  subst hRr
  have h : IsPGroup 2 ((f4Datum (GaloisField 2 f)).rootGroup β) :=
    isPGroup_two_rootGroup_F4 (GaloisField 2 f) hβ
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

theorem coreOne_F4_long
    {n f : ℕ}
    {β : Fin (ggU .F4 n f).D.rank → ℤ}
    (hl : GGLongRoot (ggU .F4 n f).D β)
    (u : (ggU .F4 n f).K) {Rr Rm Q : Subgroup (ggU .F4 n f).K}
    (hRr : Rr = ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .F4 n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  exact coreOne_long_of
    (f4_isCTGroupDatum_exact (GaloisField 2 f))
    (f4_steinbergExtras_exact (GaloisField 2 f))
    rfl longF4_isIrreducible_cartan
    (fun γ hγ => isPGroup_two_rootGroup_F4 (GaloisField 2 f) hγ)
    (isHighestRoot_F4 (GaloisField 2 f))
    (fun γ₀ hγ₀ hmax => eq_highRoot_of_maxHeight_F4 (GaloisField 2 f) hγ₀ hmax)
    hl u hRr hRm hQ

theorem coreFour_F4_long
    {n f : ℕ}
    {β : Fin (ggU .F4 n f).D.rank → ℤ}
    (hl : GGLongRoot (ggU .F4 n f).D β)
    (u : (ggU .F4 n f).K) {Rr Q : Subgroup (ggU .F4 n f).K}
    (hRr : Rr = ggRootSub (ggU .F4 n f).D (MonoidHom.id (ggU .F4 n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .F4 n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .F4 n f).K) := by
  exact coreFour_long_of
    (f4_isCTGroupDatum_exact (GaloisField 2 f))
    (f4_steinbergExtras_exact (GaloisField 2 f))
    (f4_rootGroupCommutators_exact (GaloisField 2 f))
    rfl
    (isHighestRoot_F4 (GaloisField 2 f))
    (fun γ₀ hγ₀ hmax => eq_highRoot_of_maxHeight_F4 (GaloisField 2 f) hγ₀ hmax)
    (pCoreOf_normalizer_rootGroup_highRoot_F4 (GaloisField 2 f)).le
    hl u hRr hQ

end CFSG.StandardType.LieKnownR2.Short
