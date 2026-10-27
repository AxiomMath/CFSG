module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2E7Bridge
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcDatum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcC2
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple

public section

namespace CFSG.StandardType.LieKnownR2.E7

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.HighestRoot CFSG.LieType.TitsSimplicity
  CFSG.Blueprint.Chevalley CFSG.SeitzReduction CFSG.LieType.Chevalley
open scoped commutatorElement

private theorem l10se7c_mem_roots
    {K : Type} [Field K] {γ : Fin (Tag.rank .E7) → ℤ} :
    γ ∈ (e7Datum K).roots ↔ IsRoot .E7 γ := by
  rw [MinData.Valid.minDatum_roots]
  rfl

private theorem l10se7c_eq_highRoot
    {K : Type} [Field K] {γ₀ : Fin (e7Datum K).rank → ℤ} (hγ₀ : γ₀ ∈ (e7Datum K).roots)
    (hmax : ∀ δ ∈ (e7Datum K).roots, ht δ ≤ ht γ₀) : γ₀ = highRoot .E7 :=
  Exc.eq_highRoot_of_maxHeight_adj .E7 (Or.inr (Or.inl rfl)) K
    (mem_adjDatum_roots.2 (l10se7c_mem_roots.1 hγ₀))
    (fun δ hδ => hmax δ (l10se7c_mem_roots.2 (mem_adjDatum_roots.1 hδ)))

private theorem l10se7c_isHighestRoot
    (K : Type) [Field K] : IsHighestRoot (e7Datum K) (highRoot .E7) := by
  have hrank : 0 < (e7Datum K).rank := by
    have h : (e7Datum K).rank = 7 := rfl
    omega
  obtain ⟨r, hr⟩ :=
    exists_isHighestRoot (e7Datum K) CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7 rfl hrank
  have hEq : r = highRoot .E7 := l10se7c_eq_highRoot hr.mem_roots hr.height_le
  rwa [hEq] at hr

private theorem l10se7c_map_highestRootRadical
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    (highestRootRadical (e7Datum K) (highRoot .E7)).map
        (E8Pilot.e7MinEquivAdjoint K).toMonoidHom =
      highestRootRadical (adjDatum (rootOperatorFamily .E7) K) (highRoot .E7) := by
  simp only [highestRootRadical, Subgroup.map_iSup]
  refine iSup_congr fun γ => ?_
  have hiff : γ ∈ {γ | γ ∈ (e7Datum K).roots ∧ 0 < rootForm (e7Datum K) γ (highRoot .E7)} ↔
      γ ∈ {γ | γ ∈ (adjDatum (rootOperatorFamily .E7) K).roots ∧
        0 < rootForm (adjDatum (rootOperatorFamily .E7) K) γ (highRoot .E7)} := by
    simp only [Set.mem_setOf_eq]
  exact iSup_congr_Prop hiff fun h =>
    map_e7MinEquivAdjoint_rootGroup (K := K) ((l10se7c_mem_roots (K := K)).1 h.1)

private theorem l10se7c_C2
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    pCoreOf 2 (Subgroup.normalizer (((e7Datum K).rootGroup (highRoot .E7) :
        Subgroup ↥(e7Data_valid.minGroup K)) : Set ↥(e7Data_valid.minGroup K))) =
      highestRootRadical (e7Datum K) (highRoot .E7) := by
  apply Subgroup.map_injective (f := (E8Pilot.e7MinEquivAdjoint K).toMonoidHom)
    (E8Pilot.e7MinEquivAdjoint K).injective
  rw [← GGRootNorm.pCoreOf_map_mulEquiv, ← GGRootNorm.normalizer_map_mulEquiv,
    map_e7MinEquivAdjoint_rootGroup (isRoot_highRoot .E7),
    Exc.pCoreOf_normalizer_rootGroup_highRoot_adj .E7 (Or.inr (Or.inl rfl)) K,
    l10se7c_map_highestRootRadical]

theorem coreOne_E7
    {n f : ℕ}
    {β : Fin (ggU .E7 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E7 n f).D.roots)
    (u : (ggU .E7 n f).K) {Rr Rm Q : Subgroup (ggU .E7 n f).K}
    (hRr : Rr = ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .E7 n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  have hsym : ∀ i j, (e7Datum (GaloisField 2 f)).cartan i j =
      (e7Datum (GaloisField 2 f)).cartan j i := cartanE_symm 7
  exact coreOne_long_of
    (e7Datum_isCTGroupDatum (GaloisField 2 f))
    (e7Datum_steinbergExtras (GaloisField 2 f))
    rfl CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7
    (fun γ _ => isPGroup_two_range_of_charTwo (e7Data_valid.xHom (GaloisField 2 f) γ))
    (l10se7c_isHighestRoot (GaloisField 2 f))
    (fun γ₀ hγ₀ hmax => l10se7c_eq_highRoot hγ₀ hmax)
    (ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7 hsym rfl hβ)
    u hRr hRm hQ

theorem coreFour_E7
    {n f : ℕ}
    {β : Fin (ggU .E7 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E7 n f).D.roots)
    (u : (ggU .E7 n f).K) {Rr Q : Subgroup (ggU .E7 n f).K}
    (hRr : Rr = ggRootSub (ggU .E7 n f).D (MonoidHom.id (ggU .E7 n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .E7 n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .E7 n f).K) := by
  have hsym : ∀ i j, (e7Datum (GaloisField 2 f)).cartan i j =
      (e7Datum (GaloisField 2 f)).cartan j i := cartanE_symm 7
  exact coreFour_long_of
    (e7Datum_isCTGroupDatum (GaloisField 2 f))
    (e7Datum_steinbergExtras (GaloisField 2 f))
    (rootGroupCommutators_e7 (GaloisField 2 f))
    rfl
    (l10se7c_isHighestRoot (GaloisField 2 f))
    (fun γ₀ hγ₀ hmax => l10se7c_eq_highRoot hγ₀ hmax)
    (l10se7c_C2 (K := GaloisField 2 f)).le
    (ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E7 hsym rfl hβ)
    u hRr hQ

end CFSG.StandardType.LieKnownR2.E7
