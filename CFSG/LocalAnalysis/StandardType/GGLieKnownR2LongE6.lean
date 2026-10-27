module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2CoverLift
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcDatum
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2LongExcC2
public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2HighestRootLong
public import CFSG.LocalAnalysis.StandardType.GGRootInvolutionExceptional
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.CurtisTits.ExceptionalQuasisimple
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalIsogeny
public import CFSG.ClassicalInvolution.ModelFacts.ChevAutLift
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint
public import CFSG.LocalAnalysis.ComponentClassification.BadTwoComponentSubgroup

public section

namespace CFSG.StandardType.LieKnownR2.E6

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny CFSG.LieType.HighestRoot
  CFSG.LieType.TitsSimplicity CFSG.Blueprint.Chevalley CFSG.SeitzReduction CFSG.LieType.Chevalley
open scoped commutatorElement

private theorem l10se6c_mem_roots
    {K : Type} [Field K] {γ : Fin (Tag.rank .E6) → ℤ} :
    γ ∈ (e6Datum K).roots ↔ IsRoot .E6 γ := by
  rw [MinData.Valid.minDatum_roots]
  rfl

private theorem l10se6c_eq_highRoot
    {K : Type} [Field K] {γ₀ : Fin (e6Datum K).rank → ℤ} (hγ₀ : γ₀ ∈ (e6Datum K).roots)
    (hmax : ∀ δ ∈ (e6Datum K).roots, ht δ ≤ ht γ₀) : γ₀ = highRoot .E6 :=
  Exc.eq_highRoot_of_maxHeight_adj .E6 (Or.inl rfl) K
    (mem_adjDatum_roots.2 (l10se6c_mem_roots.1 hγ₀))
    (fun δ hδ => hmax δ (l10se6c_mem_roots.2 (mem_adjDatum_roots.1 hδ)))

private theorem l10se6c_isHighestRoot
    (K : Type) [Field K] : IsHighestRoot (e6Datum K) (highRoot .E6) := by
  have hrank : 0 < (e6Datum K).rank := by
    have h : (e6Datum K).rank = 6 := rfl
    omega
  obtain ⟨r, hr⟩ :=
    exists_isHighestRoot (e6Datum K) CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6 rfl hrank
  have hEq : r = highRoot .E6 := l10se6c_eq_highRoot hr.mem_roots hr.height_le
  rwa [hEq] at hr

private theorem l10se6c_map_highestRootRadical
    {K : Type} [Field K] [Finite K] :
    (highestRootRadical (e6Datum K) (highRoot .E6)).map (e6Isogeny K) =
      highestRootRadical (adjDatum (rootOperatorFamily .E6) K) (highRoot .E6) := by
  simp only [highestRootRadical, Subgroup.map_iSup]
  refine iSup_congr fun γ => ?_
  have hiff : γ ∈ {γ | γ ∈ (e6Datum K).roots ∧ 0 < rootForm (e6Datum K) γ (highRoot .E6)} ↔
      γ ∈ {γ | γ ∈ (adjDatum (rootOperatorFamily .E6) K).roots ∧
        0 < rootForm (adjDatum (rootOperatorFamily .E6) K) γ (highRoot .E6)} := by
    simp only [Set.mem_setOf_eq]
  exact iSup_congr_Prop hiff fun h =>
    CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := K)
      ((l10se6c_mem_roots (K := K)).1 h.1)

private theorem l10se6c_C2
    {K : Type} [Field K] [Finite K] [CharP K 2] :
    pCoreOf 2 (Subgroup.normalizer (((e6Datum K).rootGroup (highRoot .E6) :
        Subgroup ↥(e6Data_valid.minGroup K)) : Set ↥(e6Data_valid.minGroup K))) ≤
      highestRootRadical (e6Datum K) (highRoot .E6) := by
  haveI : Finite ↥(e6Data_valid.minGroup K) :=
    CFSG.ClassicalInvolution.ModelFacts.ChevAut.finite_minGroup e6Data_valid K
  have hθ : IsRoot .E6 (highRoot .E6) := isRoot_highRoot .E6
  have hodd : Odd (Nat.card (e6Isogeny K).ker) := by
    have h := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_not_dvd_card_ker (p := 2) K
    exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h)
  have hX : ∀ γ ∈ (e6Datum K).roots, IsPGroup 2 ((e6Datum K).rootGroup γ) :=
    fun γ _ => isPGroup_two_range_of_charTwo (e6Data_valid.xHom K γ)
  have hQ : IsPGroup 2 (highestRootRadical (e6Datum K) (highRoot .E6)) :=
    isPGroup_highestRootRadical (e6Datum_steinbergExtras K) hX
      (l10se6c_isHighestRoot K).dominant
  refine Cover.pCoreOf_normalizer_le_of_map_surjective (e6Isogeny K) (e6Isogeny_surjective K)
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center K) hodd
    (hX _ ((l10se6c_mem_roots (K := K)).2 hθ)) hQ ?_
  rw [l10se6c_map_highestRootRadical,
    CFSG.ClassicalInvolution.ModelFacts.map_e6Isogeny_rootGroup (k := K) hθ]
  exact (Exc.pCoreOf_normalizer_rootGroup_highRoot_adj .E6 (Or.inl rfl) K).le

theorem rootGroup_isPGroup_E6
    {n f : ℕ} {β : Fin (ggU .E6 n f).D.rank → ℤ}
    (u : (ggU .E6 n f).K) {Rr : Subgroup (ggU .E6 n f).K}
    (hRr : Rr = ggRootSub (ggU .E6 n f).D (MonoidHom.id (ggU .E6 n f).K) β u) :
    IsPGroup 2 Rr := by
  subst hRr
  have h : IsPGroup 2 ((e6Datum (GaloisField 2 f)).rootGroup β) :=
    isPGroup_two_range_of_charTwo (e6Data_valid.xHom (GaloisField 2 f) β)
  exact (h.map (MulAut.conj u).toMonoidHom).map (MonoidHom.id _)

theorem coreOne_E6
    {n f : ℕ}
    {β : Fin (ggU .E6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E6 n f).D.roots)
    (u : (ggU .E6 n f).K) {Rr Rm Q : Subgroup (ggU .E6 n f).K}
    (hRr : Rr = ggRootSub (ggU .E6 n f).D (MonoidHom.id (ggU .E6 n f).K) β u)
    (hRm : Rm = ggRootSub (ggU .E6 n f).D (MonoidHom.id (ggU .E6 n f).K) (-β) u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .E6 n f).K))) :
    Q ⊔ (Rr ⊔ Rm) = ⊤ := by
  have hsym : ∀ i j, (e6Datum (GaloisField 2 f)).cartan i j =
      (e6Datum (GaloisField 2 f)).cartan j i := cartanE_symm 6
  exact coreOne_long_of
    (e6Datum_isCTGroupDatum (GaloisField 2 f))
    (e6Datum_steinbergExtras (GaloisField 2 f))
    rfl CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6
    (fun γ _ => isPGroup_two_range_of_charTwo (e6Data_valid.xHom (GaloisField 2 f) γ))
    (l10se6c_isHighestRoot (GaloisField 2 f))
    (fun γ₀ hγ₀ hmax => l10se6c_eq_highRoot hγ₀ hmax)
    (ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6 hsym rfl hβ)
    u hRr hRm hQ

theorem coreFour_E6
    {n f : ℕ}
    {β : Fin (ggU .E6 n f).D.rank → ℤ} (hβ : β ∈ (ggU .E6 n f).D.roots)
    (u : (ggU .E6 n f).K) {Rr Q : Subgroup (ggU .E6 n f).K}
    (hRr : Rr = ggRootSub (ggU .E6 n f).D (MonoidHom.id (ggU .E6 n f).K) β u)
    (hQ : Q = pCoreOf 2 (Subgroup.normalizer (Rr : Set (ggU .E6 n f).K))) :
    ⁅Q, Q⁆ ≤ Rr ∧ Q ≤ Subgroup.centralizer (Rr : Set (ggU .E6 n f).K) := by
  have hsym : ∀ i j, (e6Datum (GaloisField 2 f)).cartan i j =
      (e6Datum (GaloisField 2 f)).cartan j i := cartanE_symm 6
  exact coreFour_long_of
    (e6Datum_isCTGroupDatum (GaloisField 2 f))
    (e6Datum_steinbergExtras (GaloisField 2 f))
    (rootGroupCommutators_e6 (GaloisField 2 f))
    rfl
    (l10se6c_isHighestRoot (GaloisField 2 f))
    (fun γ₀ hγ₀ hmax => l10se6c_eq_highRoot hγ₀ hmax)
    (l10se6c_C2 (K := GaloisField 2 f))
    (ggLongRoot_of_symmetric CFSG.ClassicalInvolution.ModelFacts.isIrreducible_E6 hsym rfl hβ)
    u hRr hQ

end CFSG.StandardType.LieKnownR2.E6
