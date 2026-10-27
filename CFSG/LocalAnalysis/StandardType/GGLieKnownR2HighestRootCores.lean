module

public import CFSG.LocalAnalysis.StandardType.GGLieKnownR2Radical
public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LocalAnalysis.StandardType.GGRootNormInner
public import CFSG.LieType.HighestRoot.Gen

public section

namespace CFSG.StandardType.LieKnownR2

open CFSG.Open CFSG.StandardType CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits CFSG.LieType.Steinberg CFSG.LieType.HighestRoot
  CFSG.LieType.TitsSimplicity CFSG.ClassicalInvolution.ModelFacts
open scoped commutatorElement

theorem map_pCoreOf_normalizer_mulEquiv {G G' : Type} [Group G] [Group G'] (e : G ≃* G')
    (S : Subgroup G) :
    (pCoreOf 2 (Subgroup.normalizer (S : Set G))).map e.toMonoidHom =
      pCoreOf 2 (Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup G') : Set G')) := by
  rw [GGRootNorm.normalizer_map_mulEquiv e S]
  exact (GGRootNorm.pCoreOf_map_mulEquiv e (Subgroup.normalizer (S : Set G))).symm

theorem coreOne_highest_of
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
      (weylAction D.isFiniteType) D.roots D.rootGroup n H)
    (hext : SteinbergExtras D n H) (hdiv : D.divisible = ∅) (hirr : IsIrreducible D.cartan)
    (hX : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ))
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r) :
    pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) ⊔
      (D.rootGroup r ⊔ D.rootGroup (-r)) = ⊤ := by
  obtain ⟨-, hQp, hQN, hNQ, hsup⟩ :=
    highestRootGen_of_isHighestRoot hct hext (divisibleNormalizes_of_divisible_eq_empty hdiv)
      (divisibleWeylMem_of_divisible_eq_empty hdiv) hirr hX hr
  have hQle : highestRootRadical D r ≤
      pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) :=
    GGRootNorm.le_pCoreOf_of_normalized hQN hQp (Subgroup.le_normalizer_iff.mp hNQ)
  have htop : (⊤ : Subgroup K) ≤
      pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) ⊔ rankOneGroup D r := by
    rw [← hsup]
    exact sup_le_sup_right hQle _
  exact top_le_iff.mp htop

theorem coreFour_highest_of
    {K : Type} [Group K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
    {H : Fin D.rank → Subgroup K}
    (hext : SteinbergExtras D n H) (hcomm : RootGroupCommutators D) (hdiv : D.divisible = ∅)
    {r : Fin D.rank → ℤ} (hr : IsHighestRoot D r)
    (hC2 : pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) ≤ highestRootRadical D r) :
    ⁅pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)),
        pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K))⁆ ≤ D.rootGroup r ∧
      pCoreOf 2 (Subgroup.normalizer (D.rootGroup r : Set K)) ≤
        Subgroup.centralizer (D.rootGroup r : Set K) := by
  refine ⟨(Subgroup.commutator_mono hC2 hC2).trans
      (commutator_highestRootRadical_le_rootGroup hext hcomm hdiv hr), ?_⟩
  exact hC2.trans (highestRootRadical_le_centralizer_rootGroup hext hcomm hdiv hr)

end CFSG.StandardType.LieKnownR2
