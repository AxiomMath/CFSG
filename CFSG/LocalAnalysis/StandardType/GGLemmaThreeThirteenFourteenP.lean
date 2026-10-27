module

public import CFSG.LocalAnalysis.StandardType.GGLemmaThreeThirteenFourteen
public import CFSG.LocalAnalysis.ComponentInitial.KProperPumpUpStatement
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial
  CFSG.ComponentClassification.OuterAutomorphisms

section Transfer

variable {G : Type} [Group G]

theorem ggAssemblyIsSubnormal_subgroupOf {A B : Subgroup G} (h : CFSG.Assembly.IsSubnormal A B)
    (X : Subgroup G) : CFSG.Assembly.IsSubnormal (A.subgroupOf X) (B.subgroupOf X) :=
  h.comap X.subtype

theorem ggIsComponentOf_subgroupOf {L H X : Subgroup G} (hL : CFSG.Assembly.IsComponentOf L H)
    (hHX : H ≤ X) : CFSG.Assembly.IsComponentOf (L.subgroupOf X) (H.subgroupOf X) := by
  have hLX : L ≤ X := hL.1.trans hHX
  have hq := (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native L).mp
    hL.2.2
  exact ⟨Subgroup.comap_mono hL.1, ggAssemblyIsSubnormal_subgroupOf hL.2.1 X,
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX).symm hq)⟩

variable [Finite G]

theorem ggOuter_solvable_of_catalogue (hSch : SchreierFor InCatalog) {X : Subgroup G}
    (hcat : ∀ K L' : Subgroup G, K ≤ X → L' ≤ K → ∀ [(L'.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L'.subgroupOf K) → (∃ a b : K ⧸ L'.subgroupOf K, a * b ≠ b * a) →
        InCatalog (K ⧸ L'.subgroupOf K))
    {K' : Subgroup X} (hK' : CFSG.IsComponent K') : Group.IsSolvable (Outer K') := by
  set K : Subgroup G := K'.map X.subtype
  let e₁ : K' ≃* K := K'.equivMapOfInjective X.subtype X.subtype_injective
  obtain ⟨hperf, hsimple, hnonab⟩ : CFSG.IsQuasisimple K :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁ hK'.1
  have := hsimple
  set L'' : Subgroup G := (Subgroup.center K).map K.subtype
  have hsub : L''.subgroupOf K = Subgroup.center K :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  have : (L''.subgroupOf K).Normal := by rw [hsub]; infer_instance
  let e₂ : K ⧸ L''.subgroupOf K ≃* K ⧸ Subgroup.center K :=
    QuotientGroup.quotientMulEquivOfEq hsub
  have : Nontrivial (K ⧸ L''.subgroupOf K) := e₂.toEquiv.nontrivial
  have hsimple' : IsSimpleGroup (K ⧸ L''.subgroupOf K) :=
    IsSimpleGroup.isSimpleGroup_of_surjective e₂.symm.toMonoidHom e₂.symm.surjective
  have hnonab' : ∃ a b : K ⧸ L''.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hnonab
    refine ⟨e₂.symm a, e₂.symm b, fun h => hab ?_⟩
    simpa using congrArg e₂ h
  obtain ⟨i, ⟨φ⟩⟩ := hcat K L'' (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _) hsimple'
    hnonab'
  have hcatK : InCatalog (K ⧸ Subgroup.center K) := ⟨i, ⟨e₂.symm.trans φ⟩⟩
  have : Group.IsSolvable (Outer (K ⧸ Subgroup.center K)) := hSch _ hnonab hcatK
  have : Group.IsPerfect K := hperf
  have : Group.IsSolvable (Outer K) := solvable_of_centerQuotient K
  exact solvable_of_equiv e₁.symm

end Transfer

theorem ggLemmaThreeFourteenPInput_of_schreier (hSch : SchreierFor InCatalog) :
    GGLemmaThreeFourteenPInput := by
  intro G _ _ p hp _ X H E hcat hE hEcard hfus L₁ hL hLO
  have : Fact p.Prime := ⟨hp⟩
  have hHX : H ≤ X := hfus.2.1
  have hEX : E ≤ X := hfus.1.trans hHX
  have hL₁X : L₁ ≤ X := hL.1.trans hHX
  have hEcard' : Nat.card (E.subgroupOf X) = p ^ 2 := by
    rw [← hEcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  have hLO' : ¬ L₁.subgroupOf X ≤ CFSG.pPrimeCore p ↥X := fun hle =>
    hLO (ggLe_map_pPrimeCore hL₁X hle)
  obtain ⟨K', hK', hLK'⟩ := ggLemmaThreeFourteen_top hfus.subgroupOf
    (ggIsElemAbelian_subgroupOf hE X) hEcard'
    (fun K' hK' => ggOuter_solvable_of_catalogue hSch hcat hK')
    (ggIsComponentOf_subgroupOf hL hHX) hLO'
  have hKX : K'.map X.subtype ≤ X := Subgroup.map_subtype_le _
  refine ⟨K'.map X.subtype, (isComponentOf_iff_isComponent_subgroupOf hKX).mpr ?_, ?_⟩
  · have hsub : (K'.map X.subtype).subgroupOf X = K' :=
      Subgroup.comap_map_eq_self_of_injective X.subtype_injective _
    rwa [hsub]
  · rw [← Subgroup.map_subgroupOf_eq_of_le hL₁X]
    exact Subgroup.map_mono hLK'

theorem ggLemmaThreeThirteenInput_holds : GGLemmaThreeThirteenInput :=
  ggLemmaThreeThirteenInput_of_p ggLemmaThreeThirteenPInput_holds

theorem ggLemmaThreeFourteenInput_of_schreier (hSch : SchreierFor InCatalog) :
    GGLemmaThreeFourteenInput :=
  ggLemmaThreeFourteenInput_of_p (ggLemmaThreeFourteenPInput_of_schreier hSch)

section Inputs

theorem ggSixStepTwoV2Input_of_schreier (hSch : SchreierFor InCatalog)
    (h613 : GGStepTwoLemmaSixThirteenInput) (hA : GGStepTwoLinearFusionInput)
    (hKF : GGKGroupFusionLegacyUnrestrictedInput) (hR : GGStepTwoAutKRestInput)
    (h615 : GGStepTwoCentralizerInput) : GGSixStepTwoV2Input :=
  ggSixStepTwoV2Input_of_coprime' h613 hA ggLemmaThreeThirteenPInput_holds
    (ggLemmaThreeFourteenPInput_of_schreier hSch) hKF hR h615

end Inputs

end CFSG.StandardType
