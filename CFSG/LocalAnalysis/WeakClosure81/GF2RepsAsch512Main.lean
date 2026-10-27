module

public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Core
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512FStar
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Lift
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512L3Wr
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch512Wr
public import CFSG.LocalAnalysis.AGLEmbedding.CatalogSchreier
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A3NativeSchreier
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CF2a

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsL2 IsU3)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)
open CFSG.Blueprint (LieModel)

theorem shape512_of_shape512Quot {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (h : Shape512Quot (CFSG.Open.genFittingFStar
      (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore))) : Shape512 H := by
  have hN := normal_subgroupOf_relPPrimeCore 3 H
  have hq : ∀ {P : ∀ (X : Type) [Group X], Prop},
      P ↥(CFSG.Open.genFittingFStar (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore)) →
      HasQuotShape (fStarMod (relPPrimeCore 3 H) H) (relPPrimeCore 3 H : Set G) P :=
    fun hP => hasQuotShape_fStarMod_of_mulEquiv hN (MulEquiv.refl _) hP
  rcases h with ⟨p, e, hp, h5, h9, h1⟩ | ⟨p, f, hp, h5, ⟨h3, h4, h2⟩ | ⟨h3, h4, h2⟩⟩ |
      ⟨h7, hP⟩ | ⟨n, hn, h2 | h2⟩
  · exact Or.inl ⟨p, e, hp, h5, h9, hq h1⟩
  · exact Or.inr (Or.inl ⟨p, f, hp, h5, Or.inl ⟨h3, h4, hq h2⟩⟩)
  · exact Or.inr (Or.inl ⟨p, f, hp, h5, Or.inr ⟨h3, h4, hq h2⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨hq h7, hasQuotShape_of_quot hN hP⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨n, hn, Or.inl (hq h2)⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨n, hn, Or.inr (hq h2)⟩))

section Main

set_option linter.unusedSectionVars false


theorem asch5_12_of_inputs (hA : Asch80L3EpsWreathed) (hS : L3EpsWreathedNoCalL1) :
    Asch5_12 := by
  intro G _ _ H T hK hT hTH h3 hno hne
  by_cases hHs : Group.IsSolvable ↥H
  · exact ⟨calNIn_eq_lGen_of_isSolvable hTH hne, Or.inl hHs⟩
  have hRs : Group.IsSolvable ↥(relPPrimeCore 3 H) := isSolvable_relPPrimeCore_three hK hno
  have hRH : relPPrimeCore 3 H ≤ H := relPPrimeCore_le_ambient 3 H
  haveI hRn : ((relPPrimeCore 3 H).subgroupOf H).Normal := normal_subgroupOf_relPPrimeCore 3 H
  have hHR : ¬ H ≤ relPPrimeCore 3 H := fun hle =>
    hHs (Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle))
  let π := QuotientGroup.mk' ((relPPrimeCore 3 H).subgroupOf H).normalCore
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hYns : ¬ Group.IsSolvable (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore) :=
    fun hY => hHs (isSolvable_of_isSolvable_quot hRH hRs hY)
  obtain ⟨hEs, hEnab, hEC⟩ := genFittingFStar_simple_of_pRank_three_le_one
    (pPrimeCore_three_quot_relPPrimeCore_eq_bot H)
    ((pRank_three_quot_relPPrimeCore_le H).trans h3) hYns
  haveI : (CFSG.Open.genFittingFStar
      (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore)).Normal :=
    CFSG.ComponentClassification.GeneralizedFitting.normal _
  haveI := hEs
  have hEno : ¬ IsCalL1 ↥(CFSG.Open.genFittingFStar
      (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore)) := fun h =>
    hno ⟨_, inferInstance, isCompositionFactor_of_quot (isCompositionFactor_self_of_normal _ hEs), h⟩
  have hKE : CFSG.Open.IsKGroup ↥(CFSG.Open.genFittingFStar
      (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore)) :=
    (hK.of_surjective π hπ).of_injective (Subgroup.subtype _) (Subgroup.subtype_injective _)
  have hcat := hKE.isCatalogGroup_of_surjective ⊤ hEnab (Subgroup.subtype ⊤)
    (fun x => ⟨⟨x, trivial⟩, rfl⟩)
  have hq : Group.IsSolvable ((↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore) ⧸
      CFSG.Open.genFittingFStar (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore)) :=
    isSolvable_quotient_of_outSolvable _ (by rw [hEC]; exact bot_le)
      (CFSG.QuasithinUnique.Vol2Native.outSolvable_of_isSolvable_outer
        (CFSG.AGLEmbedding.kFactCatalogSchreier_holds _ hEs hEnab hcat))
  have h3E : CFSG.Open.pRank 3 (⊤ : Subgroup ↥(CFSG.Open.genFittingFStar
      (↥H ⧸ ((relPPrimeCore 3 H).subgroupOf H).normalCore))) = 1 := by
    refine le_antisymm ((CFSG.RankThree.PartTwo.Sec20.Res5.pRank_top_subgroup_le _).trans
      ((pRank_three_quot_relPPrimeCore_le H).trans h3)) (one_le_pRank_three_of_three_dvd ?_)
    by_contra h3d
    obtain ⟨i, ⟨ei⟩⟩ := hcat
    obtain ⟨f, hf⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd
      _ hEnab ⟨i, ⟨ei⟩⟩ h3d
    exact hEno (isCalL1_of_suzukiModel hf)
  have hTb : IsSylowIn 2 ((T.subgroupOf H).map π) ⊤ := isSylowIn_top_map π hπ hT
  rcases asch512_quot hA hS hEs hEnab hEC hq hKE h3E hTb hEno with ⟨hcf, hshape⟩ | hgen
  · have hnoX : ∀ X : Subgroup G, T ≤ X → X ≤ H → ¬ HasCompFactor X IsCalL1 := by
      rintro X hTX hXH ⟨L, _, hcfX, hL⟩
      haveI : Finite L := isCompositionFactor_finite hcfX
      have h1 := isCompositionFactor_map_of_le hRs hXH hcfX (exists_mul_ne_of_isCalL1 hL)
      have hTX' : (T.subgroupOf H).map π ≤ (X.subgroupOf H).map π :=
        Subgroup.map_mono (fun t ht => by
          rw [Subgroup.mem_subgroupOf] at ht ⊢
          exact hTX ht)
      exact hno ⟨L, inferInstance, isCompositionFactor_of_quot (hcf _ hTX' L h1 hL), hL⟩
    have hN : calNIn H T = {lGen IsCalL1 H T} :=
      calNIn_eq_lGen_of_forall hTH hne fun M hM => hnoX M hM.1 hM.2.1.le
    have hTblt : (T.subgroupOf H).map π < ⊤ := lt_top_of_isSylowIn_of_not_isSolvable hTb hYns
    let X₀ : Subgroup G := (((T.subgroupOf H).map π).comap π).map H.subtype
    have hX₀H : X₀ ≤ H := Subgroup.map_subtype_le _
    have hTX₀ : T ≤ X₀ := fun t ht =>
      ⟨⟨t, hTH.le ht⟩, Subgroup.mem_comap.2 (Subgroup.mem_map_of_mem π
        (Subgroup.mem_subgroupOf.2 ht)), rfl⟩
    have hRX₀ : relPPrimeCore 3 H ≤ X₀ := fun r hr => by
      refine ⟨⟨r, hRH hr⟩, Subgroup.mem_comap.2 ?_, rfl⟩
      have hr1 : π ⟨r, hRH hr⟩ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Subgroup.normalCore_eq_self, Subgroup.mem_subgroupOf]
        exact hr
      rw [hr1]
      exact Subgroup.one_mem _
    have hX₀lt : X₀ < H := by
      refine lt_of_le_of_ne hX₀H fun heq => hTblt.ne ?_
      rw [eq_top_iff]
      intro y _
      obtain ⟨h, hhy⟩ := hπ y
      have hh : (h : G) ∈ X₀ := by rw [heq]; exact h.2
      obtain ⟨h', hh', hhe⟩ := hh
      rw [← hhy, ← Subtype.ext hhe]
      exact hh'
    have hRL : relPPrimeCore 3 H ≤ lGen IsCalL1 H T :=
      hRX₀.trans (le_iSup₂_of_le X₀ ⟨hTX₀, hX₀lt, hnoX X₀ hTX₀ hX₀H⟩ le_rfl)
    exact ⟨hN, Or.inr ⟨hRs, hRL,
      shape512_of_shape512Quot (hshape (hasUniqueMaxOver_quot hTH.le hN hRL))⟩⟩
  · exact absurd (lGen_eq_of_quot hRs hHR hTH.le hgen).symm hne

theorem asch5_12_of_asch80L3EpsWreathed (hA : Asch80L3EpsWreathed) : Asch5_12 :=
  asch5_12_of_inputs hA l3EpsWreathedNoCalL1_holds

theorem asch5_12_holds : Asch5_12 :=
  asch5_12_of_asch80L3EpsWreathed asch80L3EpsWreathed_holds

end Main

end CFSG.LocalAnalysis.WeakClosure81

end
