module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15LinearM22
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3J2
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3J4
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3He
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3Ru
public import CFSG.LocalAnalysis.AGL81I.Section3.ThreeNineSporGenHeis3Mathieu

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Blueprint Subgroup
open CFSG.LocalAnalysis.AGL81I.Section3.SporGen
open CFSG.LocalAnalysis.AGL81I.Section3.SporGenThree
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)

theorem linear_order_dvd_center_quotient
    {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X) (hX : LieModel X .PSL 3 2 2) :
    20160 ∣ Nat.card (K ⧸ center K) := by
  have hXs := hX.isSimpleGroup_of_mem_classicalTags
    (by simp [CFSG.Blueprint.classicalTags])
  have hc := CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four
    (hX.statedClassicalModel (by simp [CFSG.Blueprint.classicalTags]))
  rw [← hc]
  exact Subgroup.card_dvd_of_injective _
    (quotient_center_inclusion_injective hXK hXq hXs)

theorem false_of_linear_sporadic_centGen
    {G : Type} [Group G] [Finite G] {X K P M E : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X) (hXs : IsSimpleGroup X)
    (hKq : CFSG.Open.IsQuasisimple K) (hEP : E ≤ P) (hPX : P ≤ X)
    (hE : IsElemAbelian 3 E) (hEc : Nat.card E = 9)
    (hGamma : rankThreeGamma 1 3 P ≤ M) (hKM : ¬ K ≤ M)
    (hZ : ¬ 3 ∣ Nat.card (center K)) {s : TauCeti.SporadicName}
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hcent : CFSG.LocalAnalysis.AGL81I.Section3.SporGen.SporadicCentGen 3 s) : False := by
  have : Group.IsPerfect K := Group.isPerfect_def.mpr hKq.1
  have : IsSimpleGroup (K ⧸ center K) := hKq.2
  have hQ : ∀ A : Subgroup (MulAut (K ⧸ center K)),
      IsElemAbelian 3 A → Nat.card A = 3 ^ 2 →
      A ≤ (MulAut.conj : (K ⧸ center K) →* MulAut (K ⧸ center K)).range →
      CFSG.LieType.SeitzGeneration.PlaneGen A := by
    intro A hA hAc hinner
    refine CFSG.LieType.SeitzGeneration.planeGen_of_inner
      (CFSG.LieType.SeitzGeneration.conj_injective_of_simple_perfect
        (Group.isPerfect_def.mp inferInstance)) ?_ hA hAc hinner
    intro B hB hBc
    have hcg : centGen B = ⊤ := hcent _ ⟨e⟩ B hB hBc
    apply top_le_iff.mp
    rw [← hcg, centGen]
    refine iSup_le fun b => iSup_le fun hb => iSup_le fun hb1 => ?_
    intro k hk
    exact Subgroup.subset_closure ⟨b, hb, hb1,
      Subgroup.mem_centralizer_singleton_iff.mp hk⟩
  exact false_of_unitary_plane_generation hEP hE hGamma hKM
    (plane_generation_of_quotient_inner_planeGen hXK hXq hXs hKq
      (hEP.trans hPX) hE (by simpa using hEc) hZ hQ)


section Prune


theorem linear_sporadic_quotient_models
    {G : Type} [Group G] [Finite G] {X K : Subgroup G}
    (hXK : X ≤ K) (hXq : CFSG.Open.IsQuasisimple X) (hX : LieModel X .PSL 3 2 2)
    (hr : CFSG.Open.pRank 3 K ≤ 3) (hZ : ¬ 3 ∣ Nat.card (center K))
    {s : TauCeti.SporadicName}
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) :
    s = .M22 ∨ s = .M23 ∨ s = .M24 ∨ s = .J2 ∨ s = .J4 ∨
      s = .HS ∨ s = .He ∨ s = .Ru := by
  have hdiv := linear_order_dvd_center_quotient hXK hXq hX
  rw [Nat.card_congr e.toEquiv,
    CFSG.HardMathSupport.Solomon.Coordinator.sporadicOrdersTable_holds s] at hdiv
  have hq : CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ center K)) ≤ 3 := by
    rw [CFSG.SectionRank.pRank_quotient_eq (center K) hZ,
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hr
  by_cases hsMcL : s = .McL
  · subst s
    have : Finite (TauCeti.CFSGIndex.sporadic .McL).Group :=
      Finite.of_equiv (K ⧸ center K) e.toEquiv
    have h4 := CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.four_le_pRank_of_elem
      .McL (CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .McL)
      CFSG.SectionRank.McL_elementary_three_rank_four
    have h4' : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (K ⧸ center K)) := by
      rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e]
      exact h4
    omega
  by_contra hnot
  have hFour : RankFourSporadic s := by
    cases s <;> simp_all [CFSG.HardMathSupport.Solomon.Coordinator.sporOrd,
      orderJ3, orderJ4, orderRu, orderTh, orderBabyMonster, orderMonster, orderON, orderHN,
      orderFi23, orderFi24Prime, orderCo1, orderLy, RankFourSporadic]
  have h4 := four_le_pRank_of_rankFourSporadic s hFour (K ⧸ center K) ⟨e⟩
  omega

end Prune

section Sporadic


theorem rest15_false_of_linear_sporadic_quotient_of_ne_m22
    {G : Type} [Group G] [Finite G]
    (_hS : Standing4 G) (_hU : uniqueFourUnique G) (S : Setup4 G)
    (_hMS : S.InMSigma) (_hPart : PartIAt S.M)
    {L X H K P : Subgroup G} (_hL : L ∈ calC S.M)
    (_hLN : S.M ≤ normalizer (L : Set G)) (_hthin : ¬ F08.Thin8 L)
    (_hXL : X ≤ L) (_hsupp : X ⊔ pCoreOf 2 L = L)
    (_hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (_hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (_hNormal : (X.subgroupOf (H ⊓ S.M)).Normal)
    (_hGammaH : rankThreeGamma 1 3 (P.subgroupOf H) ≤
      (normalizer (X : Set G)).subgroupOf H)
    (hZK : ¬ 3 ∣ Nat.card (center K))
    (_hAlt : ¬ ∃ n : ℕ, 5 ≤ n ∧
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n)))
    {s : TauCeti.SporadicName}
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hs : s ≠ .M22) : False := by
  have hKq := hKcomp.2.2
  have hXq := hXcomp.2.2
  have hKr : CFSG.Open.pRank 3 K ≤ 3 :=
    (CFSG.SectionRank.pRank_mono Nat.prime_three.one_lt hKcomp.1).trans hHr
  have hmodels := linear_sporadic_quotient_models hXK hXq hX hKr hZK e
  have hcent : CFSG.LocalAnalysis.AGL81I.Section3.SporGen.SporadicCentGen 3 s := by
    rcases hmodels with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hs rfl).elim
    · exact sporadicCentGen_three_of_row .M23 (Or.inl rfl)
    · exact CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_M24_three
    · exact CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_J2_three
    · exact CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_J4_three
    · exact sporadicCentGen_three_of_row .HS (Or.inr rfl)
    · exact CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_He_three
    · exact CFSG.LocalAnalysis.AGL81I.Section3.SporGen.ThreeHeis.sporadicCentGen_Ru_three
  have hXs := hX.isSimpleGroup_of_mem_classicalTags
    (by simp [CFSG.Blueprint.classicalTags])
  have hthree : 2 ≤ CFSG.Open.pRank 3 X := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hX.two_le_pRank_psl3_of_dvd Nat.prime_three (by norm_num)
  have hPr : 2 ≤ CFSG.Open.pRank 3 P := by
    rwa [CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow
      Nat.prime_three hP]
  obtain ⟨E, hEP, hEe, hEc⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.exists_elemAbelian_card_of_le_pRank
      Nat.prime_three hPr
  exact false_of_linear_sporadic_centGen hXK hXq hXs hKq hEP hP.le hEe
    (by simpa using hEc) hGamma hKM hZK e hcent

theorem rest15_false_of_linear_sporadic_quotient
    {G : Type} [Group G] [Finite G]
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G)
    (hMS : S.InMSigma) (hPart : PartIAt S.M)
    {L X H K P : Subgroup G} (hL : L ∈ calC S.M)
    (hLN : S.M ≤ normalizer (L : Set G)) (hthin : ¬ F08.Thin8 L)
    (hXL : X ≤ L) (hsupp : X ⊔ pCoreOf 2 L = L)
    (hHtop : H ≠ ⊤) (hHr : CFSG.Open.pRank 3 H ≤ 3)
    (hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (hNormal : (X.subgroupOf (H ⊓ S.M)).Normal)
    (hGammaH : rankThreeGamma 1 3 (P.subgroupOf H) ≤
      (normalizer (X : Set G)).subgroupOf H)
    (hZK : ¬ 3 ∣ Nat.card (center K))
    (hAlt : ¬ ∃ n : ℕ, 5 ≤ n ∧
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n)))
    {s : TauCeti.SporadicName}
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.sporadic s).Group) : False := by
  by_cases hs : s = .M22
  · subst s
    exact rest15_false_of_linear_m22_quotient hS hU S hMS hPart hL hLN hthin
      hXL hsupp hHtop hHr hnotStrong hXcomp hKcomp hXK hKM hX hP hGamma
      hNormal hGammaH hZK hAlt e
  · exact rest15_false_of_linear_sporadic_quotient_of_ne_m22 hS hU S hMS hPart
      hL hLN hthin hXL hsupp hHtop hHr hnotStrong hXcomp hKcomp hXK hKM hX hP
      hGamma hNormal hGammaH hZK hAlt e hs

end Sporadic

end CFSG.LocalAnalysis.UniquenessCase.UC22
