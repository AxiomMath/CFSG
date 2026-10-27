module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection16.proposition_16_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_1
import Mathlib.GroupTheory.Schreier
import Mathlib.Order.Preorder.Finite

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-! # Theorem 16 i from BG Section 16 -/

section MainResults

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]
public theorem CFSG.section16_typeI_KUData_of_complement
    {M MF U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hType : section16TypeI M MF)
    (hcomp : section12ComplementIn M MF U) :
    section16KUData M (⊥ : Subgroup G) U ∧ MF = section10Msigma M := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U₀, hKU15⟩
  have hKU : section16KUData M K U₀ := by
    simpa [section16KUData] using hKU15
  have hProp :=
    proposition_16_1 (G := G) (M := M) (MF := MF) (K := K) (U := U₀)
      hM hMF hKU
  have hCaseF : section16CaseF K U₀ := hProp.1.mp hType
  rcases hCaseF with ⟨hKbot, _hU₀ne⟩
  have hFamilyF : M ∈ section14MFamilyF G :=
    section16_MFamilyF_of_K_eq_bot (G := G) hM hKU hKbot
  have hMF_eq : MF = section10Msigma M := hProp.2.2.2.2.2.mpr (Or.inl hType)
  have hUcomp : section12ComplementToMsigma M U := by
    simpa [section12ComplementToMsigma, hMF_eq] using hcomp
  have hKU_exact15 : section15KUData M (⊥ : Subgroup G) U :=
    section15_KUData_of_empty_kappa_sigma_complement
      (G := G) (M := M) (U := U) hM hFamilyF.2 hUcomp
  exact ⟨by simpa [section16KUData] using hKU_exact15, hMF_eq⟩

private theorem CFSG.section16_not_typeI_of_MFamilyP
    {M MF : Subgroup G}
    (hMP : M ∈ section14MFamilyP G)
    (hMF : section16MFSubgroup M MF) :
    ¬ section16TypeI M MF := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hMP.1 with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U :=
    section16_KUData_of_section15 (G := G) hKU15
  have hKne : K ≠ ⊥ :=
    section16_K_ne_bot_of_MFamilyP (G := G) hMP hKU15.1
  intro hType
  have hCaseF : section16CaseF K U :=
    section16_caseF_of_typeI (G := G) hMP.1 hMF hKU hType
  exact hKne ((section16_caseF_iff_K_eq_bot (G := G) hMP.1 hMF hKU).1 hCaseF)

/-- A maximal subgroup in BG Type `P` cannot be BG Type `I`. -/
public theorem CFSG.section16_not_typeI_of_maximalTypeP
    {M MF : Subgroup G}
    (hMP : section16MaximalTypeP M)
    (hMF : section16MFSubgroup M MF) :
    ¬ section16TypeI M MF := by
  have hMP14 : M ∈ section14MFamilyP G := by
    simpa [section16MaximalTypeP] using hMP
  exact section16_not_typeI_of_MFamilyP (G := G) hMP14 hMF

public theorem CFSG.section16_typeI_of_not_MFamilyP
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hnotP : M ∉ section14MFamilyP G) :
    section16TypeI M MF := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U :=
    section16_KUData_of_section15 (G := G) hKU15
  by_cases hKbot : K = ⊥
  · exact section16_typeI_of_caseF (G := G) hM hMF hKU
      ((section16_caseF_iff_K_eq_bot (G := G) hM hMF hKU).2 hKbot)
  · have hMP : M ∈ section14MFamilyP G :=
      section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU15.1 hKbot
    exact False.elim (hnotP hMP)

private theorem CFSG.section16_typeII_to_V_of_K_ne_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKne : K ≠ ⊥) :
    section16TypeII M MF ∨ section16TypeIII M MF ∨ section16TypeIV M MF ∨
      section16TypeV M MF := by
  classical
  by_cases hUbot : U = ⊥
  · have hCaseP1 : section16CaseP1 K U := ⟨hKne, hUbot⟩
    by_cases hMFeq : MF = section10Msigma M
    · exact Or.inr <| Or.inr <| Or.inr <|
        section16_typeV_of_caseP1_eq (G := G) hM hMF hKU hCaseP1 hMFeq
    · rcases section16_typeIII_or_typeIV_of_caseP1_ne
        (G := G) hM hMF hKU hCaseP1 hMFeq with hTypeIII | hTypeIV
      · exact Or.inr <| Or.inl hTypeIII
      · exact Or.inr <| Or.inr <| Or.inl hTypeIV
  · exact Or.inl
      (section16_typeII_of_caseP2 (G := G) hM hMF hKU ⟨hKne, hUbot⟩)


/-- The five BG16 types exhaust the possibilities for a maximal subgroup and
its `M_F`. -/
public theorem CFSG.section16_type_exhaustive_of_maximal
    {M MF : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF) :
    section16TypeI M MF ∨ section16TypeII M MF ∨
      section16TypeIII M MF ∨ section16TypeIV M MF ∨ section16TypeV M MF := by
  classical
  rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
    ⟨K, U, hKU15⟩
  have hKU : section16KUData M K U :=
    section16_KUData_of_section15 (G := G) hKU15
  by_cases hKbot : K = ⊥
  · have hF : section16CaseF K U :=
      (section16_caseF_iff_K_eq_bot (G := G) hM hMF hKU).2 hKbot
    exact Or.inl (section16_typeI_of_caseF (G := G) hM hMF hKU hF)
  · rcases section16_typeII_to_V_of_K_ne_bot (G := G) hM hMF hKU hKbot with
      hII | hIII | hIV | hV
    · exact Or.inr (Or.inl hII)
    · exact Or.inr (Or.inr (Or.inl hIII))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hIV)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hV)))

public theorem CFSG.section16_typeII_of_MFamilyP2
    {M MF K U : Subgroup G}
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hP2 : M ∈ section14MFamilyP2 G) :
    section16TypeII M MF := by
  classical
  have hKU15 : section15KUData M K U :=
    section16_kudata_to_section15 (G := G) hKU
  have hKne : K ≠ ⊥ :=
    section16_K_ne_bot_of_MFamilyP (G := G) hP2.1 hKU15.1
  have hUne : U ≠ ⊥ :=
    section16_U_ne_bot_of_MFamilyP2 (G := G) hKU15 hP2
  exact section16_typeII_of_caseP2 (G := G) hP2.1.1 hMF hKU ⟨hKne, hUne⟩

public theorem CFSG.section16_exists_KUData_of_kappa_hall
    {M K : Subgroup G}
    (hMP : section16MaximalTypeP M)
    (hK : section12HallSubgroupIn (section16KappaPrimes M) K M) :
    ∃ U : Subgroup G, section16KUData M K U := by
  classical
  have hMP14 : M ∈ section14MFamilyP G := by
    simpa [section16MaximalTypeP] using hMP
  have hK14 : section12HallSubgroupIn (section14KappaPrimes M) K M := by
    simpa [section16KappaPrimes] using hK
  rcases proposition_14_2_a (G := G) (M := M) (K := K) hMP14 hK14 with
    ⟨U, hU⟩
  exact ⟨U, section16_KUData_of_section15 (G := G)
    (section15_KUData_of_proposition14_2AData
      (G := G) (M := M) (K := K) hMP14.1 hK14 hU)⟩

public theorem CFSG.section16_exists_typeCommon_of_K_ne_bot
    {M MF K U : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hMF : section16MFSubgroup M MF)
    (hKU : section16KUData M K U)
    (hKne : K ≠ ⊥) :
    ∃ V : Subgroup G, section16TypeCommon M MF V K (section16Kstar M K) := by
  classical
  by_cases hUne : U ≠ ⊥
  · exact ⟨U, section16_typeCommon_of_caseP2 (G := G) hM hMF hKU hKne hUne⟩
  · have hUbot : U = ⊥ := not_not.mp hUne
    have hCaseP1 : section16CaseP1 K U := ⟨hKne, hUbot⟩
    by_cases hMFeq : MF = section10Msigma M
    · have hKU15 : section15KUData M K U :=
        section16_kudata_to_section15 (G := G) hKU
      have hD_eq_MF : ambientDerivedSubgroup M = MF := by
        have hD_eq :
            ambientDerivedSubgroup M = U ⊔ section10Msigma M :=
          (section16_derived_eq_um_sigma_iff_K_ne_bot
            (G := G) hM hMF hKU).2 hKne
        simpa [hUbot, hMFeq] using hD_eq
      have hCompMFbot :
          section12ComplementIn (ambientDerivedSubgroup M) MF (⊥ : Subgroup G) := by
        refine ⟨?_, bot_le, ?_, disjoint_bot_right⟩
        · rw [hD_eq_MF]
        · simp [hD_eq_MF]
      have hBotNil : Group.IsNilpotent (⊥ : Subgroup G) := inferInstance
      have hKleNormBot :
          K ≤ subgroupNormalizerIn M (((⊥ : Subgroup G) : Set G)) := by
        intro x hxK
        have hxnorm : x ∈ Subgroup.normalizer (((⊥ : Subgroup G) : Set G)) := by
          rw [Subgroup.mem_normalizer_iff]
          intro n
          simp
        exact mem_subgroupNormalizerIn.mpr ⟨hxnorm, hKU15.1.1 hxK⟩
      have hT6Bot :
          ∀ A0 A1 : Subgroup G,
            section16PrimeOrderSubgroupOf A0 (⊥ : Subgroup G) →
              section16PrimeOrderSubgroupOf A1 (⊥ : Subgroup G) →
                section16ConjugateSubgroupsIn ⊤ A0 A1 →
                  ¬ section16ConjugateSubgroupsIn M A0 A1 →
                    subgroupCentralizerIn MF A0 = ⊥ ∨
                      subgroupCentralizerIn MF A1 = ⊥ := by
        intro A0 _A1 hA0 _hA1 _hConj _hNotM
        rcases hA0.2 with ⟨p, hcard⟩
        have hA0bot : A0 = ⊥ := le_bot_iff.mp hA0.1
        rw [hA0bot] at hcard
        have hpone : p.val = 1 := by simpa using hcard.symm
        exact False.elim (p.property.ne_one hpone)
      exact ⟨⊥, section16_typeCommon_of_caseP_with_complement
        (G := G) hM hMF hKU hKne hCompMFbot hBotNil hKleNormBot hT6Bot⟩
    · rcases section16_exists_p1_complement_package
        (G := G) hM hMF hKU hCaseP1 hMFeq with
        ⟨V, hCompMFV, hVnil, hKleNormV, hVσ, _hNormV⟩
      have hT6 :=
        section16_typeCommon_T6_of_msigma_subgroup
          (G := G) hM hMF hKU hVσ
      exact ⟨V, section16_typeCommon_of_caseP_with_complement
        (G := G) hM hMF hKU hKne hCompMFV hVnil hKleNormV hT6⟩

/-- Theorem I: the first main theorem of FT, in the Section 16 type notation. -/
public theorem CFSG.theorem_16_I :
    (∀ H : Subgroup G,
      section16HallSubgroupOf H ⊤ → Group.IsNilpotent H →
        ∀ x y : G, x ∈ H → y ∈ H →
          (section16ConjugateInSubgroup ⊤ x y ↔
            section16ConjugateInSubgroup (Subgroup.normalizer (H : Set G)) x y)) ∧
    ((∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
      ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ section16TypeI M MF) ∨
      ∃ W W1 W2 S T SF TF : Subgroup G,
        section12InternalDirectProduct W1 W2 W ∧ IsCyclic W ∧ W1 ≠ ⊥ ∧ W2 ≠ ⊥ ∧
        (∀ W0 : Set G, W0.Nonempty → W0 ⊆ (W : Set G) \ ((W1 : Set G) ∪ (W2 : Set G)) →
          Subgroup.normalizer W0 = W) ∧
        S ∈ section9MaximalSubgroups G ∧ T ∈ section9MaximalSubgroups G ∧
        section16MFSubgroup S SF ∧ section16MFSubgroup T TF ∧
        ¬ section16TypeI S SF ∧ ¬ section16TypeI T TF ∧
        S = W1 ⊔ ambientDerivedSubgroup S ∧
        T = W2 ⊔ ambientDerivedSubgroup T ∧
        ambientDerivedSubgroup S ⊓ W1 = ⊥ ∧
        ambientDerivedSubgroup T ⊓ W2 = ⊥ ∧
        W2 ≤ section16SecondDerivedSubgroup S ∧
        W1 ≤ section16SecondDerivedSubgroup T ∧
        S ⊓ T = W ∧
        (∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
          (∃ g : G, M = S.conjBy g) ∨ (∃ g : G, M = T.conjBy g) ∨
            ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ section16TypeI M MF) ∧
        (section16TypeII S SF ∨ section16TypeII T TF) ∧
        (section16TypeII S SF ∨ section16TypeIII S SF ∨ section16TypeIV S SF ∨
          section16TypeV S SF) ∧
        (section16TypeII T TF ∨ section16TypeIII T TF ∨ section16TypeIV T TF ∨
          section16TypeV T TF) ∧
        ∃ U V : Subgroup G,
          section16TypeCommon S SF U W1 W2 ∧
            section16TypeCommon T TF V W2 W1) := by
  refine ⟨?_, ?_⟩
  · intro H hHall hNil x y hxH hyH
    exact section16_nilpotent_hall_fusion_control
      (G := G) H hHall hNil x y hxH hyH
  · by_cases hAllTypeI :
      ∀ M : Subgroup G, M ∈ section9MaximalSubgroups G →
        ∃ MF : Subgroup G, section16MFSubgroup M MF ∧ section16TypeI M MF
    · exact Or.inl hAllTypeI
    · right
      push Not at hAllTypeI
      rcases hAllTypeI with ⟨M, hM, hNoTypeI⟩
      rcases section16_exists_mfSubgroup (G := G) M with ⟨MF, hMF⟩
      rcases section15_exists_KUData_for_maximal (G := G) (M := M) hM with
        ⟨K, U, hKU15⟩
      have hKU : section16KUData M K U :=
        section16_KUData_of_section15 (G := G) hKU15
      have hNotTypeI : ¬ section16TypeI M MF := by
        intro hType
        exact hNoTypeI MF hMF hType
      have hKne : K ≠ ⊥ := by
        intro hKbot
        have hTypeI : section16TypeI M MF :=
          section16_typeI_of_caseF (G := G) hM hMF hKU
            ((section16_caseF_iff_K_eq_bot (G := G) hM hMF hKU).2 hKbot)
        exact hNotTypeI hTypeI
      have hMP : M ∈ section14MFamilyP G :=
        section16_MFamilyP_of_nontrivial_hall_kappa (G := G) hM hKU15.1 hKne
      let Kstar : Subgroup G := section16Kstar M K
      have hC : section16TheoremCConclusions M MF K U :=
        theorem_16_C (G := G) hM hMF hKU hKne
      rcases hC with
        ⟨_hUcomm, _hNormUNotLeM, _hKstarCyclic, hKstarPos, _hKstarMF,
          _hMFnotCyclic, _hDerEq, hKstarSecond, hPartner⟩
      rcases hPartner with
        ⟨Mstar, hMstarP, _hUnique, hKstarEq, hKstarHall,
          _hCentralizersKstar, _hCentralizersK, hInter, hZdp, hZcyc, hCaseP2_or,
          hCoverP, hHatZTI, _hConjHatZ, _hA0TI, _hUneExtra, _hUbotExtra⟩
      rcases section16_exists_mfSubgroup (G := G) Mstar with ⟨TF, hTF⟩
      rcases section15_exists_KUData_for_maximal (G := G) (M := Mstar) hMstarP.1 with
        ⟨KT, UT, hKUT15⟩
      have hKUT : section16KUData Mstar KT UT :=
        section16_KUData_of_section15 (G := G) hKUT15
      have hKTne : KT ≠ ⊥ :=
        section16_K_ne_bot_of_MFamilyP (G := G) hMstarP hKUT15.1
      have hNotTypeI_Mstar : ¬ section16TypeI Mstar TF :=
        section16_not_typeI_of_MFamilyP (G := G) hMstarP hTF
      have hCompM : section12ComplementIn M K (ambientDerivedSubgroup M) :=
        theorem_14_7_h (G := G) (M := M) (K := K) hMP hKU15.1
      have hCompMstar : section12ComplementIn Mstar Kstar (ambientDerivedSubgroup Mstar) := by
        simpa [Kstar] using
          theorem_14_7_h (G := G) (M := Mstar) (K := Kstar)
            hMstarP (by simpa [Kstar, section16KappaPrimes] using hKstarHall)
      have hHatWNormalizer :
          ∀ W0 : Set G, W0.Nonempty →
            W0 ⊆ ((K ⊔ Kstar : Subgroup G) : Set G) \ ((K : Set G) ∪ (Kstar : Set G)) →
              Subgroup.normalizer W0 = (K ⊔ Kstar : Subgroup G) := by
        intro W0 hW0ne hW0sub
        have hTI :
            section16TISubsetWithNormalizer (section16HatW K Kstar)
              (K ⊔ Kstar : Subgroup G) := by
          simpa [Kstar, section16HatW, section16HatZ, section16ZSubgroup] using hHatZTI
        have hWcomm : IsMulCommutative (K ⊔ Kstar : Subgroup G) := by
          have hZcyc' : IsCyclic (K ⊔ Kstar : Subgroup G) := by
            change IsCyclic (section16ZSubgroup K Kstar)
            exact hZcyc
          letI : IsCyclic (K ⊔ Kstar : Subgroup G) := hZcyc'
          infer_instance
        exact section16_hatW_subset_normalizer_eq_of_ti
          (G := G) hTI hWcomm hW0ne
          (by simpa [section16HatW] using hW0sub)
      have hMaximalCover :
          ∀ N : Subgroup G, N ∈ section9MaximalSubgroups G →
            (∃ g : G, N = M.conjBy g) ∨ (∃ g : G, N = Mstar.conjBy g) ∨
              ∃ NF : Subgroup G, section16MFSubgroup N NF ∧ section16TypeI N NF := by
        intro N hN
        by_cases hNP : N ∈ section14MFamilyP G
        · rcases hCoverP N (by simpa [section16MaximalTypeP] using hNP) with
            hNM | hNMstar
          · exact Or.inl hNM
          · exact Or.inr <| Or.inl hNMstar
        · rcases section16_exists_mfSubgroup (G := G) N with ⟨NF, hNF⟩
          exact Or.inr <| Or.inr <|
            ⟨NF, hNF, section16_typeI_of_not_MFamilyP (G := G) hN hNF hNP⟩
      have hTypeII_or : section16TypeII M MF ∨ section16TypeII Mstar TF := by
        rcases hCaseP2_or with hCaseP2 | hMstarP2
        · exact Or.inl (section16_typeII_of_caseP2 (G := G) hM hMF hKU hCaseP2)
        · exact Or.inr
            (section16_typeII_of_MFamilyP2 (G := G) hTF hKUT
              (by simpa [section16MaximalTypeP2] using hMstarP2))
      have hMTypeLate :
          section16TypeII M MF ∨ section16TypeIII M MF ∨ section16TypeIV M MF ∨
            section16TypeV M MF :=
        section16_typeII_to_V_of_K_ne_bot (G := G) hM hMF hKU hKne
      have hMstarTypeLate :
          section16TypeII Mstar TF ∨ section16TypeIII Mstar TF ∨
            section16TypeIV Mstar TF ∨ section16TypeV Mstar TF :=
        section16_typeII_to_V_of_K_ne_bot (G := G) hMstarP.1 hTF hKUT hKTne
      rcases section16_exists_typeCommon_of_K_ne_bot
          (G := G) hM hMF hKU hKne with
        ⟨US, hSTypeCommon⟩
      rcases section16_exists_KUData_of_kappa_hall
          (G := G) hMstarP hKstarHall with
        ⟨UTaligned, hKUTaligned⟩
      rcases section16_exists_typeCommon_of_K_ne_bot
          (G := G) hMstarP.1 hTF hKUTaligned (ne_of_gt hKstarPos) with
        ⟨VT, hTTypeCommonRaw⟩
      have hKstarStar_eq_K : section16Kstar Mstar Kstar = K := by
        simpa [Kstar, section16Kstar] using hKstarEq.symm
      have hTTypeCommon : section16TypeCommon Mstar TF VT Kstar K := by
        simpa [Kstar, hKstarStar_eq_K] using hTTypeCommonRaw
      have hCstar : section16TheoremCConclusions Mstar TF Kstar UTaligned :=
        theorem_16_C (G := G) hMstarP.1 hTF hKUTaligned (ne_of_gt hKstarPos)
      have hKSecondMstar : K ≤ section16SecondDerivedSubgroup Mstar := by
        rcases hCstar with
          ⟨_hUcommStar, _hNormUNotLeMStar, _hKstarStarCyclic, _hKstarStarPos,
            _hKstarStarMF, _hTFnotCyclic, _hDerEqStar, hKstarStarSecond,
            _hPartnerStar⟩
        simpa [Kstar, hKstarStar_eq_K] using hKstarStarSecond
      refine ⟨K ⊔ Kstar, K, Kstar, M, Mstar, MF, TF, ?_⟩
      refine ⟨?_, ?_, hKne, ?_, ?_, hM, hMstarP.1, hMF, hTF, ?_, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, hMaximalCover, hTypeII_or, hMTypeLate,
        hMstarTypeLate, ?_⟩
      · simpa [Kstar, section16ZSubgroup] using hZdp
      · change IsCyclic (section16ZSubgroup K Kstar)
        exact hZcyc
      · exact ne_of_gt hKstarPos
      · exact hHatWNormalizer
      · exact section16_not_typeI_of_MFamilyP (G := G) hMP hMF
      · exact hNotTypeI_Mstar
      · simpa using hCompM.2.2.1
      · simpa [Kstar] using hCompMstar.2.2.1
      · simpa [inf_comm] using hCompM.2.2.2.eq_bot
      · simpa [Kstar, inf_comm] using hCompMstar.2.2.2.eq_bot
      · simpa [Kstar] using hKstarSecond
      · exact hKSecondMstar
      · simpa [Kstar, section16ZSubgroup] using hInter
      · exact ⟨US, VT, by simpa [Kstar] using hSTypeCommon, hTTypeCommon⟩

end MainResults
