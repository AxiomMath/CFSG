module

public import CFSG.RankThree.PartTwo.Sec21.HeringSec217JList
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217JInner
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217JOut
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217JCover
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217JSp
public import CFSG.RankThree.PartTwo.Sec21.Item2130Res4ProofNoField
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutAssembly
public import CFSG.RankThree.PartTwo.Sec21.HeringSec217OutJStar

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Assembly.RankThreeEven (projSU)

section Main


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem sec217OutJ_of (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1) (h45 : Sec4.Item4_5)
    (h41 : Sec4.Item4_1LargePrime) (h1134 : Item1134Four) : Sec217OutJ := by
  intro G _ _ A E U c L a h hfr d hd htr J hJd hIJ hAJ hCA
  have hst : PartTwoStanding G := h.pair.standing
  have hAS : A ∈ partTwoS G := h.pair.mem_S
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.isElemAbelian_A
  have hmax := h.maximal
  have hA81 : Nat.card A = 3 ^ 4 := h.card
  obtain ⟨hd1, -⟩ := h.frame_of_zpowers_eq_inf h45 hfr hd
  obtain ⟨-, -, -, -, -, -, -, -, hDA, -⟩ := h.dgroup_decomp h45 hfr
  have hdDL : d ∈ dGroup a c ⊓ L := hd ▸ Subgroup.mem_zpowers d
  have hdA : d ∈ A := hDA hdDL.1
  have hab := isElemAbelian_iff.1 hAe
  have hd3 : d ^ 3 = 1 := hab.2 d hdA
  have hcomm : ∀ x ∈ A, x * d = d * x := fun x hx => hab.1 x hx d hdA
  have hJC : J ≤ Subgroup.centralizer ({d} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hJd
  have hq : IsQuasisimple (lBar J) := Sec6.isQuasisimple_of_mem_thetaComponentsAt hJd
  obtain ⟨U₀, hU₀, hU₀I, -⟩ := h.exists_U0 h45 hfr
  have hJstar : J ∈ lZeroStarAt A d :=
    h.mem_lZeroStarAt_component h45 hfr hd hU₀ hU₀I hJd hIJ hAJ hCA
  have hJ0 : J ∈ lZeroUnion A :=
    lZeroStar_subset_lZeroUnion A (lZeroStarAt_subset_lZeroStar A d hJstar)
  have hJs : J ∈ lStarAt A d :=
    ⟨lZeroStar_subset_lStar A (lZeroStarAt_subset_lZeroStar A d hJstar),
      lZeroStarAt_subset A d hJstar⟩
  have hsec : Late.sectionCentralizer A J ((aschbacherSolvableCore 3 J).map J.subtype) =
      (Subgroup.zpowers d : Set G) := by
    rw [Sec13.sectionCentralizer_eq_inf hAJ, hCA]
  have hnf := h1134 G A d J hst hAS.1 hA81 hdA hd1 hJs hsec
    (Item2130Res4Proof.exists_invTwoBarNontrivial hJ0)
  obtain ⟨t, htA, htr', hcom, hfix⟩ := htr
  obtain ⟨hfixel, hcomel⟩ := transvection_elementwise htA hfix hcom
  have htd : t * d * t⁻¹ = d := (hfixel d hdA).2 ⟨hdA, hdDL.2⟩
  have hIL : iCore L a ≤ L := (sSup_le fun _ hK => hK.1).trans inf_le_right
  have htI : ∀ y ∈ A ⊓ iCore L a, t * y * t⁻¹ = y := fun y hy =>
    (hfixel y hy.1).2 ⟨hy.1, hIL hy.2⟩
  have htJ : t ∈ Subgroup.normalizer (J : Set G) := h.normalizer_of_fixes h45 hfr hJd hIJ htd htI
  have hF27 : Nat.card (A ⊓ L : Subgroup G) = 27 := h.card_inf_eq h45
  have hAC : Nat.card (A ⊓ Sec4.thetaQuotCentralizer J : Subgroup G) ≤ 3 := by
    rw [hCA, Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
  have hfinish : Subgroup.center (lBar J) = ⊥ →
      (∀ x ∈ A, ¬ Sec4.InducesOuterTheta x J) → False := by
    intro hZ hin
    have h27 := j217_le_card_inf_of_inner hAe hmax hAJ hZ hin hAC hA81
    have hdJ : d ∉ J := by
      intro hdJ
      have hA3 : IsPGroup 3 (Subgroup.zpowers d) := by
        have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
        exact IsPGroup.of_card (n := 1) (by
          rw [Nat.card_zpowers, orderOf_eq_prime hd3 hd1]; rfl)
      have hdc : QuotientGroup.mk' (aschbacherSolvableCore 3 J) ⟨d, hdJ⟩ ∈
          Subgroup.center (lBar J) := by
        rw [Subgroup.mem_center_iff]
        intro z
        obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
        have hyd : (y : G) * d = d * y :=
          Subgroup.mem_centralizer_singleton_iff.1 (hJC y.2)
        rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
        congr 1
        exact Subtype.ext hyd
      rw [hZ, Subgroup.mem_bot] at hdc
      have hinj := CFSG.RankThree.injOn_mk_of_isPGroup Nat.prime_three
        (hA3.comap_subtype (K := J))
      have h1 : (⟨d, hdJ⟩ : J) = 1 :=
        hinj (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers d)) (one_mem _)
          (by rw [map_one]; exact hdc)
      exact hd1 (congrArg Subtype.val h1)
    exact j217_false_of_card_inf_le (F := A ⊓ L) ⟨hdA, hdDL.2⟩ inf_le_left hF27 hd3 hd1 hdJ htJ
      hfixel hcomel h27
  obtain ⟨-, -, hlist⟩ := listJ217_of h417 h611 h41 hst hAS hdA hd1 hJd hAJ hCA hJ0
  rcases hlist with
    ⟨x, hx, hk⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, ⟨eA⟩, -⟩ | ⟨h3, -⟩ | ⟨-, hJ3, -⟩ |
    ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨h3, -⟩ | ⟨-, ⟨n, hno, ⟨eU⟩⟩, -⟩ | ⟨-, hSp6, -⟩
  ·
    rcases hk with hk | hk
    · exact (hnf x hx).1 hk
    · exact (hnf x hx).2 hk
  · exact absurd (h3.symm.trans hA81) (by norm_num)
  · exact absurd (h3.symm.trans hA81) (by norm_num)
  · exact absurd (h3.symm.trans hA81) (by norm_num)
  ·
    haveI : IsSimpleGroup (alternatingGroup (Fin 9)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)
    refine hfinish (j217_center_eq_bot_of_equiv_simple hq.1 eA) fun x hx =>
      j217_not_inducesOuterTheta_of_hInn (by simpa using hab.2 x hx) (j217_hInn_A9 eA)
  · exact absurd (h3.symm.trans hA81) (by norm_num)
  ·
    rcases hJ3 with hJ3' | hcov
    · obtain ⟨eJ⟩ := hJ3'
      haveI hs : IsSimpleGroup NativeSporadic.J3 := CFSG.Sporadic.J3.isSimpleGroup_J3
      haveI : IsSimpleGroup (lBar J) := @MulEquiv.isSimpleGroup _ _ _ _ hs eJ
      exact hfinish (j217_center_eq_bot_of_perfect_simple hq.1) fun x hx =>
        j217_not_inducesOuterTheta_of_hInn (by simpa using hab.2 x hx) (j217_hInn_J3 hq.1 eJ)
    · exact Item2113Res3Proof.j217_false_of_cover ks217J3CoverPreimage_holds
        ks217J3CoverNoTransvection_holds hAe hmax hAJ hq hcov hA81 hdA hd1 hCA htA htJ htr'
  · exact absurd (h3.symm.trans hA81) (by norm_num)
  · exact absurd (h3.symm.trans hA81) (by norm_num)
  · exact absurd (h3.symm.trans hA81) (by norm_num)
  · exact absurd (h3.symm.trans hA81) (by norm_num)
  ·
    have hn1 : 1 ≤ n := hno.pos
    haveI : IsSimpleGroup (projSU 4 2 n) := isSimpleGroup_projSU le_rfl hn1
    haveI : IsSimpleGroup (lBar J) := @MulEquiv.isSimpleGroup _ _ _ _ inferInstance eU
    exact hfinish (j217_center_eq_bot_of_perfect_simple hq.1) fun x hx =>
      Item223PrintProof.not_inducesOuterTheta_of_mem_thetaComponentsAt hst.toTheoremFourHyp hd3
        hd1 hJd hn1 eU (hcomm x hx) (by simpa using hab.2 x hx)
  ·
    haveI : IsSimpleGroup (lBar J) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp (lBar J) 3 2 1
        hSp6
    exact hfinish (j217_center_eq_bot_of_perfect_simple hq.1) fun x hx =>
      j217_not_inducesOuterTheta_of_hInn (by simpa using hab.2 x hx)
        (fun σ hσ => kJ217OutSp62 hSp6 σ hσ)

end Main

section Final


set_option linter.unusedSectionVars false

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem item217NotInLLocal_of_items (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (h211 : Item211) (h212 : Item212) (h213 : Item213) (h214 : Item214Unitary) (h215 : Item215)
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h417 : Sec4.Item4_17) (h611 : Sec6.Item6_11_1) (h41 : Sec4.Item4_1LargePrime)
    (h1134 : Item1134Four) : Item217NotInLLocal :=
  item217NotInLLocal_of_J h45 h48 h211 h212 h213 h214 h215 hGA
    (sec217OutJ_of h417 h611 h45 h41 h1134)

end Final

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
