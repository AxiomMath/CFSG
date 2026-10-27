module

public import CFSG.RankThree.PartTwo.Sec4.Item413FixProofCases
public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofG23Inner
public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofON
public import CFSG.RankThree.PartTwo.Sec4.Item413CoverProofL2Three
import CFSG.RankThree.PartTwo.Sec4.Item413A9
import CFSG.RankThree.PartTwo.Sec4.Item413AutSp4
public import CFSG.RankThree.PartTwo.Sec21.Item223RankResProofAut
public import CFSG.RankThree.PartTwo.Sec4.Item413
public import CFSG.RankThree.PartTwo.Sec4.Item413FixProof
public import CFSG.RankThree.PartTwo.Sec4.Item413J3
public import CFSG.RankThree.PartTwo.Sec4.Item413Native
public import CFSG.RankThree.PartTwo.Sec4.Item47CoreClosed

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

theorem rank3II_4_13_forwardFix_of
    (h45 : Item4_5) (h46 : Item4_6) (hR : Inputs413Ranks) (hl2 : Inputs413L2Three)
    (hl3 : Inputs413L3Nine) (hcov : Inputs413CoverU43McL) (hON : Inputs413CoverON)
    (hG23 : Inputs413CoverG23Inner) : Item4_13_forwardFix := by
  intro G _ _ hG L hL A E c hT hr
  have hyp : Hyp413 L A E c := ⟨hG, hL, hT, hr⟩
  obtain ⟨hAmax, hAc, hc3, -, -, -⟩ := hT
  have hA := hAmax.prop
  obtain ⟨m, hm5, hm⟩ := exists_card_eq_of_four_lt_pRank hA hr
  have hcAC : c ∈ A ⊓ Subgroup.centralizer (L : Set G) := hAc ▸ Subgroup.mem_zpowers c
  have hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.1.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hLθ : L ∈ thetaComponents 3 G := mem_thetaComponents_of_isComponent3 hL
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    h45 G hG A (isPGroup_of_isElemAbelian hA) (Or.inr ⟨hA, m, by omega, hm⟩) L hLθ
  set B := (thetaAct hAN).range with hBdef
  have hB := isElemAbelian_range_thetaAct hAN hA
  have hBk : Nat.card B = 3 ^ (m - 1) := by
    have h1 := card_range_thetaAct_mul hL.1 hAN
    rw [hAc, Nat.card_zpowers, hc3, hm] at h1
    have h2 : 3 ^ m = 3 ^ (m - 1) * 3 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hk4 : 4 ≤ m - 1 := by omega
  have hZL := odd_card_center_of_le_normalizer hG hA (by omega) hm hAN
  have hZX : Odd (Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L))) :=
    Odd.of_dvd_nat hZL (card_center_thetaQuot_dvd hL.1)
  set H := Subgroup.centralizer ({c} : Set G) with hHdef
  have hcH : c ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  have hLH : L ≤ H := fun x hx => Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp hcAC.2 x hx)
  have hAH : A ≤ H := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (hcomm c hcAC.1 a ha).symm
  have hH : SectionFourHyp H := sectionFourHyp_subgroup hG H
  have h3H : 3 ∣ Nat.card (Subgroup.center H) := by
    have hz : (⟨c, hcH⟩ : H) ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro x
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp x.2)
    have hord : orderOf (⟨⟨c, hcH⟩, hz⟩ : Subgroup.center H) = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hc3]
    exact hord ▸ orderOf_dvd_natCard _
  set L' := L.subgroupOf H
  have hL' : L' ∈ thetaComponents 3 H := mem_thetaComponents_subgroupOf hL hLH
  set eθ : L' ⧸ aschbacherSolvableCore 3 L' ≃* L ⧸ aschbacherSolvableCore 3 L :=
    thetaQuotCongr (Subgroup.subgroupOfEquivOfLe hLH)
  set B' := B.map (MulAut.congr eθ.symm).toMonoidHom
  have hB' : CFSG.Assembly.IsElemAbelian 3 B' := isElemAbelian_map _ hB
  have hBk' : Nat.card B' = 3 ^ (m - 1) := by
    rw [Subgroup.card_map_of_injective (MulAut.congr eθ.symm).injective, hBk]
  by_cases hout : ∃ a ∈ A, InducesOuterTheta a L
  ·
    obtain ⟨a, haA, ha⟩ := hout
    have haH := hAH haA
    have ha1 : a ≠ 1 := by
      rintro rfl
      exact KFacts.not_inducesOuterTheta_one L ha
    have ha3 : orderOf (⟨a, haH⟩ : H) = 3 := by
      rw [Subgroup.orderOf_mk]
      exact orderOf_eq_prime (hA.2 a haA) ha1
    have h47 := rank3II_4_7W_of h46 H hH h3H L' hL' ⟨a, haH⟩ ha3
      (inducesOuterTheta_subgroupOf hLH haH ha)
    obtain ⟨e, he, ⟨e₁⟩⟩ := Res413Fix.exists_psl2_three_of_alt47W hR hL'.2.2 h47 hB' hBk' hk4
    exact Or.inl (Or.inl (hl2 G L A E c hyp e he ⟨eθ.symm.trans e₁⟩))
  ·
    simp only [not_exists, not_and] at hout
    have hBi := range_thetaAct_le_inner hAN hout
    have hBi' : B' ≤ (MulAut.conj : L' ⧸ aschbacherSolvableCore 3 L' →*
        MulAut (L' ⧸ aschbacherSolvableCore 3 L')).range := map_congr_range_conj_le _ hBi
    have hZX' : Odd (Nat.card (Subgroup.center (L' ⧸ aschbacherSolvableCore 3 L'))) := by
      rwa [card_center_congr eθ]
    rcases Res413Fix.isSpecial413_of_le_inner hR inputs47NoD4.centerSporadic
        (h46 H hH h3H L' hL') hL'.2.2 hZX' hB' hBi' hBk' hk4 with
        ⟨e, he, ⟨e₁⟩⟩ | h2 | h3 | h4 | ⟨hZ, h5⟩
    · exact Or.inl (Or.inl (hl2 G L A E c hyp e he ⟨eθ.symm.trans e₁⟩))
    · refine (hl3 G L A E c hyp ?_).elim
      rcases h2 with ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩
      · exact Or.inl ⟨eθ.symm.trans e₁⟩
      · exact Or.inr ⟨eθ.symm.trans e₁⟩
    · refine Or.inl (Or.inr (Or.inl (hcov G L A E c hyp ?_)))
      rcases h3 with ⟨h3, ⟨e₁⟩⟩ | hext
      · exact Or.inl ⟨by rw [← card_center_congr eθ, h3],
          ⟨(quotientCenterCongr eθ).symm.trans e₁⟩⟩
      · exact Or.inr (IsExtOf.of_mulEquiv eθ hext)
    · rcases h4 with ⟨h3, hG23'⟩ | hext
      ·
        have hZ3 : Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) = 3 := by
          rw [← card_center_congr eθ, h3]
        have hM : Blueprint.ChevalleyExceptionalModel ((L ⧸ aschbacherSolvableCore 3 L) ⧸
            Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) .G2 3 1 :=
          CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv (quotientCenterCongr eθ).symm
            hG23'
        obtain ⟨hθ, hZc, hinner⟩ := hG23 G L A E c hyp hZ3 hM
        exact Or.inr ⟨hθ, hZc, CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
          (Res417Three.thetaQuotCenterEquiv hL.1).symm hM, hinner⟩
      ·
        exact (hON G L A E c hyp (IsExtOf.of_mulEquiv eθ hext)).elim
    · refine Or.inl (Res413Fix.alt413_three hR hL hAmax hAc hAN hout hZL
        (center_eq_bot_of_mulEquiv eθ.symm hZ) ?_)
      rcases h5 with h | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩ | ⟨⟨e₁⟩⟩
      · exact Or.inl (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv eθ.symm h)
      · exact Or.inr (Or.inl ⟨eθ.symm.trans e₁⟩)
      · exact Or.inr (Or.inr (Or.inl ⟨eθ.symm.trans e₁⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨eθ.symm.trans e₁⟩))

theorem inputs413Ranks_holds :
    Inputs413Ranks where
  rankAutL2 := rankAutL2_holds
  rankAutL3 := rankAutL3_holds
  rankAutU3 := rankAutU3_holds
  rankAutSL3 := rankAutSL3_holds
  rankAutSU3 := rankAutSU3_holds
  rankAutSp4 := rankAutSp4_holds
  rankAutG2 := Sec21.rankAutG2_holds
  rankAutF4 := rankAutF4_of_twistedF4 Sec21.ReeF4ThreeLocalProof.twistedF4EvenThreeRankTwo_holds
  rankAutD4 := rankAutD4_holds
  rankG2 := Sec21.rankG2_holds
  rankSp4 := rankSp4_holds
  rankU4 := rankU4_holds
  rankL4 := rankL4_holds
  rankU4Even := rankU4Even_holds
  rankA9 := rankA9_holds
  rankSporadic := rankSporadic_of_J3 rankJ3_holds
  rankSeven := rankSeven_of_Sp62 rankSp62_holds
  rankEight := rankEight_holds
  rankTits := rankTits_holds
  multiplier := multiplier_holds

theorem rank3II_4_13_forwardFix_of_46
    (h46 : Item4_6) : Item4_13_forwardFix :=
  rank3II_4_13_forwardFix_of rank3II_4_5 h46 inputs413Ranks_holds inputs413L2Three_holds
    inputs413L3Nine_holds inputs413CoverU43McL_holds inputs413CoverON_holds
    inputs413CoverG23Inner_holds

end CFSG.RankThree.PartTwo.Sec4
