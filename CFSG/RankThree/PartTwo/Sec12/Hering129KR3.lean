module

public import CFSG.RankThree.PartTwo.Sec12.Hering129KR2
public import CFSG.RankThree.PartTwo.Sec12.Hering129KYc
public import CFSG.RankThree.PartTwo.Sec12.Hering129KEk
public import CFSG.RankThree.PartTwo.Sec12.Hering129KH6
public import CFSG.RankThree.PartTwo.Sec12.Hering129GHJBranch
public import CFSG.RankThree.PartTwo.Sec12.Hering129GMod9
public import CFSG.RankThree.PartTwo.Sec12.Hering129HNot9
public import CFSG.RankThree.PartTwo.Sec12.Hering129KY6
public import CFSG.RankThree.PartTwo.Sec12.Hering129List
public import CFSG.RankThree.PartTwo.Sec21.Item2110Res2ProofTwo
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

theorem false_of_cfg129_gTwo_R (h1 : Sec4.Item4_1LargePrime) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (hK : KFacts.KS12NormalizerMoves) (h125 : Item125BarC9)
    (hN9 : Item125BarNot9) (hCl : Gap129ClaimG2M) (hKK : Gap129KFK) (hKL : Gap129KFLieIn)
    (hNI : KFNonIsoG2D4) (hEE : Gap129EndE)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {b a : G}
    {K S : Subgroup G} (cfg : Cfg129 G A c L b a K S) (hG2' : GTwoType129 L K) : False := by
  have hSym := gap129SymG2In_of h45 h48 hKK hKL
  have hSymII := gap129SymII_of_in h1 h45 h48 hK h125 hCl hKK hKL hNI
  have hstd := cfg.std
  have hty := cfg.list
  obtain ⟨hbA, haA, haL, hb1, ha1, haB, hbL, hab, haD, hxD, hxb, hxL, hxB, hxA, hx1⟩ :=
    cfg.point_facts
  obtain ⟨q, hq⟩ := gTwoType129_iff.mp hG2'
  obtain ⟨Yd, hYd, hYdc, hYdty⟩ := hCl G A c L b a K S cfg q hq a haD hab
  have hcored := core129_of h45 hK hstd hty haA ha1 hYd hYdc
  obtain ⟨hcXa, -, hXqa⟩ := hKK G A c L b a K S cfg hG2' a haD hab
  have hXd := resCent_le_of_core h48 cfg haD hab hcXa hXqa hcored
  have hLieYd : HasLieParamInRange Yd ∧ (Typ129I K Yd ∨ Typ129IV q Yd) := by
    rcases hYdty with h1' | h2 | h4 | h3
    · exact ⟨hasLieParamInRange_of_typ129I h1 cfg hq h1', Or.inl h1'⟩
    · exact absurd h2 (hSymII G A c L b a K S cfg hG2' a haD hab haL Yd hcored)
    · exact ⟨hasLieParamInRange_of_typ129IV h4, Or.inr h4⟩
    · exact absurd h3 (gap129NotIiiLcMinus_of h45 h125 G A c L b a K S cfg hG2' a haD hab haL
        Yd hcored)
  obtain ⟨-, J, hJ, hbJ, hJiso1, hJiso2, -⟩ :=
    hSym G A c L b a K S cfg hG2' a haD hab Yd hcored hLieYd.1
  by_cases hmod : PiModNine q.card
  ·
    have hI : Typ129I K Yd := by
      rcases hLieYd.2 with hI | ⟨h45', -⟩
      · exact hI
      · exfalso
        unfold PiModNine at hmod
        omega
    exact Hering129G.false_of_two_slPi_mod_nine cfg.std.partTwoF_eq cfg.std.ne_one
      (cfg.std.isE27.1.2 c cfg.std.mem_A) cfg.std.mem_thetaComponentsAt hJ.1 (Ne.symm hJ.2.1)
      cfg.std.mem_L hJ.2.2.1 hq.1 (hJiso1 hI) hmod
  ·
    obtain ⟨r, hr, hrmod⟩ : ∃ r : TauCeti.PrimePower,
        Sec4.IsSLThreePiAt (J ⧸ aschbacherSolvableCore 3 J) r.card ∧ ¬ PiModNine r.card := by
      rcases hLieYd.2 with hI | ⟨-, r, hr45, -, hrG⟩
      · obtain ⟨e⟩ := hJiso1 hI
        exact ⟨q, isSLThreePiAt_congr e.symm hq.1, hmod⟩
      · refine ⟨r, hJiso2 r hrG, ?_⟩
        unfold PiModNine
        omega
    obtain ⟨Yx, hYx, hYxc, hYxty⟩ := hCl G A c L b a K S cfg q hq (a * b) hxD hxb
    have hcorex := core129_of h45 hK hstd hty hxA hx1 hYx hYxc
    obtain ⟨hcXx, -, hXqx⟩ := hKK G A c L b a K S cfg hG2' (a * b) hxD hxb
    have hXx := resCent_le_of_core h48 cfg hxD hxb hcXx hXqx hcorex
    have hIII : Typ129IIIcMinus A c L Yx (a * b) ∧ NoLieParamInRange Yx := by
      rcases hYxty with h1' | h2 | h4 | h3
      · exact absurd (hSym G A c L b a K S cfg hG2' (a * b) hxD hxb Yx hcorex
          (hasLieParamInRange_of_typ129I h1 cfg hq h1')).1 hxL
      · exact absurd (hSym G A c L b a K S cfg hG2' (a * b) hxD hxb Yx hcorex
          (hasLieParamInRange_of_typ129II h1 cfg h2)).1 hxL
      · exact absurd (hSym G A c L b a K S cfg hG2' (a * b) hxD hxb Yx hcorex
          (hasLieParamInRange_of_typ129IV h4)).1 hxL
      · exact ⟨h3, noLieParamInRange_iff.mpr fun hrange =>
          hxL (hSym G A c L b a K S cfg hG2' (a * b) hxD hxb Yx hcorex hrange).1⟩
    obtain ⟨hType, E, hE⟩ := typ129IIIcMinus_iff.mp hIII.1
    obtain ⟨F, hF27, hcF, hFL, hmove⟩ := hEE G A c L b a K S cfg q hq (a * b) hxD hxb hxL Yx
      hcorex hXx hIII.2 hType E hE a haD hab haL Yd J hcored hXd hJ hbJ r hr hrmod hmod
    exact hmove (hN9 G A c L hstd q.card hq.1 hmod F hF27 hFL hcF)

theorem item129BarList_of_steps_R (h1 : Sec4.Item4_1LargePrime) (h45 : Sec4.Item4_5)
    (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9) (hB3 : Sec6.BThreePropertyCentral)
    (hK : KFacts.KS12NormalizerMoves) (hHJF : HJBranchFalse) (h125 : Item125BarC9)
    (hN9 : Item125BarNot9) (hT : Gap127TwoCfg) (hCl : Gap129ClaimG2M) (hKK : Gap129KFK)
    (hKL : Gap129KFLieIn) (hNI : KFNonIsoG2D4) (hEE : Gap129EndE) : Item129BarList := by
  intro G _ _ A c L hstd hAE hty hAS
  obtain ⟨b, a, K, S, cfg⟩ := exists_cfg h45 h48 h49 hB3 hstd hAE hAS hty
  rcases hT G A c L b a K S cfg with hHJ' | hG2'
  · exact (hHJF G A c L b a K S cfg hHJ').elim
  · exact false_of_cfg129_gTwo_R h1 h45 h48 hK h125 hN9 hCl hKK hKL hNI hEE cfg hG2'

theorem item129Bar_of_steps_R (h122 : Item122Bar) (h1 : Sec4.Item4_1LargePrime)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : Sec6.BThreePropertyCentral) (hK : KFacts.KS12NormalizerMoves) (hHJF : HJBranchFalse)
    (h125 : Item125BarC9) (hN9 : Item125BarNot9) (hT : Gap127TwoCfg) (hCl : Gap129ClaimG2M)
    (hKK : Gap129KFK) (hKL : Gap129KFLieIn) (hNI : KFNonIsoG2D4) (hEE : Gap129EndE) :
    Sec21.Item129Bar :=
  fun G _ _ A c L hstd hAE hAS =>
    item129BarList_of_steps_R h1 h45 h48 h49 hB3 hK hHJF h125 hN9 hT hCl hKK hKL hNI hEE G A c L
      hstd hAE (h122 G A c L hstd hAE) hAS

theorem item129Bar_of_inputs_R
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3)
    (hcov : Sec4.Census.CoverInputs46)
    (hKC : KFacts.KS12CoverExclusion) (h128 : Item128BarAt) (hNF : KS128NotHJFree)
    (h422 : Sec4.Item4_22) (h423 : Sec4.Item4_23) (h424 : Sec4.Item4_24Used)
    (hN : Sec11.Item1134E27N) (hST : Sec21.Item1134E27ST)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) (h49 : Sec4.Item4_9)
    (hB3 : Sec6.BThreePropertyCentral) (hK : KFacts.KS12NormalizerMoves)
    (hK9 : KFacts.KS12OrderNine) (hG1 : Gap125NonCentralBar)
    (hTL : KS129ThreeLocalFix) (hT : Gap127TwoCfg) (hD4 : Gap127D4Even) (hOTwo : KS129OTwo)
    (hP8 : Hering129L.Psl28ProperSolvable) (hSp : Gap129YSporadic) (hG2R : Gap129YG2Range)
    (hPGL : KF_L3_PGL) (hL3Deg : Gap129HessL3Deg) (hHD4 : Gap129HessD4) (hEE : Gap129EndE) :
    Sec21.Item129Bar :=
  item129Bar_of_steps_R (item122Bar_of h1 h2 h43 hcov hKC) h1 h45 h48 h49 hB3 hK
    (hjBranchFalse_of h128 hNF h422 h423 hST h45 h48 Sec4.Sporadic.rank3II_4_15 hK)
    (item125BarC9_of h45 hK hK9 hG1) (item125BarNot9_of h45 hK hK9 hG1) hT
    (gap129ClaimG2M_ofX
      (gap129ClaimShapeX_of
        (gap129YShape_of h424 h45 hK hN hST hTL (gap127TwoCfgPlus_of hT hD4 hTL) hOTwo hP8 hSp
          hG2R ks129PGL3Shape_holds) h45 h48 hK
        (gap129KFKStrong_of_fix hTL (gap127TwoCfgPlus_of hT hD4 hTL)))
      (gap129ClaimEX_of_hess hN hST h1 hTL (gap127TwoCfgPlus_of hT hD4 hTL)
        (gap129HessL3_of_pgl hPGL hL3Deg) hHD4) h45 hK)
    (gap129KFK_of_fix hTL (gap127TwoCfgPlus_of hT hD4 hTL))
    (gap129KFLieIn_of
      (gap129KFLieP_of hTL hN hST (gap129KFKStrong_of_fix hTL (gap127TwoCfgPlus_of hT hD4 hTL))))
    kfNonIsoG2D4_holds hEE

end CFSG.RankThree.PartTwo.Sec12
