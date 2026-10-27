module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoNormal
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoRanks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoOpp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThirtyTwoNOne
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4RootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4RankBounds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4CartanRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoAutHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoBorelHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.ThreeD4TwoSevenNormalizerHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwoRootLine
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFive
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214g
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ui
public import CFSG.Quasithin.H13.NQCatExceptional
public import CFSG.LieType.Simplicity.TrialityD4
public import CFSG.HardMathSupport.Cooperstein.Proving.NineThreeTransfer
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16UnitCase
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6K35cRee
public import CFSG.Quasithin.Background.F918R7
public import CFSG.Quasithin.Background.SmithB42Vacuous
public import CFSG.Quasithin.H13.NQCatBNExc
public import CFSG.Quasithin.Recognition.CertTriality
public import CFSG.Quasithin.Recognition.CertTrialityCheckInputs
public import CFSG.Quasithin.Recognition.CertTrialityFaithful
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522D42Para
public import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
public import CFSG.Sporadic.J4.QT2LocOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

section CertifiedOdd


theorem v0_eq_bot_of_is3D4_odd (D : Data G) {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1 : R17_1At D V₀ V hV) (h891 : F08.R891 D) (hSg : UC6S846.SigmaStd D)
    (h76 : F07.R76 D) (h72 : F07.R72 D) (hK35 : UCK.K35w)
    (h13 : SigmaRankThree13 D) (h869 : F08.R869 D) (h109 : Inputs1719.UC2_10_9 D)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal)
    {n : ℕ} (h3D4 : Is3D4 (Bar2 L) n) (hodd : Odd n) (hn : 3 ≤ n) : V₀ = ⊥ := by
  classical
  have hk : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D (h891 L hL n h3D4)
  have hCE : CFSG.Blueprint.ChevalleyExceptionalModel (Bar2 L) .trialityD4 2 n :=
    ((CFSG.Blueprint.LieModel.chevalleyExceptional_iff (by decide)).1 h3D4).2
  have hsimple : IsSimpleGroup (Bar2 L) :=
    (CFSG.LieType.Simplicity.fam_3d4_simplicity (Bar2 L) 2 n hCE).2
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    @uc22p21k_center_eq_bot (Bar2 L) _ hsimple hL.2.2
  have hn1 : 1 ≤ n := h3D4.admissible.2.1
  have hOut : IsCyclic (Outer (Bar2 L)) :=
    CFSG.Quasithin.H13.NQCat.outer_isCyclic_of_even_trialityD4_model hn1 hCE
  obtain ⟨r, hr, hrd, hr7, hrn⟩ := exists_primitive_prime_of_odd hodd hn
  have hr2 : r ≠ 2 := by omega
  have hr3 : 3 < r := by omega
  have hr5 : 5 ≤ r := by omega
  have hout : ¬ r ∣ Nat.card (Outer (Bar2 L)) := by
    rw [Inputs1719.card_outer_of_is3D4 h3D4]
    exact hrn
  obtain ⟨R, hRL, hRT, hRel, hRcard⟩ :=
    exists_elemAbelian_le_normalizer_of_is3D4_odd D
      Inputs1719.k_3D4CartanRank_holds Inputs1719.k_3D4TwoAutInner_holds hL hN hZ h3D4
      hodd hr hr2 hrd
  have hnsp : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M :=
    not_isStronglyPEmbedded_of_le_normalizer h1 hk hr hr2 (hRL.trans hL.1.le) hRT hRel hRcard
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have hrsig : r ∉ D.sig := fun hrm => hnsp (UC6S846.sp_of_mem_sig hSg hns hrm)
  have hab : ∀ P : Sylow r (Bar2 L), IsMulCommutative (P : Subgroup (Bar2 L)) :=
    fun P => Inputs1719.isMulCommutative_sylow_of_is3D4 h3D4 hr hr5 hrd P
  have hΓ : ¬ rankThreeGamma 1 r R ≤ D.M :=
    not_rankThreeGamma_le_of_is3D4 h1 hk hL hN hr hr2 hab hout hRL hRT hRel hRcard
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hp', hp2⟩ := D.sig_prime p hp
  have hbar : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (⊤ : Subgroup (Bar2 L)) ≤ 2 :=
    fun q hq hq2 => Inputs1719.pRank_le_two_of_is3D4 h3D4 hq hq2
  obtain ⟨hp3, hpL, -⟩ :=
    pRank_eq_three_of_is3D4 hSg h76 hL hN hZ hOut hbar hr hr2 hrsig hRL hRel hRcard hΓ hp
  have hrM : CFSG.Open.pRank r D.M ≤ 2 :=
    pRank_le_two_of_not_mem_sig hSg h13 hp hp3 hr hr7 hrsig
  have hX : L = Opp r D.M :=
    eq_opp_of_is3D4 hL hN hsimple hr hr2 hout hRL hRel hRcard hrM
  have hbar2 : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) = 2 := by
    rw [UC22.pRank_bar2_eq_of_odd (Y := L) hp' hp2]
    exact hpL
  have h2b : p ∣ 2 ^ (6 * n) - 1 :=
    Inputs1719.dvd_two_pow_six_mul_sub_one_of_is3D4 h3D4 hp' hp2 (by omega)
  have hpn : p ∣ 2 ^ (2 * (3 * n)) - 1 := by
    simpa [show 2 * (3 * n) = 6 * n by omega] using h2b
  obtain ⟨B, hBR, hBcard, Yt, hYt, N₀, hN₀, hL2⟩ :=
    Inputs1719.exists_rootLine_lift_3D4 Inputs1719.k_3D4RootLine_holds h3D4 hr hr3 hrd
      hRL hRel hRcard
  have hRrank : CFSG.Open.pRank r R = 2 := by
    have h := CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hRel
    rw [hRcard] at h
    have h' := Nat.pow_right_injective hr.two_le h.symm
    omega
  have hrankE : 2 ≤ CFSG.Open.pRank r D.M := by
    have hmono : CFSG.Open.pRank r R ≤ CFSG.Open.pRank r D.M :=
      CFSG.SectionRank.pRank_mono hr.one_lt (hRL.trans hL.1.le)
    omega
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hSg hns hp
  have hOp : UC22.F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hp' hsp
  have h3 : 3 ≤ CFSG.Open.pRank p D.M := by omega
  have hn3 : 3 ≤ 3 * n := by omega
  obtain ⟨-, hBmem⟩ :=
    centralizer_le_and_mem_uniqueSet_of_rootLine_of_dvd h72 hK35 hp hsp h3 hOp hn3 hpn hZ
      hOut hr hr2 hX hpL hN₀ hL2 (hBR.trans hRL) hBcard hYt hrankE
  have hLM : L ≤ D.M := hL.1.le
  have hLN : D.M ≤ Subgroup.normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  have hnt : ¬ F08.Thin8 L := by
    intro hthin
    have hle : CFSG.Open.pRank r L ≤ 1 := hthin r hr hr2
    have hmono : CFSG.Open.pRank r R ≤ CFSG.Open.pRank r L :=
      CFSG.SectionRank.pRank_mono hr.one_lt hRL
    omega
  have hU0 : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uniqueMax_conjClosure_of_not_thin h869 hL hnt
  have hUL : UniqueMax D.M (L ⊔ D.T) := by
    rw [UC22.uc22p2214_conjClosure_eq_of_normal hLM hN] at hU0
    exact UC22.uc22p22u_uniqueMax_mono D le_sup_left (sup_le hLM D.sylowM.le) hU0
  have hBU : UC6.InU D.M B := inU_iff_mem_uniqueSet.2 hBmem
  exact v0_eq_bot_of_uc2_10_9_of_normal h109 hV hL hLN hUL (s := n) (p := r) hodd hr hrd
    (hBR.trans hRL) (hBR.trans hRT) hBcard hBU

end CertifiedOdd

section CertifiedAssembly


theorem seventeen_thirtytwo_holds (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h126 : R126 D) (h111 : W3Thm111 G)
    (h869 : F08.R869 D) (h127 : R127 D) (h640 : UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hMc3D4 : W4McClurg3D4) (h1 : R17_1At D V₀ V hV) (h891 : F08.R891 D)
    (hSg : UC6S846.SigmaStd D) (h76 : F07.R76 D) (h614 : UC6.R6_14 D) (h72 : F07.R72 D)
    (hK35 : UCK.K35w) (h13 : SigmaRankThree13 D)
    (h109 : Inputs1719.UC2_10_9 D) (h3D4N : Inputs1719.W4Lem4_17TrialityD4N) :
    R17_32At D V₀ V := by
  have hK3 : Inputs1719.K_BorelTorusAbelian := Inputs1719.k_BorelTorusAbelian_holds
  classical
  intro L hL n h3D4
  have hN : (L.subgroupOf D.M).Normal :=
    normal_of_is3D4 D hSg hK3 Inputs1719.k_3D4TwoSylowSeven_holds
      Inputs1719.k_3D4TwoBorel_holds hV h1 h891 hL h3D4
  have hodd : Odd n := by
    by_contra h
    exact seventeen_thirtytwo_n_even D hV h1 h891 Inputs1719.k_3D4CartanRank_holds hL hN h3D4 h
  have h0 : V₀ = ⊥ := by
    by_cases hn1 : n = 1
    · subst hn1
      exact v0_eq_bot_of_is3D4_one Inputs1719.k_3D4TwoThreeRank_holds
        Inputs1719.k_3D4TwoSylowSeven_holds Inputs1719.k_3D4TwoBorel_holds
        Inputs1719.k_3D4TwoSevenNormalizer_holds D hV hSg h76 h614 h869 h109 hL hN h3D4
    · have hn3 : 3 ≤ n := by
        obtain ⟨k, rfl⟩ := hodd
        omega
      exact v0_eq_bot_of_is3D4_odd D hV h1 h891 hSg h76 h72 hK35 h13 h869 h109 hL hN h3D4
        hodd hn3
  subst h0
  exact seventeen_thirtytwo_normal_v0eq1 D hx h61 h126 h111 h869 h127 h640 hFF hMc3D4 h891
    hV L hL hN n h3D4 hodd h3D4N

end CertifiedAssembly

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
