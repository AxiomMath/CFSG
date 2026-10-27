module

public import CFSG.LocalAnalysis.StandardType.GGResThreeSettledDefs
import CFSG.LocalAnalysis.StandardType.GGResThreeCensusLabel
public import CFSG.LocalAnalysis.StandardType.GGResNonsingF4Three
public import CFSG.LocalAnalysis.StandardType.GGResNonsingTwASplit
public import CFSG.LocalAnalysis.StandardType.GGTBJTwoNodeUnitarySixOriginal
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
import CFSG.LocalAnalysis.StandardType.GGHdRo7CFinal
import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
import CFSG.LocalAnalysis.StandardType.GGResSeven
import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeKacSingle
public import CFSG.LocalAnalysis.StandardType.GGKacTable
public import CFSG.LocalAnalysis.StandardType.GGKacK0
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeRowCover1585Holds
public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3Holds
public import CFSG.LocalAnalysis.StandardType.GGResJPairedBlock
public import CFSG.LocalAnalysis.StandardType.GGResLeviLE3Bridge
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsHolds
public import CFSG.LocalAnalysis.StandardType.GGResNonsingularBase
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
public import CFSG.LocalAnalysis.StandardType.GGDepED4ZKE6
public import CFSG.LocalAnalysis.StandardType.GGResCentBoundNbrHolds
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineTransfer
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.LocalAnalysis.StandardType.GGFrameTBSUDvd
public import CFSG.LocalAnalysis.StandardType.GGResJOneReflSylow
public import CFSG.LocalAnalysis.StandardType.GGResKLinTwoExact3
public import CFSG.LocalAnalysis.StandardType.GGResNonsingLinearNs
import CFSG.LocalAnalysis.StandardType.GGResKLinSplitExact3
public import CFSG.LocalAnalysis.StandardType.GGResJTwA5Sylow
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneOutdiagInputs
public import CFSG.LocalAnalysis.StandardType.GGAutomizerGammaCard

public import CFSG.LocalAnalysis.StandardType.GGResF4ExactTwo
public import CFSG.LocalAnalysis.StandardType.GGResExact2KReverse
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Holds
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
public import CFSG.RankThree.PartTwo.Census.Classical.EvenPrimes
public import CFSG.LocalAnalysis.StandardType.GGResUnitaryQPlusKProducers
public import CFSG.LocalAnalysis.StandardType.GGResLinTwoRankFiveSix
public import CFSG.LocalAnalysis.StandardType.GGResLinTwoRank78K3
public import CFSG.LocalAnalysis.StandardType.GGResLinTwoL3GammaGap
public import CFSG.LocalAnalysis.StandardType.GGResJTwE6Lagrange
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLineL2Cover

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGResHyp.residualLabel_L (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hN : ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs L)
    (hS : ¬ GGInnerDiagOnLabel ggThreeSettledLabelL p Bs L)
    (hsm : ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L)
    (hE6L : ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelL p Bs L) :
    GGInnerDiagOnLabel ggThreeResidualLabelL p Bs L := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hst : LargeEvenStandardType p B x L := hH.1.1.2.2.2.2.2.2.2
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hP⟩ := largeEvenMarking_exists_hasLabel hst.1
  have hall : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs L := by
    intro S hS'
    refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hH.2.2.1.1 hlab hhas)
    rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
    subst h1
    exact ⟨hS', h2, h3⟩
  rcases ggThreeCensus_label_L hp hp2 hlab hP.1 with h | h | h | h | h
  · exact absurd (hall _ h) hN
  · exact absurd (hall _ h) hS
  · exact absurd (hall _ h) hsm
  · exact absurd (hall _ h) hE6L
  · exact hall _ h

theorem GGResHyp.residualLabel_K (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hN : ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs K)
    (hS : ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K)
    (hE6 : ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelK p Bs K)
    (hL2 : ¬ GGInnerDiagOnLabel ggThreeSettledLinTwoLabelK p Bs K)
    (hLn : ¬ GGInnerDiagOnLabel ggThreeSettledLinNsLabelK p Bs K)
    (hLs : ¬ GGInnerDiagOnLabel ggThreeSettledLinSplitLabelK p Bs K) :
    GGInnerDiagOnLabel ggThreeResidualLabelK p Bs K := by
  have hp : p.Prime := hH.1.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hInnK : GGInnerDiagOn Bs K := hH.2.2.1.2 y K hH.2.2.2.2.1
  obtain ⟨lab, hlab, hhas, R, _, I, F, θ, hHalf⟩ :=
    largeEvenMarking_exists_hasLabel (ggNbr_halfSplit_of_hyp hraw hiso hH.1 hH.2.2.2.2.1 hInnK)
  have hall : ∀ S : ℕ → LargeEvenLabel → Prop, S p lab → GGInnerDiagOnLabel S p Bs K := by
    intro S hS'
    refine largeEvenMarking_mono ?_ (ggInnerDiagOn_relabel hRig hInnK hlab hhas)
    rintro lab' R' _ I' F' θ' ⟨h1, h2, h3⟩
    subst h1
    exact ⟨hS', h2, h3⟩
  rcases ggThreeCensus_label_K hp hp2 hlab hHalf with h | h | h | h | h | h | h
  · exact absurd (hall _ h) hN
  · exact absurd (hall _ h) hS
  · exact absurd (hall _ h) hE6
  · exact absurd (hall _ h) hL2
  · exact absurd (hall _ h) hLn
  · exact absurd (hall _ h) hLs
  · exact hall _ h

theorem ggResMultiNodeRestThreeSettledInput_of_census (hRig : GGLabelRigidInput)
    (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (h : GGResMultiNodeRestThreeCensusInput) : GGResMultiNodeRestThreeSettledInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hD, hM, hsmL, hK, hres, htwo, hC2, hSU2⟩
  refine h G p B Bs x L D J y K hH hF hS hE ⟨?_, hM, hsmL, hK, hres, htwo, hC2, hSU2⟩
  rcases hD with ⟨hDL, hnL, hE6L⟩ | ⟨hDK, hnK, hE6, hL2, hLn, hLs⟩
  · exact Or.inl ⟨hDL, hnL, hE6L, hH.residualLabel_L hRig hnL hM hsmL hE6L⟩
  · exact Or.inr ⟨hDK, hnK, hE6, hL2, hLn, hLs,
      hH.residualLabel_K hRig hraw hiso hnK hK hE6 hL2 hLn hLs⟩

theorem ggResMultiNodeRestThreeCensusInput_of_settled (h : GGResMultiNodeRestThreeSettledInput) :
    GGResMultiNodeRestThreeCensusInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hD, hrest⟩
  refine h G p B Bs x L D J y K hH hF hS hE ⟨?_, hrest⟩
  rcases hD with ⟨hDL, hnL, hE6L, -⟩ | ⟨hDK, hnK, hE6, hL2, hLn, hLs, -⟩
  · exact Or.inl ⟨hDL, hnL, hE6L⟩
  · exact Or.inr ⟨hDK, hnK, hE6, hL2, hLn, hLs⟩

section RelativeF4ActualSide


theorem ggRelativeF4_actual_side_card_and_rank [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hX : X = L ∨ X = K)
    (hMark : GGInnerDiagOnLabel S 3 Bs X)
    (hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
          KGA.GGF4AutOrderAt 3 R ∧ GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I)) :
    Nat.card ↥(ggAutomizer X Bs) = 1152 ∧ 5 ≤ LargeEvenTwoLocalRank 3 G := by
  classical
  obtain ⟨hKperf, labK, hlabK, hrawK⟩ := hMark
  have hrawK0 := hrawK
  obtain ⟨_, _, _, _, hq0⟩ := largeEvenRawDatum_exists hrawK
  obtain ⟨_, _, _, hPK0⟩ := hq0
  obtain ⟨hSK, _, _⟩ := hPK0
  have hAllK := hall labK hlabK hSK
  have hrawKAll := hAllK _ hrawK0
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hrawKAll
  obtain ⟨⟨hs, hna, θ, hPK⟩, hGuard⟩ := hq
  obtain ⟨hS0, hNK, hBsIK⟩ := hPK
  obtain ⟨hZ, hcp, hout, hAO, hLift, hWR⟩ := hGuard hs hna
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hNK hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hNK hBsIK hb
  have hTB : GGTorusTBGroup 3 4 R I X (ggQuotHom θ) (ggGamma X hNK).range := by
    rcases hX with rfl | rfl
    · exact ggTorusTBGroup_of_L hH.1 hKperf θ hNK hBI hLift
    · exact ggTorusTBGroup_of_nbr hH.1 hH.2.2.2.2.1 hKperf θ hNK hBI hLift
  have hord : Nat.card (ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
      (ggGamma X hNK).range) = 1152 :=
    ggPumpTwExc_transport hZ hout hAO (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hKperf (ggGamma X hNK).range hTB.2.2.2.1
      hTB.2.2.2.2.1 hTB.2.2.2.2.2.1
  have hZact : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    rcases hX with rfl | rfl
    · exact card_bstar_inf_center_le hH.1
    · exact ggNbr_card_center_le_of_centerPCyclic ggLabelCenterPCyclicInput_holds hH.1
        (hH.2.2.1.2 y X hH.2.2.2.2.1)
  have hW : ggAutomizer (MulAut.conj : ↥X →* MulAut ↥X).range
      (ggGamma X hNK).range ≤
      Subgroup.closure (ggTorusReflSet 3 (ggGamma X hNK).range) :=
    hWR X (ggQuotHom θ) (ggGamma X hNK).range hTB
  constructor
  · rw [card_ggAutomizer_eq_gamma_of_weylReflSet Nat.prime_three (by norm_num)
      hBs hSC hH.2.2.2.1 hNK hZact hW]
    exact hord
  · rcases hX with rfl | rfl
    · exact hH.succ_le_twoLocalRank_of_torusLift_L hKperf θ hLift
    · exact hH.succ_le_twoLocalRank_of_torusLift_K hKperf θ hLift

end RelativeF4ActualSide

section TwE6QPlusTyped

theorem ggResLeaf_twE6Plus_three_noLE6 :
    GGResLeaf fun _ _ _ p _ _ Bs _ L _ J _ K =>
      p = 3 ∧
      GGInnerDiagOnLabel (fun p lab => lab.tag = .twE6 ∧ p ∣ 2 ^ lab.n + 1) p Bs L ∧
      GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny ∧
      ¬ GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypLE6 ∧
      ¬ (GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
         GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny) ∧
      ¬ ggReservedRows p J L K ∧
      ¬ (GGResRowAt ggRowTwoNode p J L ∨ GGResRowAt ggRowTwoNode p J K) ∧
      ¬ (GGResRowAt ggRowCorank2C p J L ∨ GGResRowAt ggRowCorank2C p J K) ∧
      ¬ (GGResRowAt ggRowSUCorank2 p J L ∨ GGResRowAt ggRowSUCorank2 p J K) := by
  rintro G _ _ p B Bs x L D J y K hH _ _ _ _ ⟨hp3, hM, hD, hnD, -⟩
  subst hp3
  exact (hnD (hH.levi_typLE6_of_twE6_qplus_L hM hD)).elim

end TwE6QPlusTyped

section Settled


theorem GGResHyp.not_lineJDatum_A3_of_e6_K
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLine : GGResLineJDatum 3 Bs J .A3)
    (hK : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∨ lab.tag = .twE6) 3 Bs K) :
    False := by
  classical
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hnb : GGNbr 3 B x D J y K := hH.2.2.2.2.1
  obtain ⟨E, hE, hEelem, hEcard, -⟩ := hH.exists_coroot_subgroup_of_A3 hLine
  have hpJ : 3 ∣ Nat.card J := by
    have h3E : 3 ∣ Nat.card E := by rw [hEcard]; norm_num
    exact h3E.trans (Subgroup.card_dvd_of_le (hE.trans inf_le_right))
  have hLB : GGLBalanceInput :=
    ggLBalanceInput_of_catalogueSchreier
      CFSG.RankThree.PartOne.TCB.schreierFor_inCatalog_holds
  have hJK : J ≤ K := le_of_ggNbr hLB hcfg.1 hcfg.2.2 hpJ hnb
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSS hcfg.2.2 hnb hJK
  obtain ⟨labK, hΛK, hHasK, R0, _, I0, F0, θ0, hPK⟩ :=
    largeEvenMarking_exists_hasLabel hK
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hPK.2.1
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hxN : x ∈ Subgroup.normalizer (K : Set G) := hN hxBs
  let e : MulAut ↥K := K.normalizerMonoidHom ⟨x, hxN⟩
  have he3 : e ^ 3 = 1 := by
    dsimp only [e]
    rw [← map_pow]
    have h1 : (⟨x, hxN⟩ : ↥(Subgroup.normalizer (K : Set G))) ^ 3 = 1 :=
      Subtype.ext (by simpa using hcfg.tableB_facts.2.1.2 x hxBs)
    rw [h1, map_one]
  have hJcomp : IsComponentOf (J.subgroupOf K) (ggFixSub e) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  have hK0 : GGK0ExcB3 := GGK0ExcB3Prod.ggK0ExcB3_holds
  have htagExc : labK.tag = .E6 ∨ labK.tag = .twE6 ∨ labK.tag = .E7 ∨
      labK.tag = .E8 ∨ labK.tag = .F4 := by
    rcases hPK.1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  have hExcK : GGKacExcPair labK 3 :=
    ⟨Nat.prime_three, by norm_num, ltrcov_three_dvd labK.n, htagExc⟩
  have hK0comp := hK0 3 labK hΛK hExcK
  have hInnK : GGInnerDiagOn Bs K :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.2.1, hP.2.2⟩) hK
  obtain ⟨R, _, θ, I, F, hBsI, hK0P⟩ :=
    exists_innerDiagDatum_of_labelAll ggLabelRigidInput_holds hInnK hΛK hHasK hK0comp hN
  have hperfK : commutator ↥K = ⊤ := hInnK.1
  have hφe : ∃ φ ∈ I, ∀ l : ↥K, φ (ggQuotHom θ l) = ggQuotHom θ (e l) := by
    refine ⟨ggLAut K θ ⟨x, hxN⟩, hBsI x hxBs, fun l => ?_⟩
    rw [ggQuotHom_apply, ggQuotHom_apply]
    change ggLAut K θ ⟨x, hxN⟩ (θ (l : ↥K ⧸ Subgroup.center ↥K)) =
      θ ((K.normalizerMonoidHom ⟨x, hxN⟩ l : ↥K) : ↥K ⧸ Subgroup.center ↥K)
    exact ggLAut_apply K θ ⟨x, hxN⟩ l
  obtain ⟨Dk, hDvalid, hcompclause, -⟩ :=
    hK0P ↥K (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
      hperfK e he3 hφe
  obtain ⟨o, ho, hqs, hdvd, hoΛ, hHasO⟩ := hcompclause (J.subgroupOf K) hJcomp
  obtain ⟨labJ, hΛJ, hA3J, hHasJ⟩ :=
    ggResLineJLabelInput_A3 G 3 B Bs x L D J y K hH rfl hLine
  have hHasJ' : GGHasLabel labJ
      (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _
      (Subgroup.subgroupOfEquivOfLe hJK).symm (Subgroup.map_center_eq _)) hHasJ
  have hiso : GGLabelIso labJ o.lab :=
    ggLabelRigidInput_holds labJ o.lab
      (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K))
      hΛJ hoΛ hHasJ' hHasO
  have hA3o : ggResLineJLabel .A3 o.lab := ggResLineJLabel_of_iso hA3J hiso
  have hrank3 : o.lab.rank = 3 := by
    rcases hA3o with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> exact h
  have hneB2 : o.lab.tag ≠ .B2der := by
    intro hb
    have h0 : o.lab.rank = 0 := by
      have h := hoΛ.2
      rw [hb] at h
      exact h.1
    omega
  have hshapeRank : (ggKacShapeLabel labK.n o.lab).2.1 = 3 := by
    have hshape : ggKacShapeLabel labK.n o.lab =
        (o.lab.tag, o.lab.rank, o.lab.n / labK.n) := by
      cases h : o.lab.tag
      case B2der => exact (hneB2 h).elim
      all_goals simp [ggKacShapeLabel, h]
    rw [hshape]
    exact hrank3
  obtain ⟨T, tw, hTl, hDtab⟩ := hDvalid
  rcases hPK.1 with htag | htag
  · have hlabK : labK = ⟨.E6, 0, labK.n⟩ := by
      obtain ⟨t, r, en⟩ := labK
      have h1 : t = .E6 := by simpa using htag
      have h2 : r = 0 := by simpa [h1] using hΛK.2
      cases h1
      cases h2
      rfl
    have hsome : ((T, tw) : GGKacType × Bool) = (.E6, false) := by
      have h := hTl
      rw [hlabK] at h
      simp only [ggKacTypeOfLabel] at h
      exact Option.some.inj h.symm
    cases hsome
    exact ggKacTable_E6_normalized_rank_ne_three hΛK.1
      (ltrcov_three_dvd labK.n) hDtab ho hshapeRank
  · have hlabK : labK = ⟨.twE6, 0, labK.n⟩ := by
      obtain ⟨t, r, en⟩ := labK
      have h1 : t = .twE6 := by simpa using htag
      have h2 : r = 0 := by simpa [h1] using hΛK.2
      cases h1
      cases h2
      rfl
    have hsome : ((T, tw) : GGKacType × Bool) = (.E6, true) := by
      have h := hTl
      rw [hlabK] at h
      simp only [ggKacTypeOfLabel] at h
      exact Option.some.inj h.symm
    cases hsome
    exact ggKacTable_E6_normalized_rank_ne_three hΛK.1
      (ltrcov_three_dvd labK.n) hDtab ho hshapeRank

theorem GGResHyp.not_exactThree_of_splitE6_K
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs K)
    (hD : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) :
    False := by
  have hT : GGTBTorAll := ggTBTorAll_of_remaining trivial
  have hLift : GGTBTorLiftRows := ggTBTorLiftRows_holds
  have hKmono : GGInnerDiagOnLabel ggE6TorusLabel 3 Bs K :=
    GGInnerDiagOnLabel.mono_label (fun lab h => Or.inl h) hK
  have hD6 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypLE6 :=
    GGResHyp.levi_typLE6_of_e6Torus_K hT hLift hH hKmono hD
  have hLine : GGResLineJDatum 3 Bs J .A3 := e6_exactThree_GGResLineJDatum_A3 hD6
  exact GGResHyp.not_lineJDatum_A3_of_e6_K hH hLine
    (GGInnerDiagOnLabel.mono_label (fun lab h => Or.inl h.1) hK)

theorem GGResHyp.not_exactThree_of_twE6_qplus_K
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs K)
    (hD : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) :
    False := by
  classical
  obtain ⟨labK, hΛK, hHasK, R0, _, I0, F0, θ0, hPK⟩ :=
    largeEvenMarking_exists_hasLabel hK
  have hN : Bs ≤ Subgroup.normalizer (K : Set G) := hPK.2.1
  have hbad : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs K :=
    largeEvenMarking_mono (fun lab _ _ I _ θ hP => by
      obtain ⟨t, r, n⟩ := lab
      obtain ⟨rfl, hdvd⟩ := hP.1
      exact ⟨⟨rfl, rfl, hdvd⟩,
        Or.inr (Or.inl ⟨by simp [LargeEvenUntwisted], by simp, hdvd⟩),
        hP.2.1, hP.2.2⟩) hK
  have hsc : GGTorusSelfCent 3 (ggGamma K hN).range :=
    ggTorusSelfCent_ggGamma hN hH.1.2.1.2.2.2
  have hcard5 : 3 ^ 5 ≤ Nat.card (ggGamma K hN).range :=
    ggTwE6ThreeNbrRankInput_holds G 3 B Bs x L D J hH.1 rfl y K hH.2.2.2.2.1 hbad hN hsc
  have hlabel : GGE6DepLabel labK := Or.inr ⟨hPK.1.1, hPK.1.2⟩
  obtain ⟨eK, -⟩ :=
    hH.weylOfType_E6_of_card_gamma_five ggLabelRigidInput_holds hΛK hHasK hlabel hN hcard5
  have hcard : Nat.card (ggAutomizer K Bs) = 51840 := by
    calc Nat.card (ggAutomizer K Bs) = Nat.card (CoxeterMatrix.E₆).Group :=
      (Nat.card_congr eK.toEquiv).symm
      _ = 51840 := l05nQW_ord_coxeterE6
  have hD6 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypLE6 :=
    hD.typLE6_of_card hcard
  have hLine : GGResLineJDatum 3 Bs J .A3 := e6_exactThree_GGResLineJDatum_A3 hD6
  exact GGResHyp.not_lineJDatum_A3_of_e6_K hH hLine
    (GGInnerDiagOnLabel.mono_label (fun lab h => Or.inr h.1) hK)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private abbrev ggRelativeF4KFacts : LargeEvenRawCont :=
  fun R _ I _ =>
    Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
      KGA.GGF4AutOrderAt 3 R ∧ GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I

theorem GGResHyp.false_of_automizer_J_eq_zpowers_of_twoLocalRank [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hm : 5 ≤ LargeEvenTwoLocalRank 3 G)
    {τ : MulAut ↥Bs} (hτ : GGIsReflection 3 τ)
    (hAJ : ggAutomizer J Bs = Subgroup.zpowers τ) : False := by
  classical
  have h27 : 3 ^ 3 ≤ Nat.card (ggGamma J hH.Bs_le_normalizer_J).range :=
    hH.pow_three_le_card_gamma_J_of_twoLocalRank hm
  obtain ⟨labJ, -, -, hInnerJ⟩ := hH.exists_J_marking
  have hCombJ :=
    largeEvenMarking_and_labelAll_simple
      (S := fun lab => lab = labJ)
      (P' := fun R _ I _ => GGOutdiagCyclic R I)
      (fun lab hlab _ => largeEvenLabelAll_outdiag_simple hlab)
      (fun _ _ _ _ _ _ hP => hP.1) hInnerJ
  obtain ⟨hJperf, labJ', hlabJ', hrawJ'⟩ := hCombJ
  obtain ⟨RJ, _, IJ, FJ, hsJ, hnaJ, θJ, hPmarkJ, houtJc⟩ :=
    largeEvenRawDatum_exists hrawJ'
  obtain ⟨-, hNJ, hBsIJ⟩ := hPmarkJ
  have hBsJ : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSCJ : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBIJ : ∀ (b : G) (hb : b ∈ Bs), ggLAut J θJ ⟨b, hNJ hb⟩ ∈ IJ :=
    fun b hb => ggLAut_mem_of_induces J θJ hNJ hBsIJ hb
  have hTBJ : GGTorusTBGroup 3 3 RJ IJ J (ggQuotHom θJ) (ggGamma J hNJ).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBsJ hSCJ hJperf θJ hNJ hBIJ h27 h27
  obtain ⟨SJ, hSJp, hSJnc⟩ :=
    FrameRoute.exists_noncyclic_three_of_outdiagCyclic houtJc (ggQuotHom_surjective θJ)
      (by rw [ker_ggQuotHom]) hJperf hTBJ.2.2.2.1 hTBJ.2.2.2.2.1 h27
  have hSmapP : IsPGroup 3 (SJ.map J.subtype) := hSJp.map J.subtype
  have hSmapJ : SJ.map J.subtype ≤ J := Subgroup.map_subtype_le SJ
  have hcyc : IsCyclic (SJ.map J.subtype) :=
    hH.isCyclic_of_le_J_of_oneRefl hτ hAJ hSmapP hSmapJ
  exact hSJnc ((Subgroup.equivMapOfInjective SJ J.subtype J.subtype_injective).isCyclic.mpr hcyc)

private theorem ggRelativeF4_exactThree_side_false [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X Y : Subgroup G}
    {S : ℕ → LargeEvenLabel → Prop}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hX : X = L ∨ X = K)
    (hMark : GGInnerDiagOnLabel S 3 Bs X)
    (hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard ggRelativeF4KFacts))
    (hD : GGResLeviDatumExact3 3 Bs X J Y ggSelAny ggTypAny) : False := by
  classical
  obtain ⟨hcardK, hm⟩ := ggRelativeF4_actual_side_card_and_rank hH hX hMark hall
  obtain ⟨Λ, i1, i2, Sdel, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS3, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpairL, hpairK, hsel,
    ⟨fL, hfL⟩, ⟨fK, hfK⟩, hclosL, hclosK, hdel, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  have hcardML : Nat.card ML.Group = 1152 := by
    rw [Nat.card_congr fL.toEquiv]
    exact hcardK
  have hWML : GGWeylTypeData (Fintype.card Λ) 1152
      (Nat.card ↥(Subgroup.center ML.Group)) := by
    simpa [hcardML] using ggWeylTypeData_of_isWeylMatrix hML
  have hF4 : GGWeylTypeData 4 1152 2 :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl ⟨rfl, by norm_num, by norm_num⟩))))))
  have hrank : Fintype.card Λ = 4 := ggWeylTypeData_rank_eq hWML hF4
  have hcompl : Fintype.card {i : Λ // i ∉ Sdel} = 1 := by
    rw [Fintype.card_subtype_compl, Fintype.card_coe, hrank, hS3]
  obtain ⟨j⟩ := Fintype.card_pos_iff.mp
    (by omega : 0 < Fintype.card {i : Λ // i ∉ Sdel})
  have hmemJ : φ (Sum.inl j) ∈ ggAutomizer J Bs := by
    rw [hclosJ]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hneJ : φ (Sum.inl j) ≠ 1 := (hrefl (Sum.inl j)).ne_one Nat.prime_three
  have hAJne : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    exact hneJ (Subgroup.mem_bot.mp (by simpa [hbot] using hmemJ))
  rcases ggAutomizer_eq_bot_or_zpowers_of_card_le_four φ hS3
      (by omega : Fintype.card Λ ≤ 4) hrefl hclosJ with hbot | ⟨τ, hτ, hAJ⟩
  · exact (hAJne hbot).elim
  exact hH.false_of_automizer_J_eq_zpowers_of_twoLocalRank hm hτ hAJ

theorem GGResHyp.not_exactThree_of_twE6_qminus_K [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs K)
    (hD : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) : False :=
  ggRelativeF4_exactThree_side_false hH (Or.inr rfl) hK
    (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_twE6Dvd hlab hs) hD

theorem GGResHyp.not_exactThree_of_splitE6_qplus_K [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hK : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs K)
    (hD : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) : False :=
  ggRelativeF4_exactThree_side_false hH (Or.inr rfl) hK
    (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_E6Plus hlab hs) hD

theorem GGResHyp.not_exactThree_of_splitE6_qplus_L [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hD : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny) : False :=
  ggRelativeF4_exactThree_side_false hH (Or.inl rfl) hL
    (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_E6Plus hlab hs) hD

theorem GGResHyp.card_automizer_L_and_twoLocalRank_of_splitE6_qplus [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L) :
    Nat.card ↥(ggAutomizer L Bs) = 1152 ∧ 5 ≤ LargeEvenTwoLocalRank 3 G :=
  ggRelativeF4_actual_side_card_and_rank hH (Or.inl rfl) hL
    (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_E6Plus hlab hs)

theorem GGResHyp.not_exactThree_of_twE6_qminus_L [Fact (Nat.Prime 3)]
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs L)
    (hD : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny) : False :=
  ggRelativeF4_exactThree_side_false hH (Or.inl rfl) hL
    (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_twE6Dvd hlab hs) hD

theorem GGResHyp.not_exactThree_of_splitE6_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs L)
    (hD : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny) :
    False := by
  have hD6 : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypLE6 :=
    hH.levi_typLE6_of_e6Torus_L (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds
      (GGInnerDiagOnLabel.mono_label (fun lab h => Or.inl h) hL) hD
  exact hH.not_e6_exactThree_either_of_splitE6_L hL (Or.inl hD6)

theorem GGResHyp.not_exactThree_of_twE6_qplus_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    [Fact (Nat.Prime 3)]
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hD : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny) :
    False := by
  exact hH.not_e6_exactThree_either_of_e6_L
    (GGInnerDiagOnLabel.mono_label (fun _ h => Or.inr h) hL)
    (Or.inl (hH.levi_typLE6_of_twE6_qplus_L hL hD))

theorem ggResMultiNodeRestThreeSingularInput_of_settled
    (hT : GGTBTorAll)
    (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown) (hRig : GGLabelRigidInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hQ1 : GGBstarInnerDiagJInput)
    (h : GGResMultiNodeRestThreeSettledInput) : GGResMultiNodeRestThreeSingularInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hD, hres, htwo, hC2, hSU2⟩
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hD3 : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∨
      GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny :=
    hD.imp And.left And.left
  have hsm : ∀ {X : Subgroup G}, GGInnerDiagOnLabel ggThreeSmallLabel p Bs X →
      (∀ {S : ℕ → LargeEvenLabel → Prop}, GGInnerDiagOnLabel S p Bs X →
        StandardType.LargeEvenMarking ↥X (fun lab R _ I _ _ => S p lab ∧
          ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian p E ∧
            p ^ 3 ≤ Nat.card E)) → False := by
    intro X hM hrk
    rcases GGInnerDiagOnLabel.elim_or (S := GGRootGenSmallRankLabel)
        (T := fun p lab => (GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab) ∨
          StdSubRestThree.GGTwoThreeSmallLabel p lab ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
        hM with h1 | hM
    · exact not_largeEvenMarking_smallRank hp hp2 (hrk h1)
    rcases GGInnerDiagOnLabel.elim_or
        (S := fun p lab => GGRootGenSmallExcLabel p lab ∧ GGRootGenOpenLabel p lab)
        (T := fun p lab => StdSubRestThree.GGTwoThreeSmallLabel p lab ∨ lab.tag = .G2der ∨
          lab.tag = .twF4der) hM with h1 | hM
    · exact not_largeEvenMarking_smallExc hp hp2 (hrk h1)
    rcases GGInnerDiagOnLabel.elim_or (S := StdSubRestThree.GGTwoThreeSmallLabel)
        (T := fun _ lab => lab.tag = .G2der ∨ lab.tag = .twF4der) hM with h1 | hM
    · exact ggInndiag_pRank_le_two_twoThreeSmall (hrk h1)
    rcases GGInnerDiagOnLabel.elim_or (S := fun _ lab => lab.tag = .G2der)
        (T := fun _ lab => lab.tag = .twF4der) hM with h1 | h1
    · exact ggInndiag_pRank_le_two_G2der hp hp2 (hrk h1)
    · exact ggInndiag_pRank_le_two_twF4der hp hp2 (hrk h1)
  have hsmL : ¬ GGInnerDiagOnLabel ggThreeSmallLabel p Bs L := fun hM =>
    hsm hM (fun h => ggInnerDiagOnLabel_L_pRank_ge_three hH.1 h)
  have hK : ¬ GGInnerDiagOnLabel ggThreeSettledLabelK p Bs K := fun hM => by
    rcases GGInnerDiagOnLabel.elim_or (S := ggThreeSmallLabel)
        (T := fun p lab => p = 7 ∧
          ((lab.tag = .A ∧ lab.rank = 8 ∧ lab.n = 1) ∨ (lab.tag = .E6 ∧ lab.n = 1))) hM with
      hM | hM
    · exact hsm hM (fun h => ggInnerDiagOnLabel_nbr_pRank_ge_three hH.1 hH.2.2.2.2.1 h)
    ·
      obtain ⟨-, ⟨t, r, n⟩, hΛ, hraw⟩ := hM
      obtain ⟨R, _, I, F, -, -, θ, ⟨hp7, hlab⟩, -⟩ := largeEvenRawDatum_exists hraw
      have has : GGHasLabel ⟨t, r, n⟩ (↥K ⧸ Subgroup.center ↥K) := by
        unfold GGHasLabel
        refine largeEvenRawDatum_mono ?_ hraw
        rintro R _ I F ⟨-, -, θ, -⟩
        exact ⟨θ⟩
      dsimp only at hlab
      subst hp7
      refine ggSeven_K_absurd_of_leviLE3 hH ?_ (hD3.imp
        (fun h => (ggResLeviDatumLE3_iff_exact2_or_exact3 7 Bs L J K _ _).mpr (Or.inr h))
        (fun h => (ggResLeviDatumLE3_iff_exact2_or_exact3 7 Bs K J L _ _).mpr (Or.inr h)))
      rcases hlab with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact Or.inl has
      · obtain rfl : r = 0 := hΛ.2
        exact Or.inr has
  by_cases hM : GGInnerDiagOnLabel ggThreeSettledLabelL p Bs L
  · rcases GGInnerDiagOnLabel.elim_or (S := fun p lab => lab.tag = .A ∧ p ∣ 2 ^ lab.n - 1)
        (T := fun p lab => (lab.tag = .twA ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1) ∨
          (p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank)) hM with hA | hM
    · exact (ggResExactThree_absurd_of_typeA_split_L_marking hH hA hD3).elim
    · rcases GGInnerDiagOnLabel.elim_or
          (S := fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1)
          (T := fun p lab => p = 3 ∧ (lab.tag = .B ∨ lab.tag = .C) ∧ lab.n = 1 ∧ 5 ≤ lab.rank)
          hM with hU | hSp
      · exact (hH.not_exactThree_either_of_unitary_L_allfields hU (fun h => htwo (Or.inl h))
          (fun h => hSU2 (Or.inl h)) (fun h => hres (Or.inl h)) hD3).elim
      · exact HdRo7C.ggResLeviExact3_join_of_sp_innerDiag hH hSp hD3
  ·
    have hJ : GGInnerDiagOnLabel (fun _ _ => True) p Bs J :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩)
        (hQ1 G p B Bs x L D J hH.1 hH.2.2.1.1)
    have hNL : GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny →
        ¬ GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
          p Bs L → ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs L := fun hDL hn hX => by
      rcases GGInnerDiagOnLabel.elim_or
          (S := fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
          (T := fun p lab => GGF4ThreeLabel p lab ∨ GGTwASplitLabel p lab) hX with hX | hX
      · exact hn hX
      rcases GGInnerDiagOnLabel.elim_or (S := GGF4ThreeLabel) (T := GGTwASplitLabel) hX with
        hX | hX
      · exact ggResExact3_false_of_f4Three_L hT hLift hTCJ hRig hP hH hJ hX hDL
      · exact ggResExact3_false_of_twASplit_L hT hLift hTCJ hRig hP hH hJ hX hDL
    have hNK : GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny →
        ¬ GGInnerDiagOnLabel (fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
          p Bs K → ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs K := fun hDK hn hX => by
      rcases GGInnerDiagOnLabel.elim_or
          (S := fun p lab => GGTBTorCov p lab ∧ ¬ ggSingularBaseLabel p lab)
          (T := fun p lab => GGF4ThreeLabel p lab ∨ GGTwASplitLabel p lab) hX with hX | hX
      · exact hn hX
      rcases GGInnerDiagOnLabel.elim_or (S := GGF4ThreeLabel) (T := GGTwASplitLabel) hX with
        hX | hX
      · exact ggResExact3_false_of_f4Three_K hT hLift hTCJ hRig hLB hP
          ggLabelCenterPCyclicInput_holds hH hJ hX hDK
      · exact ggResExact3_false_of_twASplit_K hT hLift hTCJ hRig hLB hP
          ggLabelCenterPCyclicInput_holds hH hJ hX hDK
    have hDs : ((GGResLeviDatumExact3 p Bs L J K ggSelAny ggTypAny ∧
        ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs L ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelL p Bs L) ∨
      (GGResLeviDatumExact3 p Bs K J L ggSelAny ggTypAny ∧
        ¬ GGInnerDiagOnLabel ggThreeNonsingBaseLabel p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledE6LabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinTwoLabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinNsLabelK p Bs K ∧
        ¬ GGInnerDiagOnLabel ggThreeSettledLinSplitLabelK p Bs K)) := by
      rcases hD with ⟨hDL, hresL⟩ | ⟨hDK, hresK⟩
      · refine Or.inl ⟨hDL, hNL hDL hresL, fun hE6 => ?_⟩
        obtain ⟨_, -, -, _, _, _, _, _, hPE⟩ := largeEvenMarking_exists_hasLabel hE6
        obtain rfl : p = 3 := hPE.1.1
        rcases GGInnerDiagOnLabel.elim_or
            (S := fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1)
            (T := fun _ lab => (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
              (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨ (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1))
            (GGInnerDiagOnLabel.mono_label (fun _ h => h.2) hE6) with hE | hE6
        ·
          exact hH.not_exactThree_of_splitE6_L hE hDL
        rcases GGInnerDiagOnLabel.elim_or
            (S := fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
            (T := fun _ lab => (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
              (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1)) hE6 with hE | hE6
        ·
          exact hH.not_exactThree_of_twE6_qplus_L hE hDL
        rcases GGInnerDiagOnLabel.elim_or
            (S := fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)
            (T := fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) hE6 with hE | hE
        ·
          exact hH.not_exactThree_of_twE6_qminus_L hE hDL
        · exact hH.not_exactThree_of_splitE6_qplus_L hE hDL
      · by_cases hKs : GGInnerDiagOnLabel ggThreeSettledE6LabelK p Bs K
        · exfalso
          by_cases hp3 : p = 3
          · subst hp3
            have hKs' : GGInnerDiagOnLabel (fun _ lab =>
                (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
                  (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
                  (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
                  (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1)) 3 Bs K :=
              GGInnerDiagOnLabel.mono_label (fun lab h => h.2) hKs
            rcases GGInnerDiagOnLabel.elim_or
              (S := fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1)
              (T := fun _ lab => (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
                (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
                (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1)) hKs' with hE | hRest
            · exact GGResHyp.not_exactThree_of_splitE6_K hH hE hDK
            · rcases GGInnerDiagOnLabel.elim_or
                (S := fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1)
                (T := fun _ lab => (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) ∨
                  (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1)) hRest with hT | hRest2
              · exact GGResHyp.not_exactThree_of_twE6_qplus_K hH hT hDK
              · rcases GGInnerDiagOnLabel.elim_or
                  (S := fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)
                  (T := fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1)
                  hRest2 with hTm | hTp
                · exact GGResHyp.not_exactThree_of_twE6_qminus_K hH hTm hDK
                · exact GGResHyp.not_exactThree_of_splitE6_qplus_K hH hTp hDK
          · obtain ⟨lab, -, -, R, _hR, I, F, θ, hP⟩ :=
              largeEvenMarking_exists_hasLabel hKs
            exact hp3 hP.1.1
        ·
          refine Or.inr ⟨hDK, hNK hDK hresK, hKs, fun hKl => ?_, fun hKn => ?_,
            fun hKs2 => hH.not_exactThree_K_of_linear_split_K hLB hKs2 hDK⟩
          ·
            obtain ⟨_, -, -, _, _, _, _, _, hP⟩ := largeEvenMarking_exists_hasLabel hKl
            exact hH.false_of_exact3_K_linTwo hP.1.1
              (GGInnerDiagOnLabel.mono_label (fun _ h => h.2) hKl) hDK
          ·
            exact ggResExact3_false_of_linearNs_K hT hLift hTCJ hRig hLB hP
              ggLabelCenterPCyclicInput_holds hH hJ (fun _ h => h) hKn hDK
    exact h G p B Bs x L D J y K hH hF hS hE ⟨hDs, hM, hsmL, hK, hres, htwo, hC2, hSU2⟩

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial LineU

theorem GGResHyp.not_exactThree_K_of_unitaryModel_of_automizerL_card_E6
    {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F]
    {n d : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {ψ : ↥(unitarySU 2 n F d) →* ↥K} (hM : UnitTB.Model ψ)
    (hpq : 3 ∣ 2 ^ n + 1) (hd : 5 ≤ d)
    (hdiag : ∀ a ∈ (ggGamma K (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer).range,
      ∃ t : Fin d → F, ActsDiagU ψ a t)
    (hAL : Nat.card (ggAutomizer L Bs) = 51840) :
    ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by
  intro h3
  have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
  obtain ⟨r, hdegree, hpd, _, _, _, _, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq hd hdiag h3
  have hdiv : 3 ∣ r + 1 := by simpa [hdegree] using hpd
  have hr5 : 5 ≤ r := by
    by_contra h
    have hr4 : r = 4 := by omega
    norm_num [hr4] at hdiv
  have hJ : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card (ggAutomizer J Bs) = 1 := by simp [hbot]
    have h6 : 6 ≤ (r - 2).factorial := by
      calc 6 = Nat.factorial 3 := by norm_num
           _ ≤ (r - 2).factorial := Nat.factorial_le (by omega)
    omega
  have hJA : GGWeylTypeData (r - 3) (Nat.card (ggAutomizer J Bs)) 1 := by
    refine Or.inl ⟨by omega, ?_, ?_⟩
    · rw [hAJ]
      congr 1
      omega
    · simp [show r - 3 ≠ 1 by omega]
  have hLE : GGWeylTypeData 6 (Nat.card (ggAutomizer L Bs)) 1 := by
    rw [hAL]
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)))
  have hfalse : ∀ k, 2 ≤ k → k ≤ 3 →
      GGResLeviDatumCard k 3 Bs L J K ggSelAny ggTypAny → False := by
    intro k hk2 hk3 hLk
    obtain ⟨rJ, hrJ, hJW⟩ := ggResLeviDatumCard_rank_eq_of_weylTypeData hLk hJ hLE
    have hJr := ggWeylTypeData_rank_eq hJW hJA
    rcases (by omega : r = 6 ∨ r = 7) with hr | hr
    · norm_num [hr] at hdiv
    · norm_num [hr] at hdiv
  rcases ggResExact3_K_reverse_or_exact2_singular ggTBFixInput_holds hH h3 with
    hL3 | ⟨hL2, -⟩
  · exact hfalse 3 (by norm_num) (by norm_num) hL3
  · exact hfalse 2 (by norm_num) (by norm_num) hL2

theorem GGResHyp.not_exactThree_K_of_twE6_qplus_L_qGeFour
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        3 ∣ 2 ^ lab.n + 1) 3 Bs K) :
    ¬ GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny := by
  have hN := (hH.2.2.1.2 y K hH.2.2.2.2.1).le_normalizer
  obtain ⟨F, hField, hFinite, n, d, θ, ψ, hn2, hd5, hpq, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_label_qGeFour hU hN
  letI : Field F := hField
  letI : Finite F := hFinite
  obtain ⟨e, -⟩ := ggTwE6Bad_weylOfType hH
    (GGInnerDiagOnLabel.mono_label (fun _ h => ⟨h.1, rfl, h.2⟩) hL)
  have hAL : Nat.card (ggAutomizer L Bs) = 51840 :=
    (Nat.card_congr e.toEquiv).symm.trans l05nQW_ord_coxeterE6
  exact hH.not_exactThree_K_of_unitaryModel_of_automizerL_card_E6 hM hpq hd5 hdiag hAL

theorem GGResHyp.relativeF4_K3_classification_of_L2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL2 : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny)
    (hAL : Nat.card ↥(ggAutomizer L Bs) = 1152)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        3 ∣ 2 ^ lab.n + 1) 3 Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (h3 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n rank d : ℕ)
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F d))
      (ψ : ↥(unitarySU 2 n F d) →* ↥K),
      rank = 5 ∧ d = 6 ∧ 2 ≤ n ∧ Odd n ∧ 3 ≤ n ∧ Nat.card F = (2 ^ n) ^ 2 ∧
        Nat.card Bs = 3 ^ 5 ∧ Nat.card ↥(ggAutomizer J Bs) = 6 ∧
        GGWeylTypeData 2 6 1 ∧
        GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny := by
  obtain ⟨F, hField, hFinite, n, rank, d, θ, ψ,
    hr4, hn2, hd5, hd_eq, hFK, hpq, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_label_qGeFour_literal hU hN
  letI : Field F := hField
  letI : Finite F := hFinite
  have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
  obtain ⟨r, hdr, hpd, hXD, hcardBs, hcent, hBlt, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq hd5 hdiag h3
  have hr4 : 4 ≤ r := by omega
  have hJ : ggAutomizer J Bs ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(ggAutomizer J Bs) = 1 := by
      simp [hbot]
    have hfac : 2 ≤ (r - 2).factorial := by
      have hle : (2 : ℕ).factorial ≤ (r - 2).factorial :=
        Nat.factorial_le (show 2 ≤ r - 2 by omega)
      simpa using hle
    have hAJ' : Nat.card ↥(ggAutomizer J Bs) = (r - 2).factorial := hAJ
    omega
  have hAJle : Nat.card ↥(ggAutomizer J Bs) ≤ 12 :=
    ggResF4_exactTwo_parabolic_card_le_twelve hL2 hJ hAL
  have hfac_le : (r - 2).factorial ≤ 12 := by simpa [hAJ] using hAJle
  have hrle : r ≤ 5 := by
    by_contra h
    have hr6 : 6 ≤ r := by omega
    have hfac : (4 : ℕ).factorial ≤ (r - 2).factorial :=
      Nat.factorial_le (show 4 ≤ r - 2 by omega)
    norm_num at hfac
    omega
  have hpd' : 3 ∣ r + 1 := by simpa [hdr] using hpd
  have hr5 : r = 5 := by
    interval_cases r <;> norm_num at hpd'
    rfl
  have hd6 : d = 6 := by omega
  have hrank5 : rank = 5 := by omega
  have hAJ6 : Nat.card ↥(ggAutomizer J Bs) = 6 := by
    rw [hAJ, hr5]
    norm_num
  have hBs5 : Nat.card Bs = 3 ^ 5 := by simpa [hr5] using hcardBs
  have hsurv6 : GGWeylTypeData 2 6 1 := by
    have hdataF4 : GGWeylTypeData 4 1152 2 :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inl ⟨rfl, by norm_num, by norm_num⟩))))))
    have hdataF4' : GGWeylTypeData 4 (Nat.card ↥(ggAutomizer L Bs)) 2 := by
      simpa [hAL] using hdataF4
    obtain ⟨rJ, hrJ, hsurv⟩ :=
      ggResLeviDatumCard_rank_eq_of_weylTypeData hL2 hJ hdataF4'
    have hrJ2 : rJ = 2 := by omega
    have hsurv' : GGWeylTypeData 2 6
        (Nat.card ↥(Subgroup.center ↥(ggAutomizer J Bs))) := by
      simpa [hrJ2, hAJ6] using hsurv
    rcases hsurv' with hA | hB | hD | hE6 | hE7 | hE8 | hF4 | hG2
    · exact Or.inl ⟨by norm_num, by norm_num, by norm_num⟩
    · norm_num at hB
    · omega
    · omega
    · omega
    · omega
    · omega
    · omega
  have hodd : Odd n :=
    CFSG.RankThree.PartTwo.Census.odd_of_three_dvd_two_pow_add_one hpq
  have hn3 : 3 ≤ n := by
    rcases hodd with ⟨k, hk⟩
    omega
  exact ⟨F, hField, hFinite, n, rank, d, θ, ψ,
    hrank5, hd6, hn2, hodd, hn3, hFK, hBs5, hAJ6, hsurv6, hL2⟩


theorem GGResHyp.relativeF4_K3_actual_models_of_L2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL2 : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny)
    (hAL : Nat.card ↥(ggAutomizer L Bs) = 1152)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        3 ∣ 2 ^ lab.n + 1) 3 Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (h3 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n : ℕ)
      (ψ : ↥(unitarySU 2 n F 6) →* ↥K) (δ : ↥(unitarySU 2 n F 3) →* ↥J),
      Nat.card F = (2 ^ n) ^ 2 ∧ Odd n ∧ 3 ≤ n ∧ UnitTB.Model ψ ∧ UnitTB.Model δ ∧
        (∀ a ∈ (ggGamma K hN).range, ∃ t : Fin 6 → F, ActsDiagU ψ a t) ∧
        (∀ a ∈ (ggGamma J hH.Bs_le_normalizer_J).range,
          ∃ t : Fin 3 → F, ActsDiagU δ a t) := by
  obtain ⟨F₀, _, _, n₀, rank₀, d₀, θ₀, ψ₀, _, _, _, _, _, _, _, hAJsix, _⟩ :=
    hH.relativeF4_K3_classification_of_L2 hL2 hAL hU hN h3
  obtain ⟨F, hField, hFinite, n, rank, d, θ, ψ,
    hr4, hn2, hd5, hd_eq, hFK, hpq, hM, hdiag⟩ :=
    hH.exists_unitaryModel_K_of_label_qGeFour_literal hU hN
  letI : Field F := hField
  letI : Finite F := hFinite
  have hLB : GGLBalanceInput := ggGammaSuppliers_proved.1
  obtain ⟨r, hdr, _, _, _, _, _, hAJ⟩ :=
    hH.unitary_exactThree_typeA_card_J_of_K hLB hM hpq hd5 hdiag h3
  have hfac : (r - 2).factorial = (3 : ℕ).factorial := by
    calc (r - 2).factorial = 6 := hAJ.symm.trans hAJsix
         _ = (3 : ℕ).factorial := by norm_num
  have hr : r - 2 = 3 := (Nat.factorial_inj (by omega : 1 < r - 2)).mp hfac
  have hd6 : d = 6 := by omega
  cases hd6
  obtain ⟨_, δ, hδ, hδdiag⟩ :=
    hH.unitary_exactThree_J_model_three_of_K hLB hM hpq hdiag h3
  have hodd : Odd n :=
    CFSG.RankThree.PartTwo.Census.odd_of_three_dvd_two_pow_add_one hpq
  have hn3 : 3 ≤ n := by
    rcases hodd with ⟨k, hk⟩
    omega
  exact ⟨F, hField, hFinite, n, ψ, δ, hFK, hodd, hn3, hM, hδ, hdiag, hδdiag⟩

theorem GGResHyp.relativeF4_K3_classification
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel GGF4ThreeLabel 3 Bs L ∨
      GGInnerDiagOnLabel (fun _ lab => lab.tag = .E6 ∧ 3 ≤ lab.n ∧
        3 ∣ 2 ^ lab.n + 1) 3 Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        3 ∣ 2 ^ lab.n + 1) 3 Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (h3 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (n rank d : ℕ)
      (θ : ↥K ⧸ Subgroup.center ↥K ≃* LargeEvenProj (unitarySU 2 n F d))
      (ψ : ↥(unitarySU 2 n F d) →* ↥K),
      rank = 5 ∧ d = 6 ∧ 2 ≤ n ∧ Odd n ∧ 3 ≤ n ∧ Nat.card F = (2 ^ n) ^ 2 ∧
        Nat.card Bs = 3 ^ 5 ∧ Nat.card ↥(ggAutomizer J Bs) = 6 ∧
        GGWeylTypeData 2 6 1 ∧
        GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny := by
  have hJ0 : GGInnerDiagOn Bs J :=
    ggBstarInnerDiagJInput_holds G 3 B Bs x L D J hH.1 hH.2.2.1.1
  have hJ : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs J :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hJ0
  rcases ggResExact3_K_reverse_or_exact2_singular ggTBFixInput_holds hH h3 with
    hL3 | ⟨hL2, -⟩
  · rcases hL with hF4 | hE6
    · exact (ggResExact3_false_of_f4Three_L (ggTBTorAll_of_remaining trivial)
        ggTBTorLiftRows_holds TCJ.ggTCJKnown_holds ggLabelRigidInput_holds
        (ggGammaSuppliers_proved.2) hH hJ hF4 hL3).elim
    · have hE6' : GGInnerDiagOnLabel
          (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs L :=
        hE6.mono_label (fun lab h => ⟨h.1, h.2.2⟩)
      exact (GGResHyp.not_exactThree_of_splitE6_qplus_L hH hE6' hL3).elim
  · have hAL : Nat.card ↥(ggAutomizer L Bs) = 1152 := by
      rcases hL with hF4 | hE6
      · exact card_ggAutomizer_of_f4Three hH.1 hH.2.2.2.1 hF4
          (card_bstar_inf_center_le hH.1)
      · exact (ggRelativeF4_actual_side_card_and_rank hH (Or.inl rfl) hE6
          (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_E6Plus hlab
            ⟨hs.1, hs.2.2⟩)).1
    exact hH.relativeF4_K3_classification_of_L2 hL2 hAL hU hN h3

private theorem largeEvenRawDatumLegacy_mono_linear
    {rank n : ℕ} {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → Q' R I F)
    (h : LargeEvenRawDatumLegacy (⟨.A, rank, n⟩ : LargeEvenLabel) Q) :
    LargeEvenRawDatumLegacy (⟨.A, rank, n⟩ : LargeEvenLabel) Q' := by
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeLinear] at h ⊢
  obtain ⟨K, hField, hFinite, hK, hq⟩ := h
  exact ⟨K, hField, hFinite, hK, hQQ' _ _ _ hq⟩

private theorem largeEvenRawDatumLegacy_mono_unitary
    {rank n : ℕ} {Q Q' : LargeEvenRawCont}
    (hQQ' : ∀ (R : Type) [Group R] (I F : Set (MulAut R)), Q R I F → Q' R I F)
    (h : LargeEvenRawDatumLegacy (⟨.twA, rank, n⟩ : LargeEvenLabel) Q) :
    LargeEvenRawDatumLegacy (⟨.twA, rank, n⟩ : LargeEvenLabel) Q' := by
  dsimp only [LargeEvenRawDatumLegacy, LargeEvenRecipeUnitary] at h ⊢
  obtain ⟨K, hField, hFinite, hK, hq⟩ := h
  exact ⟨K, hField, hFinite, hK, hQQ' _ _ _ hq⟩

private theorem exists_exact_linTwo_marking_of_residualL
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {p : ℕ}
    (h : GGInnerDiagOnLabel ggThreeResidualLabelL p Bs L) :
    ∃ lab : LargeEvenLabel, p = 3 ∧ GGLinTwoLabel 3 lab ∧ 6 ≤ lab.rank ∧
      GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨hS, hN, hact⟩ := hP
  rcases lab with ⟨tag, rank, n⟩
  unfold ggThreeResidualLabelL at hS
  obtain ⟨hp3, htag, hn, hr⟩ := hS
  cases htag
  cases hn
  have hr' : 6 ≤ rank := by simpa using hr
  have h5 : 5 ≤ rank := by omega
  refine ⟨⟨.A, rank, 1⟩, hp3, ⟨rfl, by simpa using h5, rfl, rfl⟩, hr', ?_⟩
  refine ⟨hperf, ⟨.A, rank, 1⟩, ?_, ?_⟩
  · simpa using hlab
  · apply largeEvenRawDatumLegacy_mono_linear ?_ hraw
    intro R' _ I' F' hq
    obtain ⟨hSimple, hNonab, θ', hqP⟩ := hq
    exact ⟨hSimple, hNonab, θ', ⟨rfl, hqP.2.1, hqP.2.2⟩⟩

private theorem exists_exact_twA_marking_of_residualK
    {G : Type} [Group G] [Finite G] {Bs K : Subgroup G} {p : ℕ}
    (h : GGInnerDiagOnLabel ggThreeResidualLabelK p Bs K) :
    ∃ lab : LargeEvenLabel, ggThreeResidualLabelK p lab ∧ 1 ≤ lab.n ∧
      GGInnerDiagOnLabel (fun _ lab' => lab' = lab) p Bs K := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := h
  obtain ⟨R, hR, I, F, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨hS, hN, hact⟩ := hP
  rcases lab with ⟨tag, rank, n⟩
  unfold ggThreeResidualLabelK at hS
  obtain ⟨htag, hr, hpr, hpq⟩ := hS
  cases htag
  refine ⟨⟨.twA, rank, n⟩, ⟨rfl, hr, hpr, hpq⟩, hlab.1, ?_⟩
  refine ⟨hperf, ⟨.twA, rank, n⟩, ?_, ?_⟩
  · simpa using hlab
  · apply largeEvenRawDatumLegacy_mono_unitary ?_ hraw
    intro R' _ I' F' hq
    obtain ⟨hSimple, hNonab, θ', hqP⟩ := hq
    exact ⟨hSimple, hNonab, θ', ⟨rfl, hqP.2.1, hqP.2.2⟩⟩

theorem ggResMultiNodeRestThreeCensusInput_of_KUnitaryQGeFourJoin
    (hK : GGResMultiNodeRestThreeKUnitaryQGeFourJoinInput) :
    GGResMultiNodeRestThreeCensusInput := by
  intro G _ _ p B Bs x L D J y K hH _ hF hS hE hdata
  rcases hdata with ⟨hD, hM, hsmL, hKsettled, hres, htwo, hC2, hSU2⟩
  rcases hD with ⟨hDL, hnL, hE6L, hresL⟩ |
    ⟨hDK, hnK, hE6K, hL2, hLn, hLs, hresK⟩
  · obtain ⟨lab, hp3, hlab, hr6, hmark⟩ :=
      exists_exact_linTwo_marking_of_residualL hresL
    have hH3 : GGResHyp 3 B Bs x L D J y K := by simpa [hp3] using hH
    have hDL3 : GGResLeviDatumExact3 3 Bs L J K ggSelAny ggTypAny := by
      simpa [hp3] using hDL
    rcases lt_or_ge lab.rank 7 with hlt | hge
    · have h6 : lab.rank = 6 := by omega
      have hmark3 : GGInnerDiagOnLabel
          (fun p lab' => p = 3 ∧ lab' = lab) 3 Bs L := by
        refine GGInnerDiagOnLabel.mono_label
          (S := fun _ lab' => lab' = lab) ?_ hmark
        intro lab' hlab'
        subst lab'
        exact ⟨rfl, rfl⟩
      exact (GGResHyp.false_of_exact3_linTwo_rank_five_six hH3
        ⟨lab, hlab, Or.inr h6, hmark3⟩ (Or.inl hDL3)).elim
    · rcases le_or_gt lab.rank 8 with hle | hgt
      · have h78 : lab.rank = 7 ∨ lab.rank = 8 := by omega
        exact (GGResHyp.false_of_exact3_either_linTwo_rank_seven_eight hH3 lab hlab h78
          hmark (Or.inl hDL3)).elim
      · have h9 : 9 ≤ lab.rank := by omega
        exact (GGResHyp.false_of_exact3_either_linTwo_rank_ge9 hH3 lab hlab h9
          hmark (Or.inl hDL3)).elim
  · obtain ⟨lab, hresKlab, hnpos, hmark⟩ :=
      exists_exact_twA_marking_of_residualK hresK
    by_cases hn1 : lab.n = 1
    · have hU : GGInnerDiagOnLabel
          (fun p lab' => lab'.tag = .twA ∧ 4 ≤ lab'.rank ∧ lab'.n = 1 ∧
            p ∣ 2 ^ lab'.n + 1) p Bs K := by
        refine GGInnerDiagOnLabel.mono_label
          (S := fun _ lab' => lab' = lab) ?_ hmark
        intro lab' hlab'
        subst lab'
        exact ⟨hresKlab.1, hresKlab.2.1, hn1, hresKlab.2.2.2⟩
      have hNoRow : ¬ GGResRowAt ggRowSUCorank3 p J K := by
        intro hrow
        exact hres (Or.inr (Or.inl hrow))
      exact (GGResHyp.not_exactThree_K_of_qTwo_highrank hH hU hNoRow hDK).elim
    · have hn2 : 2 ≤ lab.n := by omega
      have hr5 : 5 ≤ lab.rank := by
        by_contra h
        have hr4 : lab.rank = 4 := by
          have := hresKlab.2.1
          omega
        have hU4 : GGInnerDiagOnLabel
            (fun p lab' => lab'.tag = .twA ∧ lab'.rank = 4 ∧ 2 ≤ lab'.n ∧
              p ∣ 2 ^ lab'.n + 1) p Bs K := by
          refine GGInnerDiagOnLabel.mono_label
            (S := fun _ lab' => lab' = lab) ?_ hmark
          intro lab' hlab'
          subst lab'
          exact ⟨hresKlab.1, hr4, hn2, hresKlab.2.2.2⟩
        exact hH.not_exactThree_K_of_unitary_rank_four_qGeFour hU4 hDK
      exact hK G p B Bs x L D J y K hH hF hS hE
        ⟨hDK, ⟨lab, hresKlab, hr5, hn2, hmark⟩, hnK, hE6K, hL2, hLn, hLs,
          hM, hsmL, hKsettled, hres, htwo, hC2, hSU2⟩


theorem ggResMultiNodeRestThreeSettledInput_of_KUnitaryQGeFourJoin
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hK : GGResMultiNodeRestThreeKUnitaryQGeFourJoinInput) :
    GGResMultiNodeRestThreeSettledInput :=
  ggResMultiNodeRestThreeSettledInput_of_census hRig hraw hiso
    (ggResMultiNodeRestThreeCensusInput_of_KUnitaryQGeFourJoin hK)

theorem ggResMultiNodeRestThreeOutsideRowsInput_of_KUnitaryQGeFourJoin
    (hT : GGTBTorAll) (hLift : GGTBTorLiftRows) (hTCJ : GGTCJKnown)
    (hRig : GGLabelRigidInput) (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) (hQ1 : GGBstarInnerDiagJInput)
    (hK : GGResMultiNodeRestThreeKUnitaryQGeFourJoinInput) :
    GGResMultiNodeRestThreeOutsideRowsInput :=
  ggResMultiNodeRestThreeOutsideRowsInput_of_singular hT hLift hTCJ hRig hLB hP hQ1
    (ggResMultiNodeRestThreeSingularInput_of_settled hT hLift hTCJ hRig hLB hP hQ1
      (ggResMultiNodeRestThreeSettledInput_of_KUnitaryQGeFourJoin hRig hraw hiso hK))



theorem GGResHyp.not_exactThree_K_of_f4Two_L
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hL2mark : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .F4 ∧ lab.n = 1) 3 Bs L)
    (hU : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .twA ∧ 4 ≤ lab.rank ∧ 2 ≤ lab.n ∧
        3 ∣ 2 ^ lab.n + 1) 3 Bs K)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (h3 : GGResLeviDatumExact3 3 Bs K J L ggSelAny ggTypAny) : False := by
  have hJ0 : GGInnerDiagOn Bs J :=
    ggBstarInnerDiagJInput_holds G 3 B Bs x L D J hH.1 hH.2.2.1.1
  have hJ : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs J :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => ⟨trivial, h⟩) hJ0
  have hF4three : GGInnerDiagOnLabel GGF4ThreeLabel 3 Bs L :=
    hL2mark.mono_label (fun lab h => by
      obtain ⟨hp, htag, hn⟩ := h
      exact ⟨htag, hp, by rw [hn]; norm_num⟩)
  rcases ggResExact3_K_reverse_or_exact2_singular ggTBFixInput_holds hH h3 with
    hL3 | ⟨hL2, -⟩
  · exact (ggResExact3_false_of_f4Three_L (ggTBTorAll_of_remaining trivial)
      ggTBTorLiftRows_holds TCJ.ggTCJKnown_holds ggLabelRigidInput_holds
      (ggGammaSuppliers_proved.2) hH hJ hF4three hL3).elim
  · exact ggResF4ExactTwo_false hH hL2mark hL2

end Settled

end CFSG.StandardType

end
