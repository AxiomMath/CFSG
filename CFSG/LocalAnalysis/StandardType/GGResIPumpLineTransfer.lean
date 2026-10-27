module

public import CFSG.LocalAnalysis.StandardType.GGLieM6cFinal

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Recipe

public import CFSG.LocalAnalysis.StandardType.GGCanonicalToLegacy
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021LayerOrder

public import CFSG.LocalAnalysis.StandardType.GGResILineInputs
public import CFSG.LocalAnalysis.StandardType.GGTPNLineDefs
public import CFSG.LocalAnalysis.StandardType.GGResJLineA3
public import CFSG.LocalAnalysis.StandardType.GGResJLineBCGamma
public import CFSG.LocalAnalysis.StandardType.GGCSRHolds
public import CFSG.LocalAnalysis.StandardType.GGRootGenSmallRankQFour
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenCore
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineAut
public import CFSG.LocalAnalysis.StandardType.GGResIPumpLineA3
public import CFSG.LocalAnalysis.StandardType.GGResILineBThree
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenKernel
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
public import CFSG.LocalAnalysis.StandardType.GGTBJWeyl
public import CFSG.LocalAnalysis.StandardType.GGNbrU63Setup
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Holds
public import CFSG.LocalAnalysis.StandardType.GGInndiagCommRestExcl
public import CFSG.LocalAnalysis.StandardType.GGOddCenterPrimeLabel
public import CFSG.LocalAnalysis.StandardType.KGCenterCoprime
public import CFSG.LocalAnalysis.StandardType.GGQTwoU5Bridges
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclicHolds
public import CFSG.LocalAnalysis.StandardType.GGTBTorCHolds
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldOtherClassicalCover
public import CFSG.LocalAnalysis.StandardType.GGCRNOrthNs
public import CFSG.LocalAnalysis.StandardType.GGTBTorE7
public import CFSG.LocalAnalysis.StandardType.GGTBTorE8Split
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylExcPlusLift
public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoAux
public import CFSG.LocalAnalysis.StandardType.GGTBTorDSplit
public import CFSG.LocalAnalysis.StandardType.GGTBTorDNsHolds
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDHolds
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelDMinusSplit
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticOmega
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6Three
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNE6Cells
public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrder
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesE6NonsplitThreeHolds
public import CFSG.LocalAnalysis.StandardType.GGL45E67Center
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNE6Frame
public import CFSG.LocalAnalysis.StandardType.GGTorusWeylTypeEven
public import CFSG.LocalAnalysis.StandardType.GGTBRowOFrameAux
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourNotToral
public import CFSG.LocalAnalysis.StandardType.GGTwE6E4bReflection
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6
public import CFSG.LocalAnalysis.StandardType.GGNbrTableBE6Three
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelHoldsBoth
public import CFSG.LocalAnalysis.StandardType.GGPumpTwExcKnownHolds
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitTwE6Three
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ1Holds

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggPumpLineAutKnown_holds :
    GGPumpLineAutKnown := by
  intro T labJ labX hJ hΛX hrow hoff
  cases T with
  | A2 => exact ggPumpLineAutKnown_A2 labJ labX hJ hΛX hrow hoff
  | B2 => exact ggPumpLineAutKnown_B2 labJ labX hJ hΛX hrow hoff
  | A3 => exact ggPumpLineAutKnown_A3 labJ labX hJ hΛX hrow hoff
  | B3 =>
    exact ggPumpLineAutKnown_BThreeCThree .B3 (Or.inl rfl) labJ labX hJ hΛX hrow hoff
  | C3 =>
    exact ggPumpLineAutKnown_BThreeCThree .C3 (Or.inr rfl) labJ labX hJ hΛX hrow hoff

private theorem ggPumpLine_centralizer_card
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    {z : G} {X : Subgroup G} (hnbX : GGNbr 3 B x D J z X) (hJX : J ≤ X) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = 3 := by
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hpre := hcfg.2.2.1
  have hDcard : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDB : D ≤ B := hpre.1
  have hzB : z ∈ B := hnbX.1.2.1
  have hz1 : z ≠ 1 := hnbX.1.2.2.1
  have hXz : X ≤ Subgroup.centralizer ({z} : Set G) := hnbX.1.2.2.2.1
  have hDz : D = Subgroup.closure {x, z} := hnbX.2.1
  have hzD : z ∈ D := by
    rw [hDz]
    exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hzC : z ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact Subgroup.mem_centralizer_singleton_iff.mp (hXz hw)
  have hxC : x ∉ Subgroup.centralizer (X : Set G) := by
    intro hx
    apply hnbX.2.2.2
    have hbot : ⁅X, Subgroup.zpowers x⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro w hw
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
      exact ((Commute.zpow_left (Subgroup.mem_centralizer_iff.mp hx w hw).symm k)).eq
    rw [hbot]
    exact bot_le
  have hCD : Bs ⊓ Subgroup.centralizer (X : Set G) = D ⊓ Subgroup.centralizer (X : Set G) := by
    apply le_antisymm
    · intro c hc
      exact ⟨hI1 ⟨hc.1, Subgroup.mem_centralizer_iff.mpr fun w hw =>
        Subgroup.mem_centralizer_iff.mp hc.2 w (hJX hw)⟩, hc.2⟩
    · exact inf_le_inf_right _ (hDB.trans hcfg.2.1.1)
  have hC3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = 3 := by
    rw [hCD]
    have hdvd : Nat.card ↥(D ⊓ Subgroup.centralizer (X : Set G)) ∣ 3 ^ 2 := by
      rw [← hDcard]
      exact Subgroup.card_dvd_of_le inf_le_left
    have hne1 : Nat.card ↥(D ⊓ Subgroup.centralizer (X : Set G)) ≠ 1 := by
      intro h1
      have := Subgroup.eq_bot_of_card_eq _ h1
      have hz : z ∈ D ⊓ Subgroup.centralizer (X : Set G) := ⟨hzD, hzC⟩
      rw [this, Subgroup.mem_bot] at hz
      exact hz1 hz
    have hne9 : Nat.card ↥(D ⊓ Subgroup.centralizer (X : Set G)) ≠ 3 ^ 2 := by
      intro h9
      have hle : D ≤ D ⊓ Subgroup.centralizer (X : Set G) :=
        (Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hDcard, h9])).symm.le
      exact hxC (hle hxD).2
    rcases (Nat.dvd_prime_pow Nat.prime_three).mp hdvd with ⟨k, hk, hk'⟩
    interval_cases k
    · exact absurd (by simpa using hk') hne1
    · simpa using hk'
    · exact absurd hk' hne9
  exact hC3

theorem ggPumpLineThreeInput_of_row
    (hRig : GGLabelRigidInput)
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 3)]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hJT : GGResLineJDatum 3 Bs J T)
    (hcard : Nat.card Bs = 3 ^ (T.rank + 2))
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    {z : G} {X : Subgroup G} (hnbX : GGNbr 3 B x D J z X) (hJX : J ≤ X)
    {labJ labX : LargeEvenLabel} (_hΛJ : LargeEvenInLambda2 labJ)
    (hΛX : LargeEvenInLambda2 labX)
    (hrow : GGTablePRow 3 labJ labX)
    (hnotE6 : ¬ (labX.tag = .twE6 ∧ 3 ∣ 2 ^ labX.n + 1))
    (hJlab : ggResLineJLabel T labJ) (hhasJ : GGHasLabel labJ (J ⧸ Subgroup.center J))
    (hhasX : GGHasLabel labX (X ⧸ Subgroup.center X)) :
    ¬ T.bad ∣ Nat.card (ggAutomizer X Bs) := by
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  have hNoTr : GGNoTransvection 3 Bs := hH.2.2.2.1
  have hSS : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hDJ : LargeEvenStdSub 3 B x L D J := hcfg.2.2
  have hpre := hDJ.1
  have hDcard : Nat.card D = 3 ^ 2 := hpre.2.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDB : D ≤ B := hpre.1
  have hxBs : x ∈ Bs := hcfg.2.1.1 (hDB hxD)
  have hinnX : GGInnerDiagOn Bs X := hH.2.2.1.2 z X hnbX
  have hperfX : commutator ↥X = ⊤ := hinnX.1
  have hN : Bs ≤ Subgroup.normalizer (X : Set G) := by
    have hIDX : GGInnerDiagOn Bs X := hinnX
    obtain ⟨-, lab, -, hraw⟩ := hIDX
    obtain ⟨R, _, I, F, -, -, θ, hN, -⟩ := largeEvenRawDatum_exists hraw
    exact hN
  have hC3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) = 3 :=
    ggPumpLine_centralizer_card hH hI1 hnbX hJX
  have hγ : Nat.card (ggGamma X hN).range = 3 ^ (T.rank + 1) := by
    have h1 := NbrU63.card_range_ggGamma_mul_card_inf hN
    rw [hC3, hcard, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hrk : 2 ≤ T.rank := by cases T <;> decide
  have hrk3 : T.rank ≤ 3 := by cases T <;> decide
  have hSelf : GGTorusSelfCent 3 (ggGamma X hN).range := ggTorusSelfCent_ggGamma hN hSC
  have hKAX : LargeEvenLabelAll labX fun R _ I _ =>
      GGTorusAutNotDvdSCJ 3 labJ R I (T.rank + 1) T.bad :=
    ggPumpLineAutKnown_holds T labJ labX hJlab hΛX hrow hnotE6
  obtain ⟨R, _, θ, I, F, hBsI, hP⟩ := exists_innerDiagDatum_of_labelAll hRig hinnX hΛX hhasX
    hKAX hN
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma X hN).range := by
    rw [hγ]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hTorus : GGTorusTBGroup 3 (T.rank + 1) R I ↥X (ggQuotHom θ) (ggGamma X hN).range :=
    ggTorusTBGroup_of_marking (p := 3) (r := T.rank + 1) Nat.prime_three hBs hSC hperfX θ hN hBsI
      hγ.ge h3
  have hAb : IsElemAbelian 3 (ggGamma X hN).range := hTorus.2.2.2.1
  have hAI := hTorus.2.2.2.2.1
  have hxN : x ∈ Subgroup.normalizer (X : Set G) := hN hxBs
  let e : MulAut ↥X := X.normalizerMonoidHom ⟨x, hxN⟩
  have he_mem : e ∈ (ggGamma X hN).range := ⟨⟨x, hxBs⟩, rfl⟩
  have hcomp : IsComponentOf J (X ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hSS hDJ hnbX hJX
  have hJcomp : IsComponentOf (J.subgroupOf X) (ggFixSub e) :=
    ggIsComponentOf_ggFixSub_normalizerMonoidHom hxN hcomp
  have hHasLabelJ : GGHasLabel labJ (↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X)) :=
    ggHasLabel_of_mulEquiv (QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hJX).symm
      (Subgroup.map_center_eq _)) hhasJ
  have hnot := hP ↥X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperfX
    (ggGamma X hN).range hAb hAI h3 hγ.le hSelf ⟨e, he_mem, J.subgroupOf X, hJcomp, hHasLabelJ⟩
  have hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    rw [← hC3]
    exact Subgroup.card_le_of_le (inf_le_inf_right _ inf_le_left)
  intro hbad
  exact hnot (hbad.trans (card_ggAutomizer_dvd_gamma Nat.prime_three hBs hNoTr hN hZ))

theorem ggPumpLineThreeInput_of_label
    (hTP : GGNbrTablePNbrInputI1On GGRegimeLine) (hRig : GGLabelRigidInput)
    (hRk : GGTwE6ThreeNbrRankInput)
    {G : Type} [Group G] [Finite G] [Fact (Nat.Prime 3)]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hJT : GGResLineJDatum 3 Bs J T)
    (hcard : Nat.card Bs = 3 ^ (T.rank + 2))
    (hI1 : Bs ⊓ Subgroup.centralizer (J : Set G) ≤ D)
    {z : G} {X : Subgroup G} (hnbX : GGNbr 3 B x D J z X) (hJX : J ≤ X)
    {labJ : LargeEvenLabel} (hΛJ : LargeEvenInLambda2 labJ)
    (hJlab : ggResLineJLabel T labJ) (hhasJ : GGHasLabel labJ (J ⧸ Subgroup.center J)) :
    ¬ T.bad ∣ Nat.card (ggAutomizer X Bs) := by
  have hcfg : GGConfig 3 B Bs x L D J := hH.1
  have hinnX : GGInnerDiagOn Bs X := hH.2.2.1.2 z X hnbX
  obtain ⟨labX₀, hΛX₀, hhasX₀, -⟩ := largeEvenMarking_exists_hasLabel hinnX
  have hreg : GGRegimeLine 3 (Nat.card Bs) labJ labX₀ := by
    refine ⟨rfl, ?_, T, hJlab⟩
    have hrk3 : T.rank ≤ 3 := by cases T <;> decide
    rw [hcard]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨labJ', labX', hΛJ', hΛX', hrow, hhasJ', hhasX'⟩ :=
    hTP G 3 B Bs x L D J z X hcfg hH.2.2.1.1 hinnX hnbX hI1 labJ labX₀ hΛJ hΛX₀ hreg hhasJ hhasX₀
  have hJlab' : ggResLineJLabel T labJ' :=
    ggResLineJLabel_of_iso hJlab (hRig labJ labJ' _ hΛJ hΛJ' hhasJ hhasJ')
  have hN : Bs ≤ Subgroup.normalizer (X : Set G) := by
    obtain ⟨-, lab, -, hraw⟩ := hinnX
    obtain ⟨R, _, I, F, -, -, θ, hN, -⟩ := largeEvenRawDatum_exists hraw
    exact hN
  have hC3 := ggPumpLine_centralizer_card hH hI1 hnbX hJX
  have hγ : Nat.card (ggGamma X hN).range = 3 ^ (T.rank + 1) := by
    have h1 := NbrU63.card_range_ggGamma_mul_card_inf hN
    rw [hC3, hcard, pow_succ] at h1
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h1
  have hSelf : GGTorusSelfCent 3 (ggGamma X hN).range :=
    ggTorusSelfCent_ggGamma hN hcfg.2.1.2.2.2
  have hnotE6 : ¬ (labX'.tag = .twE6 ∧ 3 ∣ 2 ^ labX'.n + 1) := by
    rintro ⟨htag, hdvd⟩
    have hBad : GGTwE6BadLabel 3 labX' := ⟨htag, rfl, hdvd⟩
    have hMark : GGInnerDiagOnLab GGTwE6BadLabel 3 Bs X :=
      ggInnerDiagOnLab_of_hasLabel hRig hinnX hΛX' hhasX' hBad
        (largeEvenSplit_of_twE6BadLabel hBad)
    have h5 : 3 ^ 5 ≤ Nat.card (ggGamma X hN).range :=
      hRk G 3 B Bs x L D J hcfg rfl z X hnbX hMark hN hSelf
    rw [hγ] at h5
    have hrk3 : T.rank ≤ 3 := by cases T <;> decide
    have : 3 ^ 5 ≤ 3 ^ 4 :=
      h5.trans (Nat.pow_le_pow_right (by norm_num) (by omega))
    norm_num at this
  exact ggPumpLineThreeInput_of_row hRig hH hJT hcard hI1 hnbX hJX hΛJ' hΛX' hrow hnotE6
    hJlab' hhasJ' hhasX'

theorem ggPumpLineThreeInput_of_known
    (hTBJ : GGResLineJLabelInput)
    (hTP : GGNbrTablePNbrInputI1On GGRegimeLine) (hRig : GGLabelRigidInput)
    (hRk : GGTwE6ThreeNbrRankInput) : GGPumpLineThreeInput := by
  intro G _ _ p B Bs x L D J y K hH _ hp3 _ T hJT hcard hI1 z X hnbX hJX
  subst hp3
  obtain ⟨labJ, hΛJ, hJlab, hhasJ⟩ := hTBJ G 3 B Bs x L D J y K hH rfl T hJT
  exact ggPumpLineThreeInput_of_label hTP hRig hRk hH hJT hcard hI1 hnbX hJX hΛJ hJlab hhasJ

section A3SmallRankActualJ

open CFSG.Open

theorem GGResHyp.largeEvenMarking_card_ge_of_gamma
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {P : ℕ → LargeEvenLabel → Prop} (hMark : GGInnerDiagOnLabel P 3 Bs J)
    {m : ℕ} (hm : m ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range) :
    LargeEvenMarking ↥J (fun lab R _ I _ _ => P 3 lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
        m ≤ Nat.card E) := by
  have hJperf : commutator ↥J = ⊤ := hMark.1
  have hN0 : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  refine largeEvenMarking_mono ?_ hMark
  rintro lab R _ I _ θ ⟨hP, hN, hact⟩
  have hgamma : ggGamma J hN = ggGamma J hN0 := by ext b; rfl
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let E : Subgroup (MulAut R) := A.map (ggInducedAut θ)
  have hAe : IsElemAbelian 3 A := by
    dsimp [A]
    exact isElemAbelian_range
      (fun a b : ↥Bs => (@IsMulCommutative.is_comm ↥Bs _ hH.1.2.1.2.1.1).comm a b)
      (fun b : ↥Bs => Subtype.ext (by simpa using hH.1.2.1.2.1.2 b b.2))
      (ggGamma J hN)
  have hEe : IsElemAbelian 3 E := hAe.map _
  have hEcard : Nat.card E = Nat.card A := by
    dsimp [E]
    exact Subgroup.card_map_of_injective (ggInducedAut_injective_of_perfect hJperf θ)
  have hmA : m ≤ Nat.card A := by
    simpa [A, hgamma] using hm
  have hmE : m ≤ Nat.card E := by
    rwa [hEcard]
  have hEI : (E : Set (MulAut R)) ⊆ I := by
    rintro _ ⟨a, ha, rfl⟩
    obtain ⟨b, rfl⟩ := ha
    have hmem := ggBeta_mem J θ hN hact b
    have hbeta : ggBeta J θ hN b = ggInducedAut θ (ggGamma J hN b) := by
      rw [ggBeta_eq, ggLAut_eq_ggInducedAut]
      rfl
    have hmem' : ggInducedAut θ (ggGamma J hN b) ∈ I := by
      rwa [hbeta] at hmem
    exact hmem'
  exact ⟨hP, E, hEI, hEe, hmE⟩

theorem GGResHyp.largeEvenMarking_pRank_ge_three_of_B3C3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3)
    {P : ℕ → LargeEvenLabel → Prop} (hMark : GGInnerDiagOnLabel P 3 Bs J) :
    LargeEvenMarking ↥J (fun lab R _ I _ _ => P 3 lab ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
        3 ^ 3 ≤ Nat.card E) :=
  GGResHyp.largeEvenMarking_card_ge_of_gamma hH hMark
    (cube_le_card_gamma_of_B3C3 (GGResHyp.Bs_le_normalizer_J hH) hD hT)

theorem GGResHyp.rank_ge_three_of_A3_label
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    {lab : LargeEvenLabel} (hLambda : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (J ⧸ Subgroup.center J))
    (htag : lab.tag = .A ∨ lab.tag = .twA) : 3 ≤ lab.rank := by
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  haveI : Group.IsPerfect ↥J := Group.IsPerfect.mk hJperf
  obtain ⟨E, hEa, hEcard⟩ := GGResHyp.exists_coroot_quotient_of_A3 hH hD
  exact ggSmallThreeRank_linear_rank_three_of_elemAbelian (H := ↥J) hLambda hhas hEa
    hEcard.ge htag

theorem GGResHyp.not_twD_rank_two_of_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    {lab : LargeEvenLabel} (hLambda : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (J ⧸ Subgroup.center J))
    (htag : lab.tag = .twD) (hrank : lab.rank = 2) : False := by
  obtain ⟨E, hEa, hEcard⟩ := GGResHyp.exists_coroot_quotient_of_A3 hH hD
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hrank
  subst htag
  subst hrank
  have hhas' := hhas
  simp only [GGHasLabel, LargeEvenRawDatum, ↓reduceIte] at hhas'
  obtain ⟨Kf, hKfield, hKfin, hKcard, hQ⟩ := hhas'
  letI : Field Kf := hKfield
  letI : Finite Kf := hKfin
  obtain ⟨e⟩ := hQ
  have hcardK : Nat.card Kf = 2 ^ (2 * n) := by
    rw [hKcard, ← pow_mul, Nat.mul_comm]
  haveI : CharP Kf 2 := charP_two_of_card (m := 2 * n) hcardK
  have h3K : ((3 : ℕ) : Kf) ≠ 0 := by
    intro hzero
    have h2dvd : (2 : ℕ) ∣ 3 := (CharP.cast_eq_zero_iff Kf 2 3).mp hzero
    norm_num at h2dvd
  let eR : LargeEvenProj (LargeEvenSLGroup (Fin 2) Kf) ≃*
      StatedProj (StatedSL 2 Kf) := by
    rw [largeEvenSLGroup_eq_statedSL]
  let e' : (J ⧸ Subgroup.center J) ≃* StatedProj (StatedSL 2 Kf) := e.trans eR
  have hEa' : IsElemAbelian 3 (E.map e'.toMonoidHom) := hEa.map e'.toMonoidHom
  have hbound := CFSG.HardMathSupport.Malle.E27Lie.card_le_of_statedProj_SL
    (F := Kf) (n := 2) h3K (by norm_num) (E.map e'.toMonoidHom) hEa'
  have hcardmap : Nat.card (E.map e'.toMonoidHom) = Nat.card E :=
    Subgroup.card_map_of_injective (K := E) (f := e'.toMonoidHom) e'.injective
  rw [hcardmap] at hbound
  norm_num at hbound
  omega

theorem not_largeEvenMarking_sevenSmall
    {X : Type} [Group X] :
    ¬ LargeEvenMarking X (fun lab R _ I _ _ =>
      (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
        lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
        3 ^ 3 ≤ Nat.card E) := by
  intro h
  have hAll : GGSmallThreeRank := ggSmallThreeRank_of_labels
  have h' := largeEvenMarking_and_labelAll
    (P := fun lab R _ I _ _ =>
      (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
        lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) ∧
      ∃ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I ∧ IsElemAbelian 3 E ∧
        3 ^ 3 ≤ Nat.card E)
    (S := fun lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der)
    (P' := fun R _ I _ => ∀ A : Subgroup (MulAut R),
      (A : Set (MulAut R)) ⊆ I → IsElemAbelian 3 A → Nat.card A ≤ 3 ^ 2)
    (fun lab hlab htag => hAll lab hlab htag)
    (fun _ _ _ _ _ _ hP => hP.1) h
  obtain ⟨-, lab, -, hraw⟩ := h'
  obtain ⟨R, _, I, _, _, _, _, ⟨-, E, hEI, hEa, hE3⟩, hle⟩ := largeEvenRawDatum_exists hraw
  have h9 := hle E hEI hEa
  omega

theorem GGResHyp.actual_J_not_small_of_B3C3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .G2 ∨ lab.tag = .triD4 ∨
      lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨ lab.tag = .G2der ∨
      lab.tag = .twF4der) 3 Bs J) :
    False :=
  not_largeEvenMarking_sevenSmall
    (GGResHyp.largeEvenMarking_pRank_ge_three_of_B3C3 hH hD hT hMark)

end A3SmallRankActualJ

section Certificates

private theorem congr_normalizerToCenterQuotientAut_eq_ggLAut
    {G : Type} [Group G] {K Bs : Subgroup G} {R : Type} [Group R]
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (b : ↥Bs) :
    MulAut.congr θ (normalizerToCenterQuotientAut K Bs hN b) =
      ggLAut K θ ⟨b, hN b.2⟩ := by
  rfl

theorem GGResHyp.prime_dvd_card_J_of_innerDiag
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hJmark : GGInnerDiagOn Bs J) :
    p ∣ Nat.card J := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨-, -, -, -, -, hBeta, -, -⟩ := hH.1.1
  have hp2 : p ≠ 2 := hBeta.2.1
  have hBsP : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := hH.Bs_le_normalizer_J
  have hγ : p ^ 2 ≤ Nat.card (ggGamma J hN).range := by
    simpa using (GGResHyp.sq_le_card_gamma_J (p := p) hH)
  have hγne : (ggGamma J hN).range ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card (ggGamma J hN).range = 1 := by rw [hbot, Subgroup.card_bot]
    nlinarith [hp.two_le]
  obtain ⟨g, hgne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hγne
  obtain ⟨b, hb⟩ := MonoidHom.mem_range.mp g.2
  have hγb : ggGamma J hN b ≠ 1 := by
    intro h
    apply hgne
    apply Subtype.ext
    simpa [← hb] using h
  obtain ⟨hperfJ, labJ, hlabJ, hrawJ⟩ := hJmark
  obtain ⟨R, instR, I, F, hsimple, hna, θ, hPJ⟩ := largeEvenRawDatum_exists hrawJ
  let β : MulAut (↥J ⧸ Subgroup.center ↥J) :=
    normalizerToCenterQuotientAut J Bs hN b
  have hβp : β ^ p = 1 := by
    apply (MulAut.congr θ).injective
    rw [map_pow, congr_normalizerToCenterQuotientAut_eq_ggLAut, map_one]
    have hbpow : (⟨b, hN b.2⟩ : Subgroup.normalizer (J : Set G)) ^ p = 1 := by
      apply Subtype.ext
      simpa using hBsP.2 (b : G) b.2
    calc (ggLAut J θ ⟨b, hN b.2⟩) ^ p
        = ggLAut J θ (⟨b, hN b.2⟩ ^ p) := by rw [map_pow]
      _ = 1 := by rw [hbpow, map_one]
  have hβ1 : β ≠ 1 := by
    intro hβ
    have hla : ggLAut J θ ⟨b, hN b.2⟩ = 1 := by
      rw [← congr_normalizerToCenterQuotientAut_eq_ggLAut (θ := θ) (b := b)]
      change MulAut.congr θ β = 1
      rw [hβ, map_one]
    have hc := mem_centralizer_of_ggLAut_eq_one J θ hperfJ (g := ⟨b, hN b.2⟩) hla
    exact hγb ((ggGamma_eq_one_iff J hN b).2 hc)
  have hrawβ : LargeEvenRawDatum labJ (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥J ⧸ Subgroup.center ↥J ≃* R, MulAut.congr θ β ∈ I) := by
    refine largeEvenRawDatum_imp hlabJ ?_ ?_ hrawJ
    · intro R _ I F h
      exact h.2.1
    · intro R instR I F h hmodel
      exact ⟨h.1, h.2.1, by
        obtain ⟨θ', hP'⟩ := h.2.2
        exact ⟨θ', by
          rw [congr_normalizerToCenterQuotientAut_eq_ggLAut (θ := θ') (b := b)]
          exact ggLAut_mem_of_induces J θ' hN hP'.2 b.2⟩⟩
  have hrawCanon : CFSG.Assembly.LargeEvenRawDatum labJ (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : ↥J ⧸ Subgroup.center ↥J ≃* R, MulAut.congr θ β ∈ I) := by
    refine largeEvenRawDatum_canonical_of_legacy_mono ?_
      ((largeEvenRawDatum_legacy labJ _).1 hrawβ)
    intro R instR I I' F hle hq
    obtain ⟨hs, hna, θ, hmem⟩ := hq
    exact ⟨hs, hna, θ, hle hmem⟩
  have hmarkβ : CFSG.Open.GLAMarking ↥J (fun _ _ _ I _ θ => MulAut.congr θ β ∈ I) :=
    ⟨hperfJ, labJ, hlabJ, hrawCanon⟩
  have hdvdZ : p ∣ Nat.card (↥J ⧸ Subgroup.center ↥J) :=
    CFSG.LocalAnalysis.GLTheoremA.T2021.t2021Layer_dvd_card hp hp2 hβp hβ1 hmarkβ
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥J)]
  exact dvd_mul_of_dvd_left hdvdZ _

theorem GGResHyp.exists_J_label
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) := by
  obtain ⟨-, labJ, -, -, -, hΛJ, -, hHasJ⟩ :=
    ggNbr_label_J_of_tcj TCJ.ggTCJKnown_holds hH.1 hH.2.2.2.2.1
  exact ⟨labJ, hΛJ, hHasJ⟩

theorem GGResHyp.exists_J_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      LargeEvenMarking ↥J (fun lab' _ _ _ _ _ => lab' = labJ) ∧
      GGInnerDiagOnLabel (fun _ lab' => lab' = labJ) p Bs J := by
  obtain ⟨hJperf, labJ, hΛJ, hraw⟩ :=
    ggBstarInnerDiagJInput_holds G p B Bs x L D J hH.1 hH.2.2.1.1
  have hMark : GGInnerDiagOnLabel (fun _ lab' => lab' = labJ) p Bs J := by
    refine ⟨hJperf, labJ, hΛJ, ?_⟩
    exact largeEvenRawDatum_mono (fun R _ I F h =>
      ⟨h.1, h.2.1, h.2.2.choose, rfl, h.2.2.choose_spec⟩) hraw
  exact ⟨labJ, hΛJ, largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hMark, hMark⟩

theorem GGResHyp.prime_dvd_card_J
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K) :
    p ∣ Nat.card J :=
  GGResHyp.prime_dvd_card_J_of_innerDiag hH
    (ggBstarInnerDiagJInput_holds G p B Bs x L D J hH.1 hH.2.2.1.1)

section CompatibleJMarking

theorem GGResHyp.exists_J_compatible_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    ∃ labJ : LargeEvenLabel, LargeEvenInLambda2 labJ ∧
      GGHasLabel labJ (J ⧸ Subgroup.center J) ∧
      GGInnerDiagOnLabel (fun _ lab => lab = labJ) p Bs J := by
  obtain ⟨labJ, hΛJ, hHasJ⟩ := GGResHyp.exists_J_label hH
  have hJ : GGInnerDiagOn Bs J :=
    ggBstarInnerDiagJInput_holds G p B Bs x L D J hH.1 hH.2.2.1.1
  exact ⟨labJ, hΛJ, hHasJ, ggInnerDiagOn_relabel ggLabelRigidInput_holds hJ hΛJ hHasJ⟩

end CompatibleJMarking

theorem GGResHyp.card_bstar_inf_center_J_le
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) :
    Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ p := by
  obtain ⟨labJ, hΛJ, hHasJ⟩ := GGResHyp.exists_J_label hH
  exact card_inf_center_le_of_hasLabel ggLabelCenterPCyclicInput_holds
    hH.1.1.2.2.2.2.2.1.1 hH.1.1.2.2.2.2.2.1.2.1
    hH.1.2.1.2.1 hH.1.2.2.1.2.2.2.2.2.1.2.2.1 hΛJ hHasJ

theorem GGResHyp.not_exists_inversion_mem_ggTorusWeylAut_of_lineJDatum_A3
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp : p = 3)
    (hD : GGResLineJDatum p Bs J .A3) :
    ¬ ∃ φ ∈ ggTorusWeylAut p (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range,
      ∀ a : ↥(ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range, φ a = a⁻¹ := by
  have hA2 : 2 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := by
    have h := GGResHyp.sq_le_card_gamma_J hH
    have hp2 : p ^ 2 = 9 := by rw [hp]; norm_num
    have h9 : 9 ≤ Nat.card (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range := hp2 ▸ h
    omega
  exact CFSG.StandardType.not_exists_inversion_mem_ggTorusWeylAut_of_lineJDatum_A3
    (p := p) (GGResHyp.Bs_le_normalizer_J hH)
    hH.1.2.1.2.1 hH.1.2.1.2.2.2 hH.2.2.2.1
    (GGResHyp.card_bstar_inf_center_J_le hH) hp hA2 hD

theorem GGResHyp.not_small_J_label_of_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    {lab : LargeEvenLabel} (hLambda : LargeEvenInLambda2 lab)
    (hhas : GGHasLabel lab (J ⧸ Subgroup.center J)) :
    ¬ (lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨
      lab.tag = .B2der ∨ lab.tag = .G2der ∨ lab.tag = .twF4der) := by
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hJperfI : Group.IsPerfect ↥J := Group.IsPerfect.mk hJperf
  obtain ⟨E, hEa, hEcard⟩ :=
    GGResLineJDatum.exists_coroot_quotient_of_A3 (GGResHyp.Bs_le_normalizer_J hH) hD
  exact ggSmallThreeRank_not_small_of_elemAbelian (H := ↥J) hLambda hhas hEa hEcard.ge

theorem GGResHyp.card_automizer_J_eq_symplectic_of_label
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {labJ : LargeEvenLabel}
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab = labJ ∧ (lab.tag = .B ∨ lab.tag = .C))
      3 Bs J) :
    Nat.card (ggAutomizer J Bs) = 2 ^ labJ.rank * labJ.rank.factorial := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlabLambda, hraw⟩ := hMark
  obtain ⟨R, _, I, F, hs, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have hlab : lab = labJ := hP.1.1
  have htag : lab.tag = .B ∨ lab.tag = .C := hP.1.2
  have hraw0 : LargeEvenRawDatum lab (fun R _ I F =>
      IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
        ∃ θ : J ⧸ Subgroup.center J ≃* R,
          (lab.tag = .B ∨ lab.tag = .C) ∧ Bs ≤ Subgroup.normalizer (J : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    exact ⟨hs, hna, θ, hP.1.2, hP.2⟩
  have hrawS : LargeEvenRecipeSymplectic lab.rank (2 ^ lab.n) false
      (fun R _ I F =>
        IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
          ∃ θ : J ⧸ Subgroup.center J ≃* R,
            (lab.tag = .B ∨ lab.tag = .C) ∧ Bs ≤ Subgroup.normalizer (J : Set G) ∧
            ∀ b ∈ Bs, ∃ φ ∈ I,
              LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) := by
    rcases htag with hB | hC
    · simpa only [LargeEvenRawDatum, hB] using hraw0
    · simpa only [LargeEvenRawDatum, hC] using hraw0
  have hn : 2 ≤ lab.rank := by
    rcases htag with hB | hC
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hB] using hlabLambda.2
      exact h.1
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hC] using hlabLambda.2
      exact h.1
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  obtain ⟨F, hField, hFinite, hF, -, -, θ, hP⟩ := hrawS
  let : Field F := hField
  let : Finite F := hFinite
  have : CharP F 2 := charP_two_of_card hF
  have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup F lab.rank))
        (LargeEvenGSpSet F lab.rank) :=
    fun b hb => ggLAut_mem_of_induces J θ hN hP.2.2 hb
  have hBp : ∀ b : Bs, b ^ 3 = 1 := fun b =>
    Subtype.ext (by simpa using hBs.2 (b : G) b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (TableB.IsElemAbelian.comm hBs a.2 b.2)
  have hAb : IsElemAbelian 3 (ggGamma J hN).range :=
    isElemAbelian_range hBc hBp (ggGamma J hN)
  have hAI : ∀ a ∈ (ggGamma J hN).range,
      ∃ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup F lab.rank))
        (LargeEvenGSpSet F lab.rank),
      ∀ l : J, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN b, hBI b b.2, fun l => ggBeta_ggQuotHom J hN θ b l⟩
  have hSelf : GGTorusSelfCent 3 (ggGamma J hN).range :=
    ggTorusSelfCent_ggGamma hN hSC
  have hf : 1 ≤ lab.n := hlabLambda.1
  have hq : 2 ≤ 2 ^ lab.n := le_self_pow₀ (by norm_num) (by omega)
  have hoddSub : Odd (2 ^ lab.n - 1) := by
    obtain ⟨a, ha⟩ := (show Even (2 ^ lab.n) from
      Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact ⟨a - 1, by omega⟩
  have hoddAdd : Odd (2 ^ lab.n + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hdiv : 3 ∣ 2 ^ lab.n - 1 ∨ 3 ∣ 2 ^ lab.n + 1 :=
    ggThree_dvd_two_pow_sub_or_add lab.n
  have hTor : GGTorusTorData (ggTorMpm 3 lab) lab.rank
      (CartanMatrix.C lab.rank) (CoxeterMatrix.B lab.rank) J (ggGamma J hN).range := by
    by_cases hpq : 3 ∣ 2 ^ lab.n - 1
    · have hD : Nonempty (TorC.SpTorusData F (2 ^ lab.n - 1) 3) := by
        have h := TorC.nonempty_spTorusData_split Nat.prime_three (by norm_num)
          (by rwa [hF])
        simpa [hF] using h
      rw [ggTorMpm, if_pos hpq]
      exact ggTorusTorData_symplectic_of_selfCentralizing hF hn hoddSub Nat.prime_three
        (by norm_num) hpq hD.some J (ggQuotHom θ) (ggQuotHom_surjective θ)
        (by rw [ker_ggQuotHom]) hJperf hAb hAI hSelf
    · have hpq' : 3 ∣ 2 ^ lab.n + 1 := hdiv.resolve_left hpq
      have hD : Nonempty (TorC.SpTorusData F (2 ^ lab.n + 1) 3) := by
        have h := TorC.nonempty_spTorusData_nonsplit Nat.prime_three (by norm_num)
          (by rwa [hF])
        simpa [hF] using h
      rw [ggTorMpm, if_neg hpq]
      exact ggTorusTorData_symplectic_of_selfCentralizing hF hn hoddAdd Nat.prime_three
        (by norm_num) hpq' hD.some J (ggQuotHom θ) (ggQuotHom_surjective θ)
        (by rw [ker_ggQuotHom]) hJperf hAb hAI hSelf
  have hodd : Odd (ggTorMpm 3 lab) := by
    unfold ggTorMpm
    split_ifs <;> assumption
  have hdvd : 3 ∣ ggTorMpm 3 lab := by
    unfold ggTorMpm
    split_ifs with hpq
    · exact hpq
    · exact hdiv.resolve_left hpq
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, hbk, Fins, _, _, _, _, _⟩ := ggTD_core hodd hdvd hBs hSC hN w hw
  have hweyl : ∃ e : (CoxeterMatrix.B lab.rank).Group ≃* ↥(ggAutomizer J Bs),
      ∀ k, (e ((CoxeterMatrix.B lab.rank).simple k) : MulAut ↥Bs) =
        ggTDρB J Bs (ggTDnH w hnk k) :=
    ggTD_weyl hN hw (by norm_num) hBs hnk
  obtain ⟨e, _⟩ := hweyl
  have hOrd : Nat.card (ggAutomizer J Bs) = Nat.card (CoxeterMatrix.B lab.rank).Group :=
    Nat.card_congr e.symm.toEquiv
  rw [ggCoxeterB_card lab.rank hn] at hOrd
  rw [hlab] at hOrd
  exact hOrd

theorem GGResHyp.actual_J_not_B_or_C_for_A2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A2)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) 3 Bs J) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlabLambda, hraw⟩ := hMark
  obtain ⟨R, _, I, F, hs, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have htag : lab.tag = .B ∨ lab.tag = .C := hP.1
  have hMark' : GGInnerDiagOnLabel
      (fun _ lab' => lab' = lab ∧ (lab'.tag = .B ∨ lab'.tag = .C)) 3 Bs J :=
    ⟨hJperf, lab, hlabLambda, largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, hP⟩ := h
      exact ⟨hs, hna, θ, ⟨⟨rfl, hP.1⟩, hP.2⟩⟩) hraw⟩
  have hcard := GGResHyp.card_automizer_J_eq_symplectic_of_label hH hMark'
  have h6 : Nat.card (ggAutomizer J Bs) = 6 :=
    ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
  rw [h6] at hcard
  have hn : 2 ≤ lab.rank := by
    rcases htag with hB | hC
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hB] using hlabLambda.2
      exact h.1
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hC] using hlabLambda.2
      exact h.1
  have h8 : 8 ≤ 2 ^ lab.rank * lab.rank.factorial := by
    have hpow : 4 ≤ 2 ^ lab.rank := by
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn
      norm_num at this ⊢
      exact this
    have hfact : 2 ≤ lab.rank.factorial := by
      have := Nat.factorial_le hn
      norm_num at this ⊢
      exact this
    exact Nat.mul_le_mul hpow hfact
  omega

theorem GGResHyp.actual_J_not_B_or_C_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) 3 Bs J) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlabLambda, hraw⟩ := hMark
  obtain ⟨R, _, I, F, hs, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have htag : lab.tag = .B ∨ lab.tag = .C := hP.1
  have hMark' : GGInnerDiagOnLabel
      (fun _ lab' => lab' = lab ∧ (lab'.tag = .B ∨ lab'.tag = .C)) 3 Bs J :=
    ⟨hJperf, lab, hlabLambda, largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, hP⟩ := h
      exact ⟨hs, hna, θ, ⟨⟨rfl, hP.1⟩, hP.2⟩⟩) hraw⟩
  have hcard := GGResHyp.card_automizer_J_eq_symplectic_of_label hH hMark'
  have h24 : Nat.card (ggAutomizer J Bs) = 24 :=
    ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
  rw [h24] at hcard
  have hn : 2 ≤ lab.rank := by
    rcases htag with hB | hC
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hB] using hlabLambda.2
      exact h.1
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hC] using hlabLambda.2
      exact h.1
  have hge : 2 ^ lab.rank * lab.rank.factorial ≠ 24 := by
    by_cases h : lab.rank = 2
    · rw [h]
      norm_num
    · have h3r : 3 ≤ lab.rank := by omega
      have hfact : 6 ≤ lab.rank.factorial := by
        have h : Nat.factorial 3 ≤ lab.rank.factorial := Nat.factorial_le h3r
        norm_num at h
        exact h
      have hpow : 8 ≤ 2 ^ lab.rank := by
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3r
        norm_num at this ⊢
        exact this
      have : 48 ≤ 2 ^ lab.rank * lab.rank.factorial := Nat.mul_le_mul hpow hfact
      omega
  exact hge hcard.symm

theorem GGResHyp.exists_lineJLabel_of_B2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .B2)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel .B2 lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlabLambda, hraw⟩ := hMark
  obtain ⟨R, _, I, F, hs, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have htag : lab.tag = .B ∨ lab.tag = .C := hP.1
  have hHas : GGHasLabel lab (J ⧸ Subgroup.center J) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, -⟩
    exact ⟨θ⟩
  have hMark' : GGInnerDiagOnLabel
      (fun _ lab' => lab' = lab ∧ (lab'.tag = .B ∨ lab'.tag = .C)) 3 Bs J :=
    ⟨hJperf, lab, hlabLambda, largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, hP⟩ := h
      exact ⟨hs, hna, θ, ⟨⟨rfl, hP.1⟩, hP.2⟩⟩) hraw⟩
  have hcard := GGResHyp.card_automizer_J_eq_symplectic_of_label hH hMark'
  have hcard8 : Nat.card (ggAutomizer J Bs) = 8 :=
    ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
  rw [hcard8] at hcard
  have hn : 2 ≤ lab.rank := by
    rcases htag with hB | hC
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hB] using hlabLambda.2
      exact h.1
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hC] using hlabLambda.2
      exact h.1
  have hrank : lab.rank = 2 := by
    have hle2 : lab.rank ≤ 2 := by
      by_contra hle
      have h3r : 3 ≤ lab.rank := by omega
      have hpow : 8 ≤ 2 ^ lab.rank := by
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h3r
        norm_num at this ⊢
        exact this
      have hfact : 6 ≤ lab.rank.factorial := by
        have h : Nat.factorial 3 ≤ lab.rank.factorial := Nat.factorial_le h3r
        norm_num at h
        exact h
      have : 48 ≤ 2 ^ lab.rank * lab.rank.factorial := Nat.mul_le_mul hpow hfact
      omega
    omega
  exact ⟨lab, hlabLambda, Or.inl ⟨htag, hrank⟩, hHas⟩

theorem GGResHyp.exists_lineJLabel_of_B3C3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {T : GGResLineJType} (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .B ∨ lab.tag = .C) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧ ggResLineJLabel T lab ∧
      GGHasLabel lab (J ⧸ Subgroup.center J) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlabLambda, hraw⟩ := hMark
  obtain ⟨R, _, I, F, hs, hna, θ, hP⟩ := largeEvenRawDatum_exists hraw
  have htag : lab.tag = .B ∨ lab.tag = .C := hP.1
  have hHas : GGHasLabel lab (J ⧸ Subgroup.center J) := by
    refine largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, -⟩
    exact ⟨θ⟩
  have hMark' : GGInnerDiagOnLabel
      (fun _ lab' => lab' = lab ∧ (lab'.tag = .B ∨ lab'.tag = .C)) 3 Bs J :=
    ⟨hJperf, lab, hlabLambda, largeEvenRawDatum_mono (fun R _ I F h => by
      obtain ⟨hs, hna, θ, hP⟩ := h
      exact ⟨hs, hna, θ, ⟨⟨rfl, hP.1⟩, hP.2⟩⟩) hraw⟩
  have hcard := GGResHyp.card_automizer_J_eq_symplectic_of_label hH hMark'
  have hn : 2 ≤ lab.rank := by
    rcases htag with hB | hC
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hB] using hlabLambda.2
      exact h.1
    · have h : 2 ≤ lab.rank ∧ (lab.rank = 2 → 2 ≤ lab.n) := by
        simpa only [hC] using hlabLambda.2
      exact h.1
  have hrank_of : ∀ r : ℕ, 2 ≤ r → 48 = 2 ^ r * r.factorial → r = 3 := by
    intro r hr h
    have hle3 : r ≤ 3 := by
      by_contra hle
      have h4 : 4 ≤ r := by omega
      have hpow : 16 ≤ 2 ^ r := by
        have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h4
        norm_num at this ⊢
        exact this
      have hfact : 24 ≤ r.factorial := by
        have := Nat.factorial_le h4
        norm_num at this ⊢
        exact this
      have : 384 ≤ 2 ^ r * r.factorial := Nat.mul_le_mul hpow hfact
      omega
    interval_cases r
    · norm_num at h
    · rfl
  rcases hT with rfl | rfl
  · have h48 : Nat.card (ggAutomizer J Bs) = 48 :=
      ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD
    rw [h48] at hcard
    exact ⟨lab, hlabLambda, Or.inl ⟨htag, hrank_of lab.rank hn hcard⟩, hHas⟩
  · have h48 : Nat.card (ggAutomizer J Bs) = 48 :=
      ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD
    rw [h48] at hcard
    exact ⟨lab, hlabLambda, Or.inl ⟨htag, hrank_of lab.rank hn hcard⟩, hHas⟩

theorem GGResHyp.card_automizer_J_eq_E7_or_E8_of_label
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) 3 Bs J) :
    ∃ lab : LargeEvenLabel, LargeEvenInLambda2 lab ∧
      ((lab.tag = .E7 ∧ Nat.card (ggAutomizer J Bs) = 2903040) ∨
       (lab.tag = .E8 ∧ Nat.card (ggAutomizer J Bs) = 696729600)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlabLambda, hraw⟩ := hMark
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨_, _, _, _, _, _, _, hP0⟩ := largeEvenRawDatum_exists hraw
  have htag : lab.tag = .E7 ∨ lab.tag = .E8 := hP0.1
  have hn1 : 1 ≤ lab.n := hlabLambda.1
  have hpow2 : 2 ≤ 2 ^ lab.n := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hn1
    simpa using this
  have hoddSub : Odd (2 ^ lab.n - 1) := by
    obtain ⟨a, ha⟩ := (show Even (2 ^ lab.n) from
      Nat.even_pow.mpr ⟨even_two, by omega⟩)
    rw [odd_iff_exists_bit1]
    exact ⟨a - 1, by omega⟩
  have hoddAdd : Odd (2 ^ lab.n + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hdiv : 3 ∣ 2 ^ lab.n - 1 ∨ 3 ∣ 2 ^ lab.n + 1 :=
    ggThree_dvd_two_pow_sub_or_add lab.n
  have hEnnLe : ggTorEnn 3 lab ≤ 1 := by
    unfold ggTorEnn
    split_ifs <;> norm_num
  rcases htag with hE7 | hE8
  · have hpdiv : 3 ∣ (2 ^ lab.n - 1) * (2 ^ lab.n + 1) := by
      rcases hdiv with h | h
      · exact dvd_mul_of_dvd_left h _
      · exact dvd_mul_of_dvd_right h _
    have hWl : LargeEvenLabelAll lab (fun R _ I _ =>
        GGTorusTorW 3 (7 - ggTorEnn 3 lab) (ggTorMpm 3 lab) 7
          (CartanMatrix.E 7) CoxeterMatrix.E₇ R I) :=
      ggTBTorE7_holds 3 Nat.prime_three (by norm_num) lab hlabLambda hE7 hpdiv
    have hLiftAll : LargeEvenLabelAll lab (fun R _ _ _ =>
        GGTorusLift 3 (7 - ggTorEnn 3 lab) R) := by
      obtain ⟨t, l, n⟩ := lab
      dsimp only at hE7
      subst hE7
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card hK
      by_cases hminus : 3 ∣ 2 ^ n - 1
      · have hplus : ¬ 3 ∣ 2 ^ n + 1 := by
          intro h
          have htwo : 3 ∣ 2 := by
            have hsub := Nat.dvd_sub h hminus
            have hpow1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
            have hval : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
              rw [show 2 ^ n = (2 ^ n - 1) + 1 from (Nat.sub_add_cancel hpow1).symm]
              omega
            rwa [hval] at hsub
          norm_num at htwo
        have hEnn : ggTorEnn 3 ⟨.E7, l, n⟩ = 0 := by simp [ggTorEnn, hplus]
        have hpq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact hminus
        exact ⟨K, inferInstance, inferInstance, hK, hQ', by
          rw [hEnn]
          exact TableBExc.ggTorusLift_E7 (K := K) Nat.prime_three (by norm_num) hpq⟩
      · have hplus : 3 ∣ 2 ^ n + 1 := (ggThree_dvd_two_pow_sub_or_add n).resolve_left hminus
        have hEnn : ggTorEnn 3 ⟨.E7, l, n⟩ = 1 := by simp [ggTorEnn, hplus]
        have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; exact hplus
        exact ⟨K, inferInstance, inferInstance, hK, hQ', by
          rw [hEnn]
          exact ggTorusLift_E7Plus (K := K) Nat.prime_three (by norm_num) hpq⟩
    have hBoth := largeEvenLabelAll_and hWl hLiftAll
    obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
    obtain ⟨-, -, θ, _, _, hBsI⟩ := hQ
    have hr : 3 ^ (7 - ggTorEnn 3 lab) ≤ Nat.card (ggGamma J hN).range :=
      GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hlift
    have hExp : 3 ≤ 7 - ggTorEnn 3 lab := by omega
    have h3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
      (Nat.pow_le_pow_right (by norm_num : 0 < 3) hExp).trans hr
    have hTB : GGTorusTBGroup 3 (7 - ggTorEnn 3 lab) R I J (ggQuotHom θ)
        (ggGamma J hN).range :=
      ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN
        (fun b hb => ggLAut_mem_of_induces J θ hN hBsI hb)
        hr h3
    have hTor := hWtor ↥J (ggQuotHom θ) (ggGamma J hN).range hTB
    have hodd : Odd (ggTorMpm 3 lab) := by
      unfold ggTorMpm
      split_ifs <;> assumption
    have hdvd : 3 ∣ ggTorMpm 3 lab := by
      unfold ggTorMpm
      split_ifs with hpq
      · exact hpq
      · exact hdiv.resolve_left hpq
    obtain ⟨w, hw⟩ := hTor
    obtain ⟨hnk, _, _, _, _, _, _, _⟩ := ggTD_core hodd hdvd hBs hSC hN w hw
    obtain ⟨e, _⟩ := ggTD_weyl hN hw (by norm_num) hBs hnk
    have hOrd : Nat.card (ggAutomizer J Bs) = Nat.card (CoxeterMatrix.E₇).Group :=
      Nat.card_congr e.symm.toEquiv
    have hOrdE7 : Nat.card (ggAutomizer J Bs) = 2903040 := by
      rw [card_coxeterE7_group] at hOrd
      exact hOrd
    exact ⟨lab, hlabLambda, Or.inl ⟨hE7, hOrdE7⟩⟩
  · have hWl : LargeEvenLabelAll lab (fun R _ I _ =>
        GGTorusTorW 3 (8 - ggTorEnn 3 lab) (ggTorME8 lab) 8
          CartanMatrix.E₈ CoxeterMatrix.E₈ R I) :=
      ggTBTorE8_holds lab hlabLambda hE8
    have hLiftAll : LargeEvenLabelAll lab (fun R _ _ _ =>
        GGTorusLift 3 (8 - ggTorEnn 3 lab) R) := by
      obtain ⟨t, l, n⟩ := lab
      dsimp only at hE8
      subst hE8
      intro Q hQ
      obtain ⟨K, _, _, hK, hQ'⟩ := hQ
      have : CharP K 2 := charP_two_of_card hK
      by_cases hminus : 3 ∣ 2 ^ n - 1
      · have hplus : ¬ 3 ∣ 2 ^ n + 1 := by
          intro h
          have htwo : 3 ∣ 2 := by
            have hsub := Nat.dvd_sub h hminus
            have hpow1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
            have hval : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by
              rw [show 2 ^ n = (2 ^ n - 1) + 1 from (Nat.sub_add_cancel hpow1).symm]
              omega
            rwa [hval] at hsub
          norm_num at htwo
        have hEnn : ggTorEnn 3 ⟨.E8, l, n⟩ = 0 := by simp [ggTorEnn, hplus]
        have hpq : 3 ∣ Nat.card K - 1 := by rw [hK]; exact hminus
        exact ⟨K, inferInstance, inferInstance, hK, hQ', by
          rw [hEnn]
          exact TableBExc.ggTorusLift_E8 (K := K) Nat.prime_three (by norm_num) hpq⟩
      · have hplus : 3 ∣ 2 ^ n + 1 := (ggThree_dvd_two_pow_sub_or_add n).resolve_left hminus
        have hEnn : ggTorEnn 3 ⟨.E8, l, n⟩ = 1 := by simp [ggTorEnn, hplus]
        have hpq : 3 ∣ Nat.card K + 1 := by rw [hK]; exact hplus
        exact ⟨K, inferInstance, inferInstance, hK, hQ', by
          rw [hEnn]
          exact ggTorusLift_E8Plus (K := K) Nat.prime_three (by norm_num) hpq⟩
    have hBoth := largeEvenLabelAll_and hWl hLiftAll
    obtain ⟨R, _instR, I, F, hQ, hWtor, hlift⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
    obtain ⟨-, -, θ, _, _, hBsI⟩ := hQ
    have hr : 3 ^ (8 - ggTorEnn 3 lab) ≤ Nat.card (ggGamma J hN).range :=
      GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hlift
    have hExp : 3 ≤ 8 - ggTorEnn 3 lab := by omega
    have h3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
      (Nat.pow_le_pow_right (by norm_num : 0 < 3) hExp).trans hr
    have hTB : GGTorusTBGroup 3 (8 - ggTorEnn 3 lab) R I J (ggQuotHom θ)
        (ggGamma J hN).range :=
      ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN
        (fun b hb => ggLAut_mem_of_induces J θ hN hBsI hb)
        hr h3
    have hTor := hWtor ↥J (ggQuotHom θ) (ggGamma J hN).range hTB
    have hodd : Odd (ggTorME8 lab) := by
      unfold ggTorME8
      split_ifs <;> assumption
    have hdvd : 3 ∣ ggTorME8 lab := by
      unfold ggTorME8
      split_ifs with hpq
      · exact hpq
      · exact hdiv.resolve_left hpq
    obtain ⟨w, hw⟩ := hTor
    obtain ⟨hnk, _, _, _, _, _, _, _⟩ := ggTD_core hodd hdvd hBs hSC hN w hw
    obtain ⟨e, _⟩ := ggTD_weyl hN hw (by norm_num) hBs hnk
    have hOrd : Nat.card (ggAutomizer J Bs) = Nat.card (CoxeterMatrix.E₈).Group :=
      Nat.card_congr e.symm.toEquiv
    have hOrdE8 : Nat.card (ggAutomizer J Bs) = 696729600 := by
      rw [card_coxeterE8_group] at hOrd
      exact hOrd
    exact ⟨lab, hlabLambda, Or.inr ⟨hE8, hOrdE8⟩⟩

theorem GGResHyp.actual_J_not_E7_or_E8_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) 3 Bs J) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h24 : Nat.card (ggAutomizer J Bs) = 24 :=
    ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
  obtain ⟨_, _, h | h⟩ := GGResHyp.card_automizer_J_eq_E7_or_E8_of_label hH hMark
  · obtain ⟨_, hOrd⟩ := h
    rw [h24] at hOrd
    norm_num at hOrd
  · obtain ⟨_, hOrd⟩ := h
    rw [h24] at hOrd
    norm_num at hOrd

theorem GGResHyp.actual_J_not_E7_or_E8_of_line
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .A2 ∨ T = .B2 ∨ T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .E7 ∨ lab.tag = .E8) 3 Bs J) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle48 : Nat.card (ggAutomizer J Bs) ≤ 48 := by
    rcases hT with rfl | rfl | rfl | rfl
    · have h := ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
      omega
    · have h := ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
      omega
    · have h := ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD
      omega
    · have h := ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD
      omega
  obtain ⟨_, _, h | h⟩ := GGResHyp.card_automizer_J_eq_E7_or_E8_of_label hH hMark
  · obtain ⟨_, hOrd⟩ := h
    omega
  · obtain ⟨_, hOrd⟩ := h
    omega

@[expose] def GGResLineJType.highDTwDRank : GGResLineJType → ℕ
  | .A2 | .B2 | .A3 => 4
  | .B3 | .C3 => 5

theorem GGResHyp.card_automizer_eq_coxeter_of_torusLift
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hJperf : commutator ↥J = ⊤)
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R)
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I)
    {m N : ℕ} (hm3 : 3 ≤ m) (hLift : GGTorusLift 3 m R)
    {Mval : ℕ} (hodd : Odd Mval) (hpm : 3 ∣ Mval)
    {C : Matrix (Fin N) (Fin N) ℤ} {M : CoxeterMatrix (Fin N)}
    (hTorW : GGTorusTorW 3 m Mval N C M R I) :
    Nat.card (ggAutomizer J Bs) = Nat.card M.Group := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hgamma : ggGamma J hN = ggGamma J (GGResHyp.Bs_le_normalizer_J hH) := by
    ext b
    rfl
  have hr0 := GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hLift
  rw [← hgamma] at hr0
  have hr : 3 ^ m ≤ Nat.card (ggGamma J hN).range := hr0
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
    (Nat.pow_le_pow_right (by norm_num : 0 < 3) hm3).trans hr
  have hTB : GGTorusTBGroup 3 m R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN hBI hr h3
  obtain ⟨w, hw⟩ := hTorW ↥J (ggQuotHom θ) (ggGamma J hN).range hTB
  obtain ⟨hnk, _, _, _, _, _, _, _⟩ := ggTD_core hodd hpm hBs hSC hN w hw
  obtain ⟨e, _⟩ := ggTD_weyl hN hw (by norm_num) hBs hnk
  exact Nat.card_congr e.symm.toEquiv

theorem GGResHyp.actual_J_not_D_high_or_twD_split_of_line
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hMark : GGInnerDiagOnLabel (fun _ lab => 3 ∣ 2 ^ lab.n - 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ T.highDTwDRank ≤ lab.rank))) 3 Bs J) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlabLambda, hraw⟩ := hMark
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, θ₀, hP₀⟩ := hQ₀
  have hpq : 3 ∣ 2 ^ lab.n - 1 := hP₀.1.1
  have hcase : (lab.tag = .D ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ T.highDTwDRank ≤ lab.rank) := hP₀.1.2
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hle48 : Nat.card (ggAutomizer J Bs) ≤ 48 := by
    cases T with
    | A2 => have h := ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD; omega
    | B2 => have h := ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD; omega
    | A3 => have h := ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD; omega
    | B3 => have h := ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD; omega
    | C3 => have h := ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD; omega
  have hle24 : T = .A2 ∨ T = .B2 ∨ T = .A3 → Nat.card (ggAutomizer J Bs) ≤ 24 := by
    rintro (rfl | rfl | rfl)
    · have h := ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD; omega
    · have h := ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD; omega
    · have h := ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD; omega
  have hle48BC : T = .B3 ∨ T = .C3 → Nat.card (ggAutomizer J Bs) ≤ 48 := by
    rintro (rfl | rfl)
    · have h := ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD; omega
    · have h := ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD; omega
  have h4 : 4 ≤ lab.rank := by
    rcases hcase with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · have hfloor : 4 ≤ T.highDTwDRank := by cases T <;> decide
      exact hfloor.trans h
  have hX192 : 192 ≤ 2 ^ (lab.rank - 1) * lab.rank.factorial := by
    have hpow : 8 ≤ 2 ^ (lab.rank - 1) := by
      have h1 : 3 ≤ lab.rank - 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      norm_num at this
      exact this
    have hfact : 24 ≤ lab.rank.factorial := by
      have h := Nat.factorial_le h4
      norm_num at h
      exact h
    calc 192 = 8 * 24 := by norm_num
      _ ≤ 2 ^ (lab.rank - 1) * lab.rank.factorial := Nat.mul_le_mul hpow hfact
  have hY48 : 48 ≤ 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial := by
    have hpow : 8 ≤ 2 ^ (lab.rank - 1) := by
      have h1 : 3 ≤ lab.rank - 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      norm_num at this
      exact this
    have hfact : 6 ≤ (lab.rank - 1).factorial := by
      have h := Nat.factorial_le (by omega : 3 ≤ lab.rank - 1)
      norm_num at h
      exact h
    calc 48 = 8 * 6 := by norm_num
      _ ≤ 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial := Nat.mul_le_mul hpow hfact
  have hY384 : 5 ≤ lab.rank →
      384 ≤ 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial := by
    intro h5
    have hpow : 16 ≤ 2 ^ (lab.rank - 1) := by
      have h1 : 4 ≤ lab.rank - 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      norm_num at this
      exact this
    have hfact : 24 ≤ (lab.rank - 1).factorial := by
      have h := Nat.factorial_le (by omega : 4 ≤ lab.rank - 1)
      norm_num at h
      exact h
    calc 384 = 16 * 24 := by norm_num
      _ ≤ 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial := Nat.mul_le_mul hpow hfact
  have hf : 1 ≤ lab.n := hlabLambda.1
  have hq : 2 ≤ 2 ^ lab.n := le_self_pow₀ (by norm_num) (by omega)
  have hoddSub : Odd (2 ^ lab.n - 1) := by
    obtain ⟨a, ha⟩ := (show Even (2 ^ lab.n) from
      Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact ⟨a - 1, by omega⟩
  have hoddAdd : Odd (2 ^ lab.n + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hdiv : 3 ∣ 2 ^ lab.n - 1 ∨ 3 ∣ 2 ^ lab.n + 1 :=
    ggThree_dvd_two_pow_sub_or_add lab.n
  have hodd : Odd (ggTorMpm 3 lab) := by
    unfold ggTorMpm
    split_ifs <;> assumption
  have hdvd : 3 ∣ ggTorMpm 3 lab := by
    unfold ggTorMpm
    by_cases h : 3 ∣ 2 ^ lab.n - 1
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact hdiv.resolve_left h
  have hEnn : ggTorEnn 3 lab = 0 := by
    unfold ggTorEnn
    rw [if_neg]
    intro h
    have h2 : 3 ∣ (2 ^ lab.n + 1) - (2 ^ lab.n - 1) := Nat.dvd_sub h hpq
    have hq1 : 1 ≤ 2 ^ lab.n := Nat.one_le_two_pow
    have heq : (2 ^ lab.n + 1) - (2 ^ lab.n - 1) = 2 := by omega
    rw [heq] at h2
    norm_num at h2
  rcases hcase with ⟨hDtag, hrank⟩ | ⟨htwDtag, hfloor⟩
  ·
    have hLiftAll := largeEvenLabelAll_torusLift_D hDtag hlabLambda hrank Nat.prime_three hpq
    have hTorAll := ggTBTorDHigh_split Nat.prime_three (by norm_num) hlabLambda hrank hDtag hpq
    have hBoth := largeEvenLabelAll_and hLiftAll hTorAll
    obtain ⟨R, _, I, _, hQ⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
    obtain ⟨hQ', hLift, hTorW⟩ := hQ
    obtain ⟨_, _, θ, hP⟩ := hQ'
    have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
      fun b hb => ggLAut_mem_of_induces J θ hN hP.2.2 hb
    have hcard : Nat.card (ggAutomizer J Bs) =
        Nat.card (ggCoxeterMatrixD lab.rank).Group :=
      GGResHyp.card_automizer_eq_coxeter_of_torusLift hH hJperf θ hN hBI
        (by omega : 3 ≤ lab.rank) (by simpa [hEnn] using hLift)
        hodd hdvd (by simpa [hEnn] using hTorW)
    have hcardD := OrthF3.card_coxeterD_eq lab.rank hrank
    have hX : 192 ≤ Nat.card (ggAutomizer J Bs) := by
      rw [hcard, hcardD]
      exact hX192
    omega
  ·
    have hLiftAll := largeEvenLabelAll_torusLift_twD htwDtag hlabLambda h4
      Nat.prime_three hpq
    have hTorAll : LargeEvenLabelAll lab (fun R _ I _ =>
        GGTorusTorW 3 (lab.rank - 1) (ggTorMpm 3 lab) (lab.rank - 1)
          (CartanMatrix.B (lab.rank - 1)) (CoxeterMatrix.B (lab.rank - 1)) R I) := by
      obtain ⟨t, l, n⟩ := lab
      simp only at htwDtag
      subst htwDtag
      exact largeEvenLabelAll_relD_twD_split (p := 3) (n := n) (ℓ := l)
        Nat.prime_three (by norm_num) hlabLambda.1 h4 hpq
    have hBoth := largeEvenLabelAll_and hLiftAll hTorAll
    obtain ⟨R, _, I, _, hQ⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
    obtain ⟨hQ', hLift, hTorW⟩ := hQ
    obtain ⟨_, _, θ, hP⟩ := hQ'
    have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
      fun b hb => ggLAut_mem_of_induces J θ hN hP.2.2 hb
    have hcard : Nat.card (ggAutomizer J Bs) =
        Nat.card (CoxeterMatrix.B (lab.rank - 1)).Group :=
      GGResHyp.card_automizer_eq_coxeter_of_torusLift hH hJperf θ hN hBI
        (by omega : 3 ≤ lab.rank - 1) hLift hodd hdvd hTorW
    have hcardB := ggCoxeterB_card (lab.rank - 1) (by omega : 2 ≤ lab.rank - 1)
    have hY : 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial ≤
        Nat.card (ggAutomizer J Bs) := by
      rw [hcard, hcardB]
    by_cases hBC : T = .B3 ∨ T = .C3
    · have h5 : 5 ≤ lab.rank := by
        rcases hBC with rfl | rfl <;> simpa [GGResLineJType.highDTwDRank] using hfloor
      have h384 : 384 ≤ Nat.card (ggAutomizer J Bs) := (hY384 h5).trans hY
      omega
    · have h24 : Nat.card (ggAutomizer J Bs) ≤ 24 := by
        cases T with
        | A2 => exact hle24 (Or.inl rfl)
        | B2 => exact hle24 (Or.inr (Or.inl rfl))
        | A3 => exact hle24 (Or.inr (Or.inr rfl))
        | B3 => exact absurd (Or.inl rfl) hBC
        | C3 => exact absurd (Or.inr rfl) hBC
      have h48 : 48 ≤ Nat.card (ggAutomizer J Bs) := hY48.trans hY
      omega

theorem GGResHyp.actual_J_not_D_high_or_twD_split_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => 3 ∣ 2 ^ lab.n - 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank))) 3 Bs J) :
    False :=
  GGResHyp.actual_J_not_D_high_or_twD_split_of_line hH hD
    (by simpa [GGResLineJType.highDTwDRank] using hMark)

theorem GGResHyp.actual_J_not_D_high_or_twD_nonsplit_of_line
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hMark : GGInnerDiagOnLabel (fun _ lab => 3 ∣ 2 ^ lab.n + 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ T.highDTwDRank ≤ lab.rank))) 3 Bs J) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlabLambda, hraw⟩ := hMark
  obtain ⟨R₀, _, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, θ₀, hP₀⟩ := hQ₀
  have hpn : 3 ∣ 2 ^ lab.n + 1 := hP₀.1.1
  have hcase : (lab.tag = .D ∧ 4 ≤ lab.rank) ∨
      (lab.tag = .twD ∧ T.highDTwDRank ≤ lab.rank) := hP₀.1.2
  have hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hle48 : Nat.card (ggAutomizer J Bs) ≤ 48 := by
    cases T with
    | A2 => have h := ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD; omega
    | B2 => have h := ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD; omega
    | A3 => have h := ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD; omega
    | B3 => have h := ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD; omega
    | C3 => have h := ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD; omega
  have hle24 : T = .A2 ∨ T = .B2 ∨ T = .A3 → Nat.card (ggAutomizer J Bs) ≤ 24 := by
    rintro (rfl | rfl | rfl)
    · have h := ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD; omega
    · have h := ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD; omega
    · have h := ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD; omega
  have hle48BC : T = .B3 ∨ T = .C3 → Nat.card (ggAutomizer J Bs) ≤ 48 := by
    rintro (rfl | rfl)
    · have h := ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD; omega
    · have h := ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD; omega
  have h4 : 4 ≤ lab.rank := by
    rcases hcase with ⟨_, h⟩ | ⟨_, h⟩
    · exact h
    · have hfloor : 4 ≤ T.highDTwDRank := by cases T <;> decide
      exact hfloor.trans h
  have hX192 : 192 ≤ 2 ^ (lab.rank - 1) * lab.rank.factorial := by
    have hpow : 8 ≤ 2 ^ (lab.rank - 1) := by
      have h1 : 3 ≤ lab.rank - 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      norm_num at this
      exact this
    have hfact : 24 ≤ lab.rank.factorial := by
      have h := Nat.factorial_le h4
      norm_num at h
      exact h
    calc 192 = 8 * 24 := by norm_num
      _ ≤ 2 ^ (lab.rank - 1) * lab.rank.factorial := Nat.mul_le_mul hpow hfact
  have hX384 : 5 ≤ lab.rank → 384 ≤ 2 ^ (lab.rank - 1) * lab.rank.factorial := by
    intro h5
    have hpow : 16 ≤ 2 ^ (lab.rank - 1) := by
      have h1 : 4 ≤ lab.rank - 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      norm_num at this
      exact this
    have hfact : 24 ≤ lab.rank.factorial := by
      have h := Nat.factorial_le (by omega : 4 ≤ lab.rank)
      norm_num at h
      exact h
    calc 384 = 16 * 24 := by norm_num
      _ ≤ 2 ^ (lab.rank - 1) * lab.rank.factorial := Nat.mul_le_mul hpow hfact
  have hY48 : 48 ≤ 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial := by
    have hpow : 8 ≤ 2 ^ (lab.rank - 1) := by
      have h1 : 3 ≤ lab.rank - 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      norm_num at this
      exact this
    have hfact : 6 ≤ (lab.rank - 1).factorial := by
      have h := Nat.factorial_le (by omega : 3 ≤ lab.rank - 1)
      norm_num at h
      exact h
    calc 48 = 8 * 6 := by norm_num
      _ ≤ 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial := Nat.mul_le_mul hpow hfact
  have hY384 : 5 ≤ lab.rank →
      384 ≤ 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial := by
    intro h5
    have hpow : 16 ≤ 2 ^ (lab.rank - 1) := by
      have h1 : 4 ≤ lab.rank - 1 := by omega
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) h1
      norm_num at this
      exact this
    have hfact : 24 ≤ (lab.rank - 1).factorial := by
      have h := Nat.factorial_le (by omega : 4 ≤ lab.rank - 1)
      norm_num at h
      exact h
    calc 384 = 16 * 24 := by norm_num
      _ ≤ 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial := Nat.mul_le_mul hpow hfact
  have hf : 1 ≤ lab.n := hlabLambda.1
  have hq : 2 ≤ 2 ^ lab.n := le_self_pow₀ (by norm_num) (by omega)
  have hoddSub : Odd (2 ^ lab.n - 1) := by
    obtain ⟨a, ha⟩ := (show Even (2 ^ lab.n) from
      Nat.even_pow.mpr ⟨even_two, by omega⟩)
    exact ⟨a - 1, by omega⟩
  have hoddAdd : Odd (2 ^ lab.n + 1) :=
    (Nat.even_pow.mpr ⟨even_two, by omega⟩).add_one
  have hdiv : 3 ∣ 2 ^ lab.n - 1 ∨ 3 ∣ 2 ^ lab.n + 1 :=
    ggThree_dvd_two_pow_sub_or_add lab.n
  have hodd : Odd (ggTorMpm 3 lab) := by
    unfold ggTorMpm
    split_ifs <;> assumption
  have hdvd : 3 ∣ ggTorMpm 3 lab := by
    unfold ggTorMpm
    by_cases h : 3 ∣ 2 ^ lab.n - 1
    · rw [if_pos h]
      exact h
    · rw [if_neg h]
      exact hdiv.resolve_left h
  have hEnn : ggTorEnn 3 lab = 1 := by
    unfold ggTorEnn
    rw [if_pos hpn]
  rcases hcase with ⟨hDtag, hrank⟩ | ⟨htwDtag, hfloor⟩
  ·
    by_cases heven : Even lab.rank
    ·
      have hTorAll := ggTBTorDHigh_nonsplit 3 Nat.prime_three (by norm_num) lab hlabLambda
        hrank hpn (Or.inl ⟨hDtag, heven⟩)
      have hLiftAll := largeEvenLabelAll_torusLift_D_nonsplit hDtag hrank
        Nat.prime_three (by norm_num) hpn
      have hBoth := largeEvenLabelAll_and hLiftAll hTorAll
      obtain ⟨R, _, I, _, hQ⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
      obtain ⟨hQ', hLift, hTorW⟩ := hQ
      obtain ⟨_, _, θ, hP⟩ := hQ'
      have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
        fun b hb => ggLAut_mem_of_induces J θ hN hP.2.2 hb
      have hcard : Nat.card (ggAutomizer J Bs) =
          Nat.card (ggCoxeterMatrixD lab.rank).Group :=
        GGResHyp.card_automizer_eq_coxeter_of_torusLift hH hJperf θ hN hBI
          (by omega : 3 ≤ lab.rank - 1) (by simpa [hEnn] using hLift)
          hodd hdvd (by simpa [hEnn] using hTorW)
      have hcardD := OrthF3.card_coxeterD_eq lab.rank hrank
      have hX : 192 ≤ Nat.card (ggAutomizer J Bs) := by
        rw [hcard, hcardD]
        exact hX192
      omega
    ·
      have hoddl : Odd lab.rank := Nat.not_even_iff_odd.mp heven
      have h5 : 5 ≤ lab.rank := by
        obtain ⟨j, hj⟩ := hoddl
        omega
      have hTorAll := ggTBTorRelD_holds 3 Nat.prime_three (by norm_num) lab hlabLambda
        (Or.inl ⟨hDtag, hpn, hoddl⟩)
      have hLiftAll := largeEvenLabelAll_torusLift_D_nonsplit hDtag hrank
        Nat.prime_three (by norm_num) hpn
      have hBoth := largeEvenLabelAll_and hLiftAll hTorAll
      obtain ⟨R, _, I, _, hQ⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
      obtain ⟨hQ', hLift, hTorW⟩ := hQ
      obtain ⟨_, _, θ, hP⟩ := hQ'
      have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
        fun b hb => ggLAut_mem_of_induces J θ hN hP.2.2 hb
      have hcard : Nat.card (ggAutomizer J Bs) =
          Nat.card (CoxeterMatrix.B (lab.rank - 1)).Group :=
        GGResHyp.card_automizer_eq_coxeter_of_torusLift hH hJperf θ hN hBI
          (by omega : 3 ≤ lab.rank - 1) hLift hodd hdvd hTorW
      have hcardB := ggCoxeterB_card (lab.rank - 1) (by omega : 2 ≤ lab.rank - 1)
      have hY : 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial ≤
          Nat.card (ggAutomizer J Bs) := by
        rw [hcard, hcardB]
      have h384 : 384 ≤ Nat.card (ggAutomizer J Bs) := (hY384 h5).trans hY
      omega
  ·
    have hLiftAll : LargeEvenLabelAll lab (fun R _ _ _ => GGTorusLift 3 (lab.rank - 1) R) := by
      obtain ⟨t, l, n⟩ := lab
      simp only at htwDtag
      subst htwDtag
      have h4l : 4 ≤ l := by simpa using h4
      intro Q hQ
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      split_ifs at hQ ⊢ with h2 h3
      · omega
      · omega
      obtain ⟨K, hKfield, hKfin, hKcard, b, c, hbc, hQ'⟩ := hQ
      let : Field K := hKfield
      let : Finite K := hKfin
      have : CharP K 2 := charP_two_of_card hKcard
      exact ⟨K, inferInstance, inferInstance, hKcard, b, c, hbc, hQ',
        ggOrthRestTorusLiftInput_holds.1 K n (l - 1) 3 b c hKcard (by omega)
          Nat.prime_three hpn hbc⟩
    by_cases heven : Even lab.rank
    ·
      have hTorAll := ggTBTorRelD_holds 3 Nat.prime_three (by norm_num) lab hlabLambda
        (Or.inr ⟨htwDtag, Or.inr ⟨hpn, heven⟩⟩)
      have hBoth := largeEvenLabelAll_and hLiftAll hTorAll
      obtain ⟨R, _, I, _, hQ⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
      obtain ⟨hQ', hLift, hTorW⟩ := hQ
      obtain ⟨_, _, θ, hP⟩ := hQ'
      have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
        fun b hb => ggLAut_mem_of_induces J θ hN hP.2.2 hb
      have hcard : Nat.card (ggAutomizer J Bs) =
          Nat.card (CoxeterMatrix.B (lab.rank - 1)).Group :=
        GGResHyp.card_automizer_eq_coxeter_of_torusLift hH hJperf θ hN hBI
          (by omega : 3 ≤ lab.rank - 1) hLift hodd hdvd hTorW
      have hcardB := ggCoxeterB_card (lab.rank - 1) (by omega : 2 ≤ lab.rank - 1)
      have hY : 2 ^ (lab.rank - 1) * (lab.rank - 1).factorial ≤
          Nat.card (ggAutomizer J Bs) := by
        rw [hcard, hcardB]
      by_cases hBC : T = .B3 ∨ T = .C3
      · have h5 : 5 ≤ lab.rank := by
          rcases hBC with rfl | rfl <;> simpa [GGResLineJType.highDTwDRank] using hfloor
        have h384 : 384 ≤ Nat.card (ggAutomizer J Bs) := (hY384 h5).trans hY
        omega
      · have h24 : Nat.card (ggAutomizer J Bs) ≤ 24 := by
          cases T with
          | A2 => exact hle24 (Or.inl rfl)
          | B2 => exact hle24 (Or.inr (Or.inl rfl))
          | A3 => exact hle24 (Or.inr (Or.inr rfl))
          | B3 => exact absurd (Or.inl rfl) hBC
          | C3 => exact absurd (Or.inr rfl) hBC
        have h48 : 48 ≤ Nat.card (ggAutomizer J Bs) := hY48.trans hY
        omega
    ·
      have hoddl : Odd lab.rank := Nat.not_even_iff_odd.mp heven
      have h5 : 5 ≤ lab.rank := by
        obtain ⟨j, hj⟩ := hoddl
        omega
      have hTorAll := ggTBTorDHigh_nonsplit 3 Nat.prime_three (by norm_num) lab hlabLambda
        h4 hpn (Or.inr ⟨htwDtag, hoddl⟩)
      have hBoth := largeEvenLabelAll_and hLiftAll hTorAll
      obtain ⟨R, _, I, _, hQ⟩ := largeEvenRawDatum_exists (hBoth _ hraw)
      obtain ⟨hQ', hLift, hTorW⟩ := hQ
      obtain ⟨_, _, θ, hP⟩ := hQ'
      have hBI : ∀ b (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
        fun b hb => ggLAut_mem_of_induces J θ hN hP.2.2 hb
      have hcard : Nat.card (ggAutomizer J Bs) =
          Nat.card (ggCoxeterMatrixD lab.rank).Group :=
        GGResHyp.card_automizer_eq_coxeter_of_torusLift hH hJperf θ hN hBI
          (by omega : 3 ≤ lab.rank - 1) (by simpa [hEnn] using hLift)
          hodd hdvd (by simpa [hEnn] using hTorW)
      have hcardD := OrthF3.card_coxeterD_eq lab.rank h4
      have hX : 384 ≤ Nat.card (ggAutomizer J Bs) := by
        rw [hcard, hcardD]
        exact hX384 h5
      omega

theorem GGResHyp.actual_J_not_D_high_or_twD_nonsplit_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel (fun _ lab => 3 ∣ 2 ^ lab.n + 1 ∧
      ((lab.tag = .D ∧ 4 ≤ lab.rank) ∨ (lab.tag = .twD ∧ 4 ≤ lab.rank))) 3 Bs J) :
    False :=
  GGResHyp.actual_J_not_D_high_or_twD_nonsplit_of_line hH hD
    (by simpa [GGResLineJType.highDTwDRank] using hMark)

theorem GGResHyp.card_automizer_J_eq_E6_split_of_label
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    Nat.card (ggAutomizer J Bs) = 51840 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlab, hraw⟩ := hMark
  have hraw0 := hraw
  obtain ⟨_, _, _, _, hq0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP0⟩ := hq0
  obtain ⟨⟨htag, h3n⟩, _, _⟩ := hP0
  have hLiftAll : LargeEvenLabelAll lab fun R _ _ _ => GGTorusLift 3 5 R :=
    largeEvenLabelAll_torusLift_E6_three htag h3n
  have hTorAll : LargeEvenLabelAll lab fun R _ I _ =>
      GGTorusTorW 3 5 (ggTorM lab) 6 CartanMatrix.E₆ CoxeterMatrix.E₆ R I := by
    have h3m : 3 ∣ ggTorM lab := by simpa [ggTorM, htag] using h3n
    exact ggTBTorE6_holds lab hlab htag h3m
  have hrawAll := (largeEvenLabelAll_and hLiftAll hTorAll) _ hraw0
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hrawAll
  obtain ⟨⟨hs, hna, θ, hP⟩, hLift, hTorW⟩ := hq
  obtain ⟨⟨htag, h3n⟩, hN, hBsI⟩ := hP
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBI : ∀ (b : G) (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces J θ hN hBsI hb
  have hr : 3 ^ 5 ≤ Nat.card (ggGamma J hN).range :=
    GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hLift
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
    (show 3 ^ 3 ≤ 3 ^ 5 by norm_num).trans hr
  have hTB : GGTorusTBGroup 3 5 R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN hBI hr h3
  have hTor : GGTorusTorData (ggTorM lab) 6 CartanMatrix.E₆ CoxeterMatrix.E₆ J
      (ggGamma J hN).range :=
    hTorW J (ggQuotHom θ) (ggGamma J hN).range hTB
  have hn1 : 1 ≤ lab.n := hlab.1
  have hodd : Odd (ggTorM lab) := by
    have h2 : 2 ≤ 2 ^ lab.n := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ lab.n := Nat.pow_le_pow_right (by norm_num) hn1
    have hsub : Odd (2 ^ lab.n - 1) := by
      obtain ⟨a, ha⟩ := (show Even (2 ^ lab.n) from
        Nat.even_pow.mpr ⟨even_two, by omega⟩)
      exact ⟨a - 1, by omega⟩
    simpa [ggTorM, htag] using hsub
  have hdvd : 3 ∣ ggTorM lab := by
    simpa [ggTorM, htag] using h3n
  obtain ⟨w, hw⟩ := hTor
  obtain ⟨hnk, _, _, _, _, _, _, _⟩ :=
    ggTD_core hodd hdvd hBs hSC hN w hw
  obtain ⟨e, _⟩ := ggTD_weyl hN hw (by norm_num) hBs hnk
  have hType : GGIsTypeE6 (CoxeterMatrix.E₆) := ⟨Equiv.refl (Fin 6), rfl⟩
  exact card_ggAutomizer_of_typeE6 hType e

theorem GGResHyp.actual_J_not_E6_split_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    False := by
  have h51840 := GGResHyp.card_automizer_J_eq_E6_split_of_label hH hMark
  have h24 : Nat.card (ggAutomizer J Bs) = 24 :=
    ggAutomizer_card_of_lineJDatum_A3 (p := 3) rfl hD
  rw [h24] at h51840
  norm_num at h51840

theorem GGResHyp.actual_J_not_E6_split_of_line
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .A2 ∨ T = .B2 ∨ T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    False := by
  have h51840 := GGResHyp.card_automizer_J_eq_E6_split_of_label hH hMark
  have hle48 : Nat.card (ggAutomizer J Bs) ≤ 48 := by
    rcases hT with rfl | rfl | rfl | rfl
    · have h := ggAutomizer_card_of_lineJDatum_A2 (p := 3) rfl hD
      omega
    · have h := ggAutomizer_card_of_lineJDatum_B2 (p := 3) rfl hD
      omega
    · have h := ggAutomizer_card_of_lineJDatum_B3 (p := 3) rfl hD
      omega
    · have h := ggAutomizer_card_of_lineJDatum_C3 (p := 3) rfl hD
      omega
  omega

section E6ThreeFrameCertificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

private theorem ggTorusInvolFrameElt_E6Plus
    {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K + 1) :
    GGTorusInvolFrameElt 3 4 (TableBExc.RecipeGroup .E6 K) := by
  refine ggTorusInvolFrameElt_of_mulEquiv (TableBExc.recipeEquiv .E6 K) ?_
  obtain ⟨F, hF⟩ :=
    ExcFrames.E6QPlusThree.exists_e6QPlusThreeFrame_weyl_surjective (K := K) h3
  choose a ha using fun i => hF (simple .F4 i)
  have hfr := exists_involFrame_torusAct_F4 Nat.prime_three (by decide) F.frame
    (fun i => (a i : adjointGroup .E6 K)) fun i s => by rw [F.conj_frame, ha]
  refine ggTorusInvolFrameElt_of_conj F.frame F.frame_injective hfr ?_
  intro E hE hr _ hsc
  refine ExcFrames.e6ThreeSCReference_holds h3 F hE hr ?_
  intro c hc hc3
  exact hsc c (fun e he => (Subgroup.mem_centralizer_iff.mp hc e he).symm) hc3

private theorem ggExcPlusFrameModelOn_E6Plus
    {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K + 1) :
    GGExcPlusFrameModelOn .F4 3 4 (adjointGroup .E6 K) := by
  classical
  obtain ⟨F, hsurj⟩ :=
    ExcFrames.E6QPlusThree.exists_e6QPlusThreeFrame_weyl_surjective (K := K) h3
  choose m hm using fun i => hsurj (simple .F4 i)
  intro E hE hcard hsc
  have hEsc : ∀ c ∈ Subgroup.centralizer (E : Set (adjointGroup .E6 K)), c ^ 3 = 1 → c ∈ E :=
    fun c hc hc3 => hsc c (fun e he => (Subgroup.mem_centralizer_iff.mp hc e he).symm) hc3
  obtain ⟨c, hc⟩ := ExcFrames.e6ThreeSCReference_holds h3 F hE hcard hEsc
  refine ⟨(MulAut.conj c).toMonoidHom.comp F.frame,
    fun i => c * (m i : adjointGroup .E6 K) * c⁻¹,
    (MulAut.conj c).injective.comp F.frame_injective, ?_, ?_, ?_⟩
  · rw [MonoidHom.range_comp, hc]
  · intro i s
    have h1 := F.conj_frame (m i) s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c * (m i : adjointGroup .E6 K) * c⁻¹ *
          (c * F.frame (Multiplicative.ofAdd s) * c⁻¹) *
          (c * (m i : adjointGroup .E6 K) * c⁻¹)⁻¹ =
        c * ((m i : adjointGroup .E6 K) * F.frame (Multiplicative.ofAdd s) *
          (m i : adjointGroup .E6 K)⁻¹) * c⁻¹ by group]
    rw [h1, hm i]
  · intro g hg
    rw [hc, ← Subgroup.map_equiv_normalizer_eq] at hg
    obtain ⟨x, hx, rfl⟩ := hg
    have hxs : ∀ s, x * F.frame s * x⁻¹ ∈ F.frame.range :=
      fun s => (Subgroup.mem_normalizer_iff.mp hx _).mp ⟨s, rfl⟩
    have hxN : x ∈ F.N := F.mem_N_of_conj x hxs
    refine ⟨F.weyl ⟨x, hxN⟩, fun s => ?_⟩
    have h1 := F.conj_frame ⟨x, hxN⟩ s
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show c * x * c⁻¹ * (c * F.frame (Multiplicative.ofAdd s) * c⁻¹) *
          (c * x * c⁻¹)⁻¹ =
        c * (x * F.frame (Multiplicative.ofAdd s) * x⁻¹) * c⁻¹ by group]
    rw [h1]

private theorem ggTorusReflGenW_E6Plus
    {K : Type} [Field K] [Finite K] [CharP K 2] (h3 : 3 ∣ Nat.card K + 1) :
    GGTorusReflGenW 3 4 (TableBExc.RecipeGroup .E6 K) (TableBExc.RecipeID .E6 K) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  have hnK : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  have h3' : ¬ 3 ∣ Nat.card K - 1 := by
    intro hdiv
    have hsub : 3 ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub h3 hdiv
    have heq : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by
      have hpos : 1 ≤ Nat.card K := Nat.card_pos
      omega
    rw [heq] at hsub
    norm_num at hsub
  have h3n : ¬ 3 ∣ 2 ^ (n : ℕ) - 1 := by
    rw [← hnK]
    exact h3'
  have hcop : Nat.Coprime 3 (Nat.gcd 3 (Nat.card K - 1)) :=
    Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 (Nat.card K - 1))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3')
  exact ggTorusReflGenW_of_excPlusModel Nat.prime_three (by norm_num)
    (ggExcPlusWeylModelSCr_of_frameModelOn (τ := .F4) Nat.prime_three
      (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (fun φ hφ hφp => mem_inn_of_mem_recipeID_E6 (n := n) hnK Nat.prime_three
        (Or.inr h3n) hφ hφp)
      (ggCenterPrime_recipe_E6_of_coprime (K := K) Nat.prime_three (by norm_num) hcop)
      ((ggExcPlusFrameModelOn_E6Plus (K := K) h3).of_mulEquiv
        (TableBExc.recipeEquiv .E6 K)))

private theorem largeEvenLabelAll_frame_E6Plus
    {lab : LargeEvenLabel} (h : lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift 3 r R ∧
      ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
        GGTorusTBGroup 3 r R I L' ψ A → GGTorusFrame 3 A := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, h3n⟩ := h
  dsimp only at ht h3n
  subst ht
  rintro Q ⟨K, _, _, hK, hQ⟩
  have : CharP K 2 := charP_two_of_card hK
  have h3K : 3 ∣ Nat.card K + 1 := by rw [hK]; exact h3n
  have h3n' : 3 ∣ 2 ^ n + 1 := by simpa using h3n
  have hnot : ¬ 3 ∣ 2 ^ n - 1 := by
    intro hdiv
    have hsub : 3 ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub h3n' hdiv
    have htwo : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    rw [htwo] at hsub
    norm_num at hsub
  have hnotK : ¬ 3 ∣ Nat.card K - 1 := by simpa [hK] using hnot
  have hgcd : Nat.gcd 3 (Nat.card K - 1) = 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one]
    exact (Nat.prime_three.coprime_iff_not_dvd).mpr hnotK
  have hcop : Nat.Coprime 3 (Nat.gcd 3 (Nat.card K - 1)) := by
    rw [hgcd]
    exact Nat.coprime_one_right 3
  exact ⟨K, inferInstance, inferInstance, hK, hQ, 4,
    TableBExc.E6Three.ggTorusLift_E6_two,
    ggTorusFrame_of_involFrameElt Nat.prime_three
      (TableBExc.center_recipeGroup_eq_bot .E6 K)
      (fun φ hφ hφp => mem_inn_of_mem_recipeID_E6 hK Nat.prime_three (Or.inr hnot) hφ hφp)
      (ggCenterPrime_recipe_E6_of_coprime (K := K) Nat.prime_three (by norm_num) hcop)
      (ggTorusInvolFrameElt_E6Plus h3K)⟩

private theorem largeEvenLabelAll_reflGenW_E6Plus
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab fun R _ I _ => GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, h3n⟩ := h
  dsimp only at ht
  subst ht
  have hl : l = 0 := by simpa using hlab.2
  subst hl
  rintro Q ⟨K, _, _, hK, hQ⟩
  have : CharP K 2 := charP_two_of_card hK
  have h3K : 3 ∣ Nat.card K + 1 := by rw [hK]; exact h3n
  exact ⟨K, inferInstance, inferInstance, hK, hQ,
    TableBExc.E6Three.ggTorusLift_E6_two, ggTorusReflGenW_E6Plus h3K⟩

private theorem largeEvenLabelAll_reflGenW_twE6Dvd
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I) :=
  TwE6Delta.labelAll h.1 fun _ _ _ hK _ _ =>
    ⟨ggTorusLift_twE6Dvd_holds hlab.1 hK Nat.prime_three (by norm_num) h.2,
      ggTorusReflGenW_twE6Three hlab.1 hK h.2⟩

theorem largeEvenLabelAll_facts_reflGenW_E6Plus
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        KGA.GGF4AutOrderAt 3 R ∧ GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, h3n⟩ := h
  dsimp only at ht
  subst ht
  have hl : l = 0 := by simpa using hlab.2
  subst hl
  have hf := ggPumpTwExc_facts_E6 (f := n) h3n
  have hw : LargeEvenLabelAll ⟨.E6, 0, n⟩ (LargeEvenSimpleGuard fun R _ I _ =>
      GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I) :=
    (largeEvenLabelAll_reflGenW_E6Plus (lab := ⟨.E6, 0, n⟩) hlab ⟨rfl, h3n⟩).mono
      (fun _ _ _ _ hW _ _ => hW)
  refine (largeEvenLabelAll_and hf hw).mono ?_
  rintro R _ I F h hs hna
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, (h.2 hs hna).1, (h.2 hs hna).2⟩

theorem largeEvenLabelAll_facts_reflGenW_twE6Dvd
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab)
    (h : lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) :
    LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
      Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
        KGA.GGF4AutOrderAt 3 R ∧ GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, h3n⟩ := h
  dsimp only at ht
  subst ht
  have hl : l = 0 := by simpa using hlab.2
  subst hl
  have hf := ggPumpTwExc_facts_twE6 (f := n) hlab.1 h3n
  have hw := largeEvenLabelAll_reflGenW_twE6Dvd (lab := ⟨.twE6, 0, n⟩) hlab ⟨rfl, h3n⟩
  refine (largeEvenLabelAll_and hf hw).mono ?_
  rintro R _ I F h hs hna
  exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, (h.2 hs hna).1, (h.2 hs hna).2⟩

theorem GGResHyp.card_automizer_J_ge_1152_of_marking
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {S : ℕ → LargeEvenLabel → Prop}
    (hMark : GGInnerDiagOnLabel S 3 Bs J)
    (hall : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab (LargeEvenSimpleGuard fun R _ I _ =>
        Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧ GGOutdiagPrime 3 R I ∧
          KGA.GGF4AutOrderAt 3 R ∧ GGTorusLift 3 4 R ∧ GGTorusReflGenW 3 4 R I)) :
    1152 ≤ Nat.card (ggAutomizer J Bs) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlab, hraw⟩ := hMark
  have hraw0 := hraw
  obtain ⟨_, _, _, _, hq0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP0⟩ := hq0
  obtain ⟨hS0, _, _⟩ := hP0
  have hAll := hall lab hlab hS0
  have hrawAll := hAll _ hraw0
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hrawAll
  obtain ⟨⟨hs, hna, θ, hPmark⟩, hGuard⟩ := hq
  obtain ⟨hZ, hcp, hout, hAO, hLift, hWR⟩ := hGuard hs hna
  obtain ⟨hS, hN, hBsI⟩ := hPmark
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBI : ∀ (b : G) (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces J θ hN hBsI hb
  have hr : 3 ^ 4 ≤ Nat.card (ggGamma J hN).range :=
    GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hLift
  have hTB : GGTorusTBGroup 3 4 R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN hBI hr
      ((by norm_num : 3 ^ 3 ≤ 3 ^ 4).trans hr)
  have hsurj : Function.Surjective (ggAutomizerGammaHom hN) := by
    intro a
    obtain ⟨c, hc, hover⟩ :=
      exists_overGamma_of_weylReflSet Nat.prime_three (by norm_num) hBs hSC hN
        (hWR J (ggQuotHom θ) (ggGamma J hN).range hTB) a a.2
    have hcAut : c ∈ ggAutomizer J Bs :=
      (Subgroup.closure_le _).mpr (fun φ hφ => hφ.1) hc
    refine ⟨⟨c, hcAut⟩, ?_⟩
    apply Subtype.ext
    exact GGOverGamma.unique (ggAutomizerGammaHom_overGamma hN ⟨c, hcAut⟩) hover
  have hord : Nat.card (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range
      (ggGamma J hN).range) = 1152 :=
    ggPumpTwExc_transport hZ hout hAO (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hJperf (ggGamma J hN).range hTB.2.2.2.1
      hTB.2.2.2.2.1 hr
  have hle := Nat.card_le_card_of_surjective (ggAutomizerGammaHom hN) hsurj
  rwa [hord] at hle

theorem GGResHyp.actual_J_automizer_card_ge_1152_of_E6_qplus
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    1152 ≤ Nat.card (ggAutomizer J Bs) :=
  GGResHyp.card_automizer_J_ge_1152_of_marking hH hMark
    (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_E6Plus hlab hs)

theorem GGResHyp.actual_J_automizer_card_ge_1152_of_twE6_split
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    1152 ≤ Nat.card (ggAutomizer J Bs) :=
  GGResHyp.card_automizer_J_ge_1152_of_marking hH hMark
    (fun lab hlab hs => largeEvenLabelAll_facts_reflGenW_twE6Dvd hlab hs)

theorem GGResHyp.actual_J_not_E6_qplus_or_twE6_split_for_all_lines
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    {T : GGResLineJType}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J T)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab =>
        (lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)) 3 Bs J) :
    False := by
  have h48 : Nat.card (ggAutomizer J Bs) ≤ 48 :=
    CFSG.StandardType.ResJCubicBlock.card_ggAutomizer_le_fortyEight_of_lineJDatum hD
  rcases GGInnerDiagOnLabel.elim_or hMark with hE6 | hTw
  · have h1152 := GGResHyp.actual_J_automizer_card_ge_1152_of_E6_qplus hH hE6
    omega
  · have h1152 := GGResHyp.actual_J_automizer_card_ge_1152_of_twE6_split hH hTw
    omega

private theorem GGResHyp.actual_J_not_frame_of_marking
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (S : ℕ → LargeEvenLabel → Prop)
    (hP : ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → S 3 lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r : ℕ, GGTorusLift 3 r R ∧
        ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R) (A : Subgroup (MulAut L')),
          GGTorusTBGroup 3 r R I L' ψ A → GGTorusFrame 3 A)
    (hMark : GGInnerDiagOnLabel S 3 Bs J) :
    False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlab, hraw⟩ := hMark
  have hraw0 := hraw
  obtain ⟨_, _, _, _, hq0⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, _, _, hP0⟩ := hq0
  obtain ⟨hS0, _, _⟩ := hP0
  have hAll := hP lab hlab hS0
  have hrawAll := hAll _ hraw0
  obtain ⟨R, _, I, F, hq⟩ := largeEvenRawDatum_exists hrawAll
  obtain ⟨⟨hs, hna, θ, hPmark⟩, r, hLift, hFrame⟩ := hq
  obtain ⟨hS, hN, hBsI⟩ := hPmark
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBI : ∀ (b : G) (hb : b ∈ Bs), ggLAut J θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces J θ hN hBsI hb
  have hr : 3 ^ r ≤ Nat.card (ggGamma J hN).range :=
    GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hLift
  have h3 : 3 ^ 3 ≤ Nat.card (ggGamma J hN).range :=
    GGResHyp.cube_le_card_gamma_of_A3 hH hD
  have hTB : GGTorusTBGroup 3 r R I J (ggQuotHom θ) (ggGamma J hN).range :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN hBI hr h3
  have hFrameA : GGTorusFrame 3 (ggGamma J hN).range :=
    hFrame J (ggQuotHom θ) (ggGamma J hN).range hTB
  obtain ⟨a₁, ha₁, a₂, ha₂, h4⟩ := hFrameA
  obtain ⟨n₁, hn₁, hnW₁, rfl, hrefl₁⟩ := ha₁
  obtain ⟨n₂, hn₂, hnW₂, rfl, hrefl₂⟩ := ha₂
  obtain ⟨g₁, hg₁J, hg₁, hrefl₁', hover₁⟩ :=
    exists_isReflection_overGamma_of_weylElt Nat.prime_three (by norm_num) hBs hSC hN
      hnW₁ hn₁ hrefl₁
  obtain ⟨g₂, hg₂J, hg₂, hrefl₂', hover₂⟩ :=
    exists_isReflection_overGamma_of_weylElt Nat.prime_three (by norm_num) hBs hSC hN
      hnW₂ hn₂ hrefl₂
  have hc₁ : ggConjAut Bs hg₁ ∈ ggAutomizer J Bs :=
    ggConjAut_mem_ggAutomizer hg₁J hg₁
  have hc₂ : ggConjAut Bs hg₂ ∈ ggAutomizer J Bs :=
    ggConjAut_mem_ggAutomizer hg₂J hg₂
  have h4' : 4 ∣ orderOf (ggConjAut Bs hg₁ * ggConjAut Bs hg₂) :=
    h4.trans (hover₁.mul hover₂).orderOf_dvd
  exact (ggWeylOfType_A_no_frame (p := 3) (by norm_num) hBs
    (ggWeylOfType_of_lineJDatum_A3 hD) hc₁ hc₂ hrefl₁' hrefl₂') h4'

theorem GGResHyp.actual_J_not_twE6_split_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1) 3 Bs J) :
    False :=
  GGResHyp.actual_J_not_frame_of_marking hH hD
    (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n - 1)
    (fun lab hlab hs => largeEvenLabelAll_frame_twE6Dvd
      Nat.prime_three (by norm_num) hlab hs) hMark

theorem GGResHyp.actual_J_not_E6_qplus_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    False :=
  GGResHyp.actual_J_not_frame_of_marking hH hD
    (fun _ lab => lab.tag = .E6 ∧ 3 ∣ 2 ^ lab.n + 1)
    (fun lab _ hs => largeEvenLabelAll_frame_E6Plus hs) hMark

end E6ThreeFrameCertificates

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Open

theorem GGResHyp.not_of_e6ThreeWeylModel_of_lineJDatum
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    {Z : Subgroup ↥J}
    (hN : Bs ≤ Subgroup.normalizer (J : Set G))
    (hM : GGE6ThreeWeylModel Z (ggGamma J hN).range) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  obtain ⟨Φ, Tsub, w, h⟩ := hM.exists_data
  have hsurj : Function.Surjective (ggAutomizerGammaHom hN) := by
    intro a
    have ha : (a : MulAut ↥(ggGamma J hN).range) ∈
        Subgroup.closure (Set.range h.conjAut) := by
      rw [← h.automizer_eq_reflGen]
      exact a.2
    have hgen : Set.range h.conjAut ⊆
        ((ggAutomizerGammaHom hN).range.map
          (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range (ggGamma J hN).range).subtype :
          Subgroup (MulAut ↥(ggGamma J hN).range)) := by
      rintro _ ⟨i, rfl⟩
      have hnBs : (w i : G) ∈ Subgroup.normalizer (Bs : Set G) :=
        mem_normalizer_of_ggTorusWeylElt (X := J) hN hSC (h.torusWeylElt_w i)
      let c : ggAutomizer J Bs :=
        ⟨ggConjAut Bs hnBs, ggConjAut_mem_ggAutomizer (w i).2 hnBs⟩
      refine Subgroup.mem_map.mpr ⟨⟨h.conjAut i, h.conjAut_mem_automizer i⟩, ?_, rfl⟩
      refine MonoidHom.mem_range.mpr ⟨c, Subtype.ext ?_⟩
      refine (GGOverGamma.unique (ggAutomizerGammaHom_overGamma hN c)
        (ggOverGamma_conjAut (hN := hN) (w i).2 hnBs)).trans ?_
      apply MulEquiv.ext
      intro b
      exact Subtype.ext rfl
    have hclos : Subgroup.closure (Set.range h.conjAut) ≤
        (ggAutomizerGammaHom hN).range.map
          (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range (ggGamma J hN).range).subtype := by
      rw [Subgroup.closure_le]
      exact hgen
    obtain ⟨c, hcrange, hcval⟩ := Subgroup.mem_map.mp (hclos ha)
    obtain ⟨d, hd⟩ := MonoidHom.mem_range.mp hcrange
    refine ⟨d, Subtype.ext ?_⟩
    rw [hd]
    exact hcval
  have hcardDom : Nat.card (ggAutomizer J Bs) ≤ 48 :=
    ResJCubicBlock.card_ggAutomizer_le_fortyEight_of_lineJDatum hD
  have hcardCod : Nat.card (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range
      (ggGamma J hN).range) = 51840 := by
    rw [← Nat.card_congr h.automizerEquivWeyl.toEquiv]
    exact NoOffExc.card_weyl_E6
  have hle : Nat.card (ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range
      (ggGamma J hN).range) ≤ Nat.card (ggAutomizer J Bs) :=
    Nat.card_le_card_of_surjective _ hsurj
  rw [hcardCod] at hle
  omega

theorem GGResHyp.actual_J_not_twE6_qplus_toral_of_lineJDatum
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    {n : ℕ} {K' : Type} [Field K'] [Finite K'] (hn : 1 ≤ n)
    (hK : Nat.card K' = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {θ : ↥J ⧸ Subgroup.center ↥J ≃* TwE6Delta.RecipeR K' n}
    (hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut J θ ⟨b, (GGResHyp.Bs_le_normalizer_J hH) hb⟩ ∈ TwE6Delta.RecipeI K' n)
    {Ω : Type} [Field Ω] [Algebra K' Ω] [IsAlgClosure K' Ω]
    (σ : K' ≃+* K') (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K' σ.toRingHom) ≃* TwE6Delta.RecipeR K' n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K' σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K' n ↔ x ∈ (RecipeExcLang.twConj K' σ).range)
    (htor : SCFourCover.E6AdToral (SCFourCover.rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.inducedSub (ggQuotHom θ)
        (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range))) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let hN := GGResHyp.Bs_le_normalizer_J hH
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  have hJperf : commutator ↥J = ⊤ := hH.1.2.2.1.2.2.2.2.2.1.2.2.1
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hlift4 : GGTorusLift 3 4 (TwE6Delta.RecipeR K' n) :=
    ggTorusLift_twE6Three hn hK h3
  have hr4 : 3 ^ 4 ≤ Nat.card A :=
    GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hlift4
  have h3A : 3 ^ 3 ≤ Nat.card A :=
    (by norm_num : 3 ^ 3 ≤ 3 ^ 4).trans hr4
  have hTB4 : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR K' n) (TwE6Delta.RecipeI K' n)
      J (ggQuotHom θ) A :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN hBsI hr4 h3A
  have h5 : 3 ^ 5 ≤ Nat.card A :=
    SCFourCover.three_pow_five_le_card_of_e6AdToral_rgrpModel
      hn hK σ hσ Fr hFr ε hε h3 hTB4.1 hTB4.2.1 hJperf hTB4.2.2.2.1 hr4
      hTB4.2.2.2.2.1 hTB4.2.2.2.2.2.2.2 htor
  have hTB5 : GGTorusTBGroup 3 5 (TwE6Delta.RecipeR K' n) (TwE6Delta.RecipeI K' n)
      J (ggQuotHom θ) A :=
    ggTorusTBGroup_of_marking Nat.prime_three hBs hSC hJperf θ hN hBsI h5 h3A
  have hM : GGE6ThreeWeylModel (ggQuotHom θ).ker A :=
    (E6ThreeModel.e6ThreeModel_holds.2 K' n hn hK h3)
      ↥J (ggQuotHom θ) hTB5.1 hTB5.2.1 hJperf A hTB5.2.2.2.1 hTB5.2.2.2.2.1 h5
      hTB5.2.2.2.2.2.2.2
  exact GGResHyp.not_of_e6ThreeWeylModel_of_lineJDatum hH hD hN hM

theorem GGResHyp.actual_J_not_twE6_qplus_toral_of_line
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .A3 ∨ T = .B3 ∨ T = .C3)
    {n : ℕ} {K' : Type} [Field K'] [Finite K'] (hn : 1 ≤ n)
    (hK : Nat.card K' = (2 ^ n) ^ 2) (h3 : 3 ∣ 2 ^ n + 1)
    {θ : ↥J ⧸ Subgroup.center ↥J ≃* TwE6Delta.RecipeR K' n}
    (hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut J θ ⟨b, (GGResHyp.Bs_le_normalizer_J hH) hb⟩ ∈ TwE6Delta.RecipeI K' n)
    {Ω : Type} [Field Ω] [Algebra K' Ω] [IsAlgClosure K' Ω]
    (σ : K' ≃+* K') (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K' σ.toRingHom) ≃* TwE6Delta.RecipeR K' n)
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K' σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K' n ↔ x ∈ (RecipeExcLang.twConj K' σ).range)
    (htor : SCFourCover.E6AdToral (SCFourCover.rgrpModel hn hK σ hσ Fr hFr ε
      (TypeA.inducedSub (ggQuotHom θ)
        (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range))) :
    False :=
  GGResHyp.actual_J_not_twE6_qplus_toral_of_lineJDatum hH hD hn hK h3 hBsI σ hσ Fr hFr ε hε htor

end Certificates

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.GGFinModel
open CFSG.StandardType.SCFourCover

section Certificates

theorem GGResHyp.actual_J_not_twE6_qplus_of_line
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .A3 ∨ T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlab, hraw⟩ := hMark
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hS₀, hBsN₀, hBsI₀⟩ := hP₀
  have ht : lab.tag = .twE6 := hS₀.1
  obtain ⟨t, l, n⟩ := lab
  change t = .twE6 at ht
  subst ht
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨Kf, hKfield, hKfin, hKcard, hQ⟩ := hraw
  letI : Field Kf := hKfield
  letI : Finite Kf := hKfin
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨hS, hBsN', hBsI⟩ := hP
  have hdvd : 3 ∣ 2 ^ n + 1 := hS.2
  have hn : 1 ≤ n := hlab.1
  let hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP Kf 2 := CFSG.StandardType.charP_two_of_card (m := n * 2)
    (by rw [hKcard, pow_mul])
  have hinj : Function.Injective (iterateFrobenius Kf 2 n) :=
    (iterateFrobenius Kf 2 n).injective
  let σ : Kf ≃+* Kf := RingEquiv.ofBijective (iterateFrobenius Kf 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨inst, hinst⟩ := exists_algebra_isAlgClosure_ggl Kf
  letI : Algebra Kf GGL := inst
  haveI : IsAlgClosure Kf GGL := hinst
  haveI : CharP GGL 2 := charP_of_injective_algebraMap (algebraMap Kf GGL).injective 2
  let Fr : GGL →+* GGL := ggFrobT n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => ggFrobT_apply n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hKcard σ hσ
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let ψ : ↥J →* TwE6Delta.RecipeR Kf n := ggQuotHom θ
  let E : Subgroup (ModGL Tag.E6 GGL) :=
    rgrpModel hn hKcard σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  have hψ : Function.Surjective ψ := ggQuotHom_surjective θ
  have hker : ψ.ker ≤ Subgroup.center ↥J := by rw [ker_ggQuotHom]
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hA : IsElemAbelian 3 A :=
    CFSG.StandardType.ggIsElemAbelian_range le_rfl hBs (ggGamma J hN)
  have hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI Kf n, ∀ l : ↥J,
      φ (ψ l) = ψ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN b, ggBeta_mem J θ hN hBsI b,
      fun l => ggBeta_ggQuotHom J hN θ b l⟩
  have hBI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut J θ ⟨b, hN hb⟩ ∈ TwE6Delta.RecipeI Kf n :=
    fun b hb => ggLAut_mem_of_induces J θ hN hBsI hb
  by_cases htor : E6AdToral E
  · exact GGResHyp.actual_J_not_twE6_qplus_toral_of_line hH hD hT hn hKcard hdvd hBI
      σ hσ Fr hFr ε hε htor
  ·
    have hnt : ¬ E6AdToral E := htor
    haveI : Finite A := Subtype.finite
    have hle : Nat.card A ≤ 3 ^ 4 :=
      SCFourCover.card_le_four_of_not_e6AdToral_rgrpModel_of_cover
        (Ω := GGL) (n := n) (K := Kf) (hn := hn) (hK := hKcard) (σ := σ) (hσ := hσ)
        (Fr := Fr) (hFr := hFr) (ε := ε) hε hψ hker hJperf hA hAI hnt
    have hlift4 : GGTorusLift 3 4 (TwE6Delta.RecipeR Kf n) :=
      ggTorusLift_twE6Three hn hKcard hdvd
    have hr4 : 3 ^ 4 ≤ Nat.card A :=
      GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hlift4
    have hcardA : Nat.card A = 3 ^ 4 := le_antisymm hle hr4
    have hcardA81 : Nat.card A ≤ 81 := by
      have h := hle
      norm_num at h
      exact h
    let γ := recipeActorModelEquiv hn hKcard σ hσ Fr hFr ε hε hψ hker hJperf hAI
    have hcardEA : Nat.card E = Nat.card A :=
      (Nat.card_congr γ.toEquiv).symm
    have hcardE : Nat.card E = 3 ^ 4 := hcardEA.trans hcardA
    have hEa : E ≤ adjointGroup Tag.E6 GGL := fun z hz =>
      ((TwistedDiag.mem_Rgrp Fr).mp
        (rgrpModel_le_Rgrp hn hKcard σ hσ Fr hFr ε (TypeA.inducedSub ψ A) hz)).1
    have hcardne : Nat.card E ≠ 0 := by rw [hcardE]; norm_num
    have hEfin : (E : Set (ModGL Tag.E6 GGL)).Finite :=
      Set.finite_coe_iff.mpr (Nat.finite_of_card_ne_zero hcardne)
    have hAab : IsElemAbelian 3 E :=
      isElemAbelian_rgrpModel hn hKcard σ hσ Fr hFr ε
        (TypeA.isElemAbelian_inducedSub hψ hA)
    have hpre : LieCore.M6c.GGLieAbelianPreimageE6 E :=
      actual_rankThree_recipe_abelianPreimage hN hD hT hn hKcard σ hσ Fr hFr ε hε
        hψ hker hJperf hAI hcardA81
    have htor' : E6AdToral E :=
      LieCore.M6c.e6AdToral_of_abelianPreimage_GGL E hEa hEfin hAab hcardE hpre
    exact hnt htor'

theorem GGResHyp.actual_J_not_twE6_qplus_for_A3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub) (hD : GGResLineJDatum 3 Bs J .A3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    False :=
  GGResHyp.actual_J_not_twE6_qplus_of_line hH hD (Or.inl rfl) hMark

theorem GGResHyp.actual_J_not_twE6_qplus_for_B3C3
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub) {T : GGResLineJType}
    (hD : GGResLineJDatum 3 Bs J T)
    (hT : T = .B3 ∨ T = .C3)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    False :=
  GGResHyp.actual_J_not_twE6_qplus_of_line hH hD (Or.inr hT) hMark

theorem GGResHyp.b2_actual_reflections_transport
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .B2) :
    ∃ r0 r1 : ggAutomizer J Bs,
      GGIsReflection 3 (r0 : MulAut ↥Bs) ∧
      GGIsReflection 3 (r1 : MulAut ↥Bs) ∧
      GGIsReflection 3 ((ggAutomizerGammaHom (GGResHyp.Bs_le_normalizer_J hH) r0 :
          MulAut ↥(ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range)) ∧
      GGIsReflection 3 ((ggAutomizerGammaHom (GGResHyp.Bs_le_normalizer_J hH) r1 :
          MulAut ↥(ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range)) ∧
      orderOf (r0 * r1) = 4 ∧
      orderOf (ggAutomizerGammaHom (GGResHyp.Bs_le_normalizer_J hH) (r0 * r1)) = 4 := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨V, instA, instM, ι, r, h, α, hform, hrefl, hpair, hind, hgen⟩ := hD
  let C : Matrix (Fin 2) (Fin 2) ℤ := CartanMatrix.B 2
  have hC : GGIntCartan (CoxeterMatrix.B 2) C := ggIntCartan_B 2
  have hFT : TauCeti.IsFiniteType C := TauCeti.isFiniteType_cartanMatrix_B 2
  have hcartan : GGResLineJType.cartan .B2 = C := rfl
  have hpairC : ∀ i j : Fin 2, α i (h j) = (C i j : ZMod 3) := by
    intro i j
    rw [hpair i j, hcartan]
  obtain ⟨e, he⟩ := ggAutomizer_coxeterEquiv_of_reflectionData
    (M := CoxeterMatrix.B 2) (C := C) ι r h α hC hFT hform hpairC hind hgen
  have hr0 : r (0 : Fin 2) ∈ ggAutomizer J Bs := by
    rw [hgen]
    exact Subgroup.subset_closure ⟨(0 : Fin 2), rfl⟩
  have hr1 : r (1 : Fin 2) ∈ ggAutomizer J Bs := by
    rw [hgen]
    exact Subgroup.subset_closure ⟨(1 : Fin 2), rfl⟩
  let r0 : ggAutomizer J Bs := ⟨r (0 : Fin 2), hr0⟩
  let r1 : ggAutomizer J Bs := ⟨r (1 : Fin 2), hr1⟩
  have hrefl0 : GGIsReflection 3 (r0 : MulAut ↥Bs) := hrefl (0 : Fin 2)
  have hrefl1 : GGIsReflection 3 (r1 : MulAut ↥Bs) := hrefl (1 : Fin 2)
  have he0 : e r0 = (CoxeterMatrix.B 2).simple 0 := he (0 : Fin 2) hr0
  have he1 : e r1 = (CoxeterMatrix.B 2).simple 1 := he (1 : Fin 2) hr1
  have hprod : e (r0 * r1) =
      (CoxeterMatrix.B 2).simple 0 * (CoxeterMatrix.B 2).simple 1 := by
    rw [map_mul, he0, he1]
  have h01 : (CoxeterMatrix.B 2) (0 : Fin 2) 1 = 4 := by decide
  have horder_e : orderOf (e (r0 * r1)) = 4 := by
    rw [hprod]
    simpa [h01] using
      (CoxeterMatrix.B 2).toCoxeterSystem.orderOf_simple_mul_simple (0 : Fin 2) 1
  have horder : orderOf (r0 * r1) = 4 :=
    (orderOf_injective e.toMonoidHom e.injective (r0 * r1)).symm.trans horder_e
  let hN := GGResHyp.Bs_le_normalizer_J hH
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hNoTr : GGNoTransvection 3 Bs := hH.2.2.2.1
  have hZ : Nat.card ↥(Bs ⊓ J ⊓ Subgroup.centralizer (J : Set G)) ≤ 3 :=
    GGResHyp.card_bstar_inf_center_J_le hH
  have hinj : Function.Injective (ggAutomizerGammaHom hN) :=
    ggAutomizerGammaHom_injective (p := 3) (by norm_num) hBs hNoTr hN hZ
  have himage0 : GGIsReflection 3 ((ggAutomizerGammaHom hN r0 :
      MulAut ↥(ggGamma J hN).range)) := by
    rcases isReflection_or_eq_one_of_overGamma (p := 3) (by norm_num) (by norm_num)
      hBs hN (ggAutomizerGammaHom_overGamma hN r0) hrefl0 with h | h1
    · exact h
    · exfalso
      have h2 : ggAutomizerGammaHom hN r0 = 1 := Subtype.ext h1
      have h3 : r0 = 1 := hinj (by rw [h2, map_one])
      have h3' : (r0 : MulAut ↥Bs) = 1 := congrArg Subtype.val h3
      exact hrefl0.ne_one (by norm_num) h3'
  have himage1 : GGIsReflection 3 ((ggAutomizerGammaHom hN r1 :
      MulAut ↥(ggGamma J hN).range)) := by
    rcases isReflection_or_eq_one_of_overGamma (p := 3) (by norm_num) (by norm_num)
      hBs hN (ggAutomizerGammaHom_overGamma hN r1) hrefl1 with h | h1
    · exact h
    · exfalso
      have h2 : ggAutomizerGammaHom hN r1 = 1 := Subtype.ext h1
      have h3 : r1 = 1 := hinj (by rw [h2, map_one])
      have h3' : (r1 : MulAut ↥Bs) = 1 := congrArg Subtype.val h3
      exact hrefl1.ne_one (by norm_num) h3'
  have himage_order : orderOf (ggAutomizerGammaHom hN (r0 * r1)) = 4 :=
    (orderOf_injective (ggAutomizerGammaHom hN) hinj (r0 * r1)).trans horder
  exact ⟨r0, r1, hrefl0, hrefl1, himage0, himage1, horder, himage_order⟩

theorem GGResHyp.b2_non_toral_contradiction
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .B2)
    {Kf : Type} [Field Kf] [Finite Kf] [Algebra Kf GGL] [IsAlgClosure Kf GGL]
    {n : ℕ} (hn : 1 ≤ n)
    (hKcard : Nat.card Kf = (2 ^ n) ^ 2)
    (hdvd : 3 ∣ 2 ^ n + 1)
    {θ : ↥J ⧸ Subgroup.center ↥J ≃* TwE6Delta.RecipeR Kf n}
    {σ : Kf ≃+* Kf} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {Fr : GGL →+* GGL} (hFr : ∀ c, Fr c = c ^ 2 ^ n)
    {ε : ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom) ≃* TwE6Delta.RecipeR Kf n}
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 Kf σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI Kf n ↔ x ∈ (RecipeExcLang.twConj Kf σ).range)
    (hJperf : commutator J = ⊤)
    (hBsI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut J θ ⟨b, (GGResHyp.Bs_le_normalizer_J hH) hb⟩ ∈ TwE6Delta.RecipeI Kf n)
    (hnt : ¬ E6AdToral (rgrpModel hn hKcard σ hσ Fr hFr ε
      (TypeA.inducedSub (ggQuotHom θ) (ggGamma J (GGResHyp.Bs_le_normalizer_J hH)).range))) :
    False := by
  classical
  let hN := GGResHyp.Bs_le_normalizer_J hH
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let G : Subgroup (MulAut A) := ggAutomizer (MulAut.conj : ↥J →* MulAut ↥J).range A
  obtain ⟨r0, r1, hrefl0, hrefl1, himage0, himage1, horder, himage_order⟩ :=
    GGResHyp.b2_actual_reflections_transport hH hD
  let φ0 : MulAut A := ((ggAutomizerGammaHom hN r0 : MulAut A))
  let φ1 : MulAut A := ((ggAutomizerGammaHom hN r1 : MulAut A))
  have hφ0A : φ0 ∈ G := by
    simpa [G, φ0] using (ggAutomizerGammaHom hN r0).2
  have hφ1A : φ1 ∈ G := by
    simpa [G, φ1] using (ggAutomizerGammaHom hN r1).2
  have hlift4 : GGTorusLift 3 4 (TwE6Delta.RecipeR Kf n) :=
    ggTorusLift_twE6Three hn hKcard hdvd
  have hr4 : 3 ^ 4 ≤ Nat.card (ggGamma J hN).range :=
    GGResHyp.pow_le_card_range_gamma_J_of_torusLift hH θ hlift4
  have hTB : GGTorusTBGroup 3 4 (TwE6Delta.RecipeR Kf n) (TwE6Delta.RecipeI Kf n)
      ↥J (ggQuotHom θ) A :=
    ggTorusTBGroup_of_card (p := 3) (r := 4) hH.1 (by norm_num) hJperf θ hN hBsI hr4
  have hne : orderOf (φ0 * φ1) ≠ 4 :=
    orderOf_reflectionProduct_ne_four_of_tableB hn hKcard σ hσ Fr hFr ε hε hTB hnt hφ0A hφ1A
      (by simpa [φ0] using himage0) (by simpa [φ1] using himage1)
  have heq : orderOf (φ0 * φ1) = 4 := by
    have hmap : ((ggAutomizerGammaHom hN (r0 * r1) : G) : MulAut A) = φ0 * φ1 := by
      simp [G, φ0, φ1, map_mul]
    rw [← hmap]
    exact (orderOf_injective G.subtype G.subtype_injective
      (ggAutomizerGammaHom hN (r0 * r1))).trans himage_order
  exact hne heq

theorem GGResHyp.actual_J_not_twE6_qplus_for_B2
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {Ksub : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y Ksub)
    (hD : GGResLineJDatum 3 Bs J .B2)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .twE6 ∧ 3 ∣ 2 ^ lab.n + 1) 3 Bs J) :
    False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hJperf, lab, hlab, hraw⟩ := hMark
  obtain ⟨R₀, hR₀, I₀, F₀, hQ₀⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨-, -, θ₀, hP₀⟩ := hQ₀
  obtain ⟨hS₀, hBsN₀, hBsI₀⟩ := hP₀
  have ht : lab.tag = .twE6 := hS₀.1
  obtain ⟨t, l, n⟩ := lab
  change t = .twE6 at ht
  subst ht
  dsimp only [LargeEvenRawDatumLegacy] at hraw
  obtain ⟨Kf, hKfield, hKfin, hKcard, hQ⟩ := hraw
  letI : Field Kf := hKfield
  letI : Finite Kf := hKfin
  obtain ⟨-, -, θ, hP⟩ := hQ
  obtain ⟨hS, hBsN', hBsI⟩ := hP
  have hdvd : 3 ∣ 2 ^ n + 1 := hS.2
  have hn : 1 ≤ n := hlab.1
  let hN : Bs ≤ Subgroup.normalizer (J : Set G) := GGResHyp.Bs_le_normalizer_J hH
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP Kf 2 := CFSG.StandardType.charP_two_of_card (m := n * 2)
    (by rw [hKcard, pow_mul])
  have hinj : Function.Injective (iterateFrobenius Kf 2 n) :=
    (iterateFrobenius Kf 2 n).injective
  let σ : Kf ≃+* Kf := RingEquiv.ofBijective (iterateFrobenius Kf 2 n)
    ⟨hinj, Finite.surjective_of_injective hinj⟩
  have hσ : ∀ c, σ c = c ^ 2 ^ n := fun c => iterateFrobenius_def 2 n c
  obtain ⟨inst, hinst⟩ := exists_algebra_isAlgClosure_ggl Kf
  letI : Algebra Kf GGL := inst
  haveI : IsAlgClosure Kf GGL := hinst
  haveI : CharP GGL 2 := charP_of_injective_algebraMap (algebraMap Kf GGL).injective 2
  let Fr : GGL →+* GGL := ggFrobT n
  have hFr : ∀ c, Fr c = c ^ 2 ^ n := fun c => ggFrobT_apply n c
  obtain ⟨ε, hε⟩ := TwE6DD2.exists_recipeEquiv hn hKcard σ hσ
  let A : Subgroup (MulAut ↥J) := (ggGamma J hN).range
  let ψ : ↥J →* TwE6Delta.RecipeR Kf n := ggQuotHom θ
  let E : Subgroup (ModGL Tag.E6 GGL) :=
    rgrpModel hn hKcard σ hσ Fr hFr ε (TypeA.inducedSub ψ A)
  have hψ : Function.Surjective ψ := ggQuotHom_surjective θ
  have hker : ψ.ker ≤ Subgroup.center ↥J := by rw [ker_ggQuotHom]
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hA : IsElemAbelian 3 A :=
    CFSG.StandardType.ggIsElemAbelian_range le_rfl hBs (ggGamma J hN)
  have hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI Kf n, ∀ l : ↥J,
      φ (ψ l) = ψ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta J θ hN b, ggBeta_mem J θ hN hBsI b,
      fun l => ggBeta_ggQuotHom J hN θ b l⟩
  have hBI : ∀ (b : G) (hb : b ∈ Bs),
      ggLAut J θ ⟨b, hN hb⟩ ∈ TwE6Delta.RecipeI Kf n :=
    fun b hb => ggLAut_mem_of_induces J θ hN hBsI hb
  by_cases htor : E6AdToral E
  · exact GGResHyp.actual_J_not_twE6_qplus_toral_of_lineJDatum hH hD hn hKcard hdvd hBI
      σ hσ Fr hFr ε hε htor
  · exact GGResHyp.b2_non_toral_contradiction hH hD hn hKcard hdvd hσ hFr hε hJperf hBI htor

end Certificates

end CFSG.StandardType
