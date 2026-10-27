module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight91Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KStrongEmbedded72Holds
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Quot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OutPRankBound
import CFSG.GroupTheory.CoprimeCentralizerRank
import CFSG.GroupTheory.PRankCoprimeQuotient
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.PerfectSubgroupNormalMeet
import CFSG.GroupTheory.PRankCommutingSup
import CFSG.LocalAnalysis.GLTheoremB.PCompBasics
public import CFSG.CGT.PushingUpLit.CGT6.SixFourCoreSL
public import CFSG.CGT.PushingUpLit.Glue.NineContentGlue
public import CFSG.CGT.PushingUpLit.NineContent
public import CFSG.CGT.Timmesfeld75.Derivations
public import CFSG.CGT.Timmesfeld75.Targets
public import CFSG.ClassicalInvolution.AschTight.Thm6Tight
public import CFSG.GroupTheory.CoprimeActionSupport.AbelianEquivalence
public import CFSG.GroupTheory.CoprimeActionSupport.Geometry
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.RankCube
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagLink
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtFusion
public import CFSG.LocalAnalysis.AGLEmbedding.MSideAtInner
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieNormalClosure
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreL34
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreStar
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Cover
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbL34Esc
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMain
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreePerf
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34Ph6
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosA
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallPosT
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.Kmax
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsidePrelim.ThompsonFactor
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011I1416Small
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ICitedHyp111K
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81NineSeventeenReduction
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111NineThree
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACz
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3AFi22
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeA
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNBridgeB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNPair
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15GNSetting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Reduction
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.LocalAnalysis.RankThreeUC.Section3.CoprimeSpecialGroups.CommPowPow
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialOrder
public import CFSG.LocalAnalysis.RankThreeUC.SourceSetting.AschbacherCommon
public import CFSG.LocalAnalysis.RankThreeUC.TheoremDFFDatum
public import CFSG.LocalAnalysis.RankThreeUC.WeakModules
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC22S20b
public import CFSG.LocalAnalysis.UniquenessCase.UC6C621Glue
public import CFSG.LocalAnalysis.UniquenessCase.UC6C636a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLargeHolds
public import CFSG.Quasithin.Background.GoldschmidtAmalgamPairCentral
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.RankThree.OddKernel.CentralCoverComponentModels
public import Certificates.Certificate19762
public import Certificates.Certificate19763
public import Certificates.Certificate9530
public import Certificates.Certificate9681
import CFSG.Quasithin.H13.QRCThreeFreeRankOneStep
import CFSG.Quasithin.SteinbergBKHigherElementaryThompson

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07 (R72)

open scoped commutatorElement

private theorem k891normzcong_R891X_le {G : Type} [Group G] [Finite G] (L Z : Subgroup G)
    (n : ℕ) : R891X L Z n ≤ L ⊓ centralizer (Z : Set G) := by
  unfold R891X
  split
  · exact (Subgroup.closure_le _).mpr (fun y hy => hy.1)
  · exact Subgroup.map_subtype_le _

private theorem k891normzcong_mem_normalizer_pCoreOf_of_mem_centOverO2
    {G : Type} [Group G] [Finite G] {M L : Subgroup G} {c : G}
    (hc : c ∈ F08.CentOverO2 M L) :
    c ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have hcomm := (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hc).2 q
      (CFSG.LieType.BorelTits.pCoreOf_le 2 L hq)
    rw [show c * q * c⁻¹ = (c * q * c⁻¹ * q⁻¹) * q by group]
    exact (pCoreOf 2 L).mul_mem hcomm hq
  · intro hq
    have hq' : c * q * c⁻¹ ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L hq
    have hc' : c⁻¹ ∈ F08.CentOverO2 M L := (F08.CentOverO2 M L).inv_mem hc
    have hcomm := (CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hc').2
      (c * q * c⁻¹) hq'
    rw [show q = (c⁻¹ * (c * q * c⁻¹) * c * (c * q * c⁻¹)⁻¹) * (c * q * c⁻¹) by group]
    exact (pCoreOf 2 L).mul_mem (by simpa only [inv_inv] using hcomm) hq

private theorem k891normzcong_C_inf_L_le_O2 {G : Type} [Group G] [Finite G] {M L : Subgroup G}
    (hcenter : center (Bar2 L) = ⊥) :
    F08.CentOverO2 M L ⊓ L ≤ pCoreOf 2 L := by
  intro x hx
  obtain ⟨hxC, hxL⟩ := Subgroup.mem_inf.mp hx
  have hcent : (QuotientGroup.mk ⟨x, hxL⟩ : Bar2 L) ∈ Subgroup.center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
      have hcoe : (((l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) : ↥L) : G) =
          (x * l * x⁻¹ * l⁻¹)⁻¹ := by
        simp [div_eq_mul_inv, mul_assoc]
      have hG : (((l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) : ↥L) : G) ∈ pCoreOf 2 L := by
        rw [hcoe]
        exact (pCoreOf 2 L).inv_mem
          ((CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff.mp hxC).2 l l.2)
      obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp hG
      have hp_eq : p = (l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) := L.subtype_injective hpeq
      rwa [← hp_eq]
  rw [hcenter] at hcent
  have hxcore : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
    (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hcent)
  exact Subgroup.mem_map_of_mem (f := L.subtype) (K := CFSG.pCore 2 ↥L) hxcore

private theorem k891normzcong_exists_pElement_centOverO2
    {G : Type} [Group G] [Finite G] {M L E : Subgroup G} (hLM : L ≤ M)
    (hML : M ≤ Subgroup.normalizer (L : Set G))
    {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hr : r.Prime) (hr2 : r ≠ 2)
    (hEL : E ≤ L) (hEr : IsPGroup r E)
    (hCp : p ∣ Nat.card (F08.CentOverO2 M L)) :
    ∃ z ∈ F08.CentOverO2 M L, orderOf z = p ∧ z ∈ centralizer (E : Set G) := by
  classical
  let C := F08.CentOverO2 M L
  have hMC : M ≤ Subgroup.normalizer (C : Set G) := by
    rw [show C = F08.CentOverO2 M L from rfl, PartTwo.centOverO2_eq_ker_map hML]
    exact CFSG.GroupTheory.FT63ChII.le_normalizer_map_subtype
      (R := M) ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp (Subgroup.inclusion hML)).ker
  have hEC : E ≤ Subgroup.normalizer (C : Set G) := hEL.trans (hLM.trans hMC)
  have hEO : E ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hEL.trans (le_normalizer.trans (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf L))
  have hO2C : pCoreOf 2 L ≤ C := by
    intro x hx
    refine PartTwo.mem_centOverO2_iff.mpr
      ⟨hLM ((CFSG.LieType.BorelTits.pCoreOf_le 2 L) hx), ?_⟩
    intro l hl
    have hNl : l ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      (le_normalizer.trans (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf L)) hl
    have hconj : l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp hNl x⁻¹).mp ((pCoreOf 2 L).inv_mem hx)
    simpa only [mul_assoc] using (pCoreOf 2 L).mul_mem hx hconj
  have hcomm : ⁅C, E⁆ ≤ pCoreOf 2 L := by
    rw [Subgroup.commutator_le]
    intro c hc e he
    rw [commutatorElement_def]
    exact (PartTwo.mem_centOverO2_iff.mp hc).2 e (hEL he)
  have hOr : ¬ r ∣ Nat.card (pCoreOf 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L) hr hr2
  have hOp : ¬ p ∣ Nat.card (pCoreOf 2 L) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L) hp hp2
  refine letI : Fact r.Prime := ⟨hr⟩; ?_
  refine letI : Fact p.Prime := ⟨hp⟩; ?_
  obtain ⟨P, hP, hPC⟩ :=
    CFSG.GroupTheory.exists_isSylowOf_le_centralizer_of_commutator_le
      (p := r) (q := p) (X := C) (N := pCoreOf 2 L) (R := E)
      hO2C hEC hEO hEr hOr hcomm hOp
  have hPp : p ∣ Nat.card P := by
    rw [hP.card_eq]
    exact dvd_pow_self p (hp.factorization_pos_of_dvd Nat.card_pos.ne' hCp).ne'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := P) p hPp
  exact ⟨z, hP.le z.2, (Subgroup.orderOf_coe z).trans hz, hPC z.2⟩



open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem k891normzcong_two_le_pRank_centralizer
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L S : Subgroup G} {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hset : R891Set D L S n) (hbasic : R891Basic D L S) (hrank : R891Rank893 D L)
    (hpSig : p ∈ D.sig)
    (hpdvd : p ∣ Nat.card (Bar2 (R891X L (ZOf (S ⊓ L)) n))) :
    2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (ZOf (S ⊓ L) : Set G)) := by
  classical
  refine letI : Fact p.Prime := ⟨hp⟩; ?_
  refine letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩; ?_
  set Z : Subgroup G := ZOf (S ⊓ L) with hZdef
  set X : Subgroup G := R891X L Z n with hXdef
  set C : Subgroup G := F08.CentOverO2 D.M L with hCdef
  set N0 : Subgroup G := pCoreOf 2 L ⊓ centralizer (Z : Set G) with hN0def
  have hZcard : Nat.card Z = 3 := hbasic.zOrder
  have hZ3 : IsPGroup 3 Z := by
    rw [IsPGroup.iff_card]; exact ⟨1, by rw [hZcard]; norm_num⟩
  have hZleL : Z ≤ L := by
    intro z hz
    exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hz).1).2
  have hLM : L ≤ D.M := hset.mem.1.le
  have hML : D.M ≤ Subgroup.normalizer (L : Set G) := hbasic.normal
  have hcenter : center (Bar2 L) = ⊥ := hbasic.centerBot
  have hrankC : CFSG.Open.pRank p C = 1 := (hrank p hpSig).2
  have hCp : p ∣ Nat.card C := by
    have h1 : 1 ≤ CFSG.Open.pRank p C := by rw [hrankC]
    exact CFSG.GroupTheory.dvd_card_of_one_le_pRank hp h1
  obtain ⟨z, hzC, hzord, hzZ⟩ :=
    k891normzcong_exists_pElement_centOverO2 hLM hML hp hp2 Nat.prime_three (by norm_num)
      hZleL hZ3 hCp
  have hX_le : X ≤ L ⊓ centralizer (Z : Set G) := by
    rw [hXdef]; exact k891normzcong_R891X_le L Z n
  have hXL : X ≤ L := hX_le.trans inf_le_left
  have hXZ : X ≤ centralizer (Z : Set G) := hX_le.trans inf_le_right
  have hpX : p ∣ Nat.card X := by
    have h1 : p ∣ Nat.card (Bar2 X) := hpdvd
    have h2 : Nat.card (Bar2 X) ∣ Nat.card X := by
      show Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ∣ Nat.card ↥X
      exact Subgroup.card_quotient_dvd_card _
    exact h1.trans h2
  obtain ⟨xg, hxgX, hxgold⟩ : ∃ x : G, x ∈ X ∧ orderOf x = p := by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥X) p (by simpa using hpX)
    exact ⟨(x : G), x.2, (Subgroup.orderOf_coe x).trans hx⟩
  let B : Subgroup G := Subgroup.zpowers xg
  have hBX : B ≤ X := Subgroup.zpowers_le.mpr hxgX
  have hBL : B ≤ L := hBX.trans hXL
  have hBZ : B ≤ centralizer (Z : Set G) := hBX.trans hXZ
  have hBcard : Nat.card B = p := by rw [Nat.card_zpowers, hxgold]
  have hBel : IsElemAbelian p B :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hxgold]; exact pow_orderOf_eq_one xg)
  have hBp : IsPGroup p B := hBel.isPGroup
  have hMC : D.M ≤ Subgroup.normalizer (C : Set G) := by
    rw [hCdef, PartTwo.centOverO2_eq_ker_map hML]
    exact CFSG.GroupTheory.FT63ChII.le_normalizer_map_subtype
      (R := D.M) ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp
        (Subgroup.inclusion hML)).ker
  have hLC : L ≤ Subgroup.normalizer (C : Set G) := hLM.trans hMC
  have hzO2 : z ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    k891normzcong_mem_normalizer_pCoreOf_of_mem_centOverO2 hzC
  have hzCZ : z ∈ Subgroup.normalizer (centralizer (Z : Set G) : Set G) :=
    Subgroup.le_normalizer hzZ
  have hzN0 : z ∈ Subgroup.normalizer (N0 : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hN0def, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hzO2 w).mp h1,
        (Subgroup.mem_normalizer_iff.mp hzCZ w).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hzO2 w).mpr h1,
        (Subgroup.mem_normalizer_iff.mp hzCZ w).mpr h2⟩
  have hBN0 : B ≤ Subgroup.normalizer (N0 : Set G) := by
    intro b hb
    have hbO2 : b ∈ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      (Subgroup.le_normalizer.trans
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf L)) (hBL hb)
    have hbCZ : b ∈ Subgroup.normalizer (centralizer (Z : Set G) : Set G) :=
      Subgroup.le_normalizer (hBZ hb)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hN0def, Subgroup.mem_inf, Subgroup.mem_inf]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hbO2 w).mp h1,
        (Subgroup.mem_normalizer_iff.mp hbCZ w).mp h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hbO2 w).mpr h1,
        (Subgroup.mem_normalizer_iff.mp hbCZ w).mpr h2⟩
  have hcommzB : ⁅Subgroup.zpowers z, B⁆ ≤ N0 := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def, hN0def, Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · exact (PartTwo.mem_centOverO2_iff.mp (Subgroup.zpowers_le.mpr hzC ha)).2 b (hBL hb)
    · have haZ : a ∈ centralizer (Z : Set G) := Subgroup.zpowers_le.mpr hzZ ha
      have hbZ' : b ∈ centralizer (Z : Set G) := hBZ hb
      exact (centralizer (Z : Set G)).mul_mem
        ((centralizer (Z : Set G)).mul_mem
          ((centralizer (Z : Set G)).mul_mem haZ hbZ')
          ((centralizer (Z : Set G)).inv_mem haZ))
        ((centralizer (Z : Set G)).inv_mem hbZ')
  have hzP : IsPGroup p (Subgroup.zpowers z) := by
    rw [IsPGroup.iff_card]; exact ⟨1, by rw [Nat.card_zpowers, hzord]; norm_num⟩
  have hpN0 : ¬ p ∣ Nat.card N0 :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup
      ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L).to_le inf_le_left) hp hp2
  obtain ⟨n0, hn0N0, hn0cent⟩ :=
    CFSG.GroupTheory.exists_map_conj_le_centralizer_of_commutator_le
      (p := p) (q := p) (N := N0) (R := Subgroup.zpowers z) (B := B)
      (Subgroup.zpowers_le.mpr hzN0) hBN0 hzP hBp hpN0 hpN0 hcommzB
  let A' : Subgroup G := (Subgroup.zpowers z).map (MulAut.conj n0).toMonoidHom
  have hn0L : n0 ∈ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L (Subgroup.mem_inf.mp hn0N0).1
  have hn0Z : n0 ∈ centralizer (Z : Set G) := (Subgroup.mem_inf.mp hn0N0).2
  have hA'C : A' ≤ C := by
    have hmap : C.map (MulAut.conj n0).toMonoidHom = C :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLC hn0L)
    exact (Subgroup.map_mono (Subgroup.zpowers_le.mpr hzC)).trans (le_of_eq hmap)
  have hA'Z : A' ≤ centralizer (Z : Set G) := by
    have hmap : (centralizer (Z : Set G)).map (MulAut.conj n0).toMonoidHom =
        centralizer (Z : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hn0Z)
    exact (Subgroup.map_mono (Subgroup.zpowers_le.mpr hzZ)).trans (le_of_eq hmap)
  have hA'M : A' ≤ D.M := by
    have hzM : Subgroup.zpowers z ≤ D.M :=
      (Subgroup.zpowers_le.mpr hzC).trans fun x hx => (PartTwo.mem_centOverO2_iff.mp hx).1
    have hmap : D.M.map (MulAut.conj n0).toMonoidHom = D.M :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer (hLM hn0L))
    exact (Subgroup.map_mono hzM).trans (le_of_eq hmap)
  have hzEl : IsElemAbelian p (Subgroup.zpowers z) :=
    CFSG.Open.isElemAbelian_zpowers (by rw [← hzord]; exact pow_orderOf_eq_one z)
  have hA'el : IsElemAbelian p A' := by
    dsimp [A']; exact hzEl.map (MulAut.conj n0).toMonoidHom
  have hA'card : Nat.card A' = p := by
    dsimp [A']
    rw [Subgroup.card_map_of_injective (MulAut.conj n0).injective, Nat.card_zpowers, hzord]
  have hA'cent : A' ≤ Subgroup.centralizer (B : Set G) := hn0cent
  have hbot : A' ⊓ B = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨hyA', hyB⟩ := Subgroup.mem_inf.mp hy
    have hyO2 : y ∈ pCoreOf 2 L :=
      k891normzcong_C_inf_L_le_O2 hcenter (Subgroup.mem_inf.mpr ⟨hA'C hyA', hBL hyB⟩)
    have hyp : y ^ p = 1 := hA'el.2 y hyA'
    have hdivp : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyp
    obtain ⟨k, hk⟩ :=
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf L).exists_orderOf_eq_pow
        (p := 2) ⟨y, hyO2⟩
    rw [← Subgroup.orderOf_coe (⟨y, hyO2⟩ : ↥(pCoreOf 2 L))] at hk
    have hcop : Nat.Coprime p (2 ^ k) := by
      rw [Nat.Prime.coprime_iff_not_dvd hp]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow hp h))
    have h2 : orderOf y ∣ 2 ^ k := by rw [hk]
    have h1 : orderOf y ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd hdivp h2
    exact (orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1))
  have hAB : ¬ p ∣ Nat.card ↥(A' ⊓ B) := by
    rw [hbot, Subgroup.card_bot]
    exact hp.not_dvd_one
  have hadd := CFSG.GroupTheory.pRank_sup_eq_add_of_commute_of_not_dvd hp hA'cent hAB
  have h1 : 1 ≤ CFSG.Open.pRank p A' :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hA'el (by rw [hA'card, pow_one])
  have h2 : 1 ≤ CFSG.Open.pRank p B :=
    CFSG.SectionRank.le_pRank hp.one_lt le_rfl hBel (by rw [hBcard, pow_one])
  have hsup : A' ⊔ B ≤ D.M ⊓ centralizer (Z : Set G) :=
    sup_le (le_inf hA'M hA'Z) (le_inf (hBL.trans hLM) hBZ)
  have hmono := CFSG.SectionRank.pRank_mono hp.one_lt hsup
  omega



private theorem k891normzcong_X_perfect {G : Type} [Group G] [Finite G] {L Z : Subgroup G} {n : ℕ}
    (hn1 : n ≠ 1) : ⁅R891X L Z n, R891X L Z n⁆ = R891X L Z n := by
  have hXeq : R891X L Z n = F08.DerInf8 (L ⊓ centralizer (Z : Set G)) := by
    rw [R891X, if_neg hn1]
  rw [hXeq]
  refine letI : Group.IsPerfect ↥(CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
      ↥(L ⊓ centralizer (Z : Set G))) :=
    CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_isPerfect; ?_
  have hmap : Group.IsPerfect ↥((CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual
      ↥(L ⊓ centralizer (Z : Set G))).map (L ⊓ centralizer (Z : Set G)).subtype) :=
    Group.IsPerfect.map (L ⊓ centralizer (Z : Set G)).subtype
  exact Subgroup.isPerfect_iff.mp hmap

private theorem k891normzcong_commutatorElement_mul_of_mem_center {Q : Type} [Group Q] {z w a b : Q}
    (hz : z ∈ Subgroup.center Q) (hw : w ∈ Subgroup.center Q) :
    ⁅z * a, w * b⁆ = ⁅a, b⁆ := by
  have hza : z * a = a * z := (Subgroup.mem_center_iff.mp hz a).symm
  have hwb : w * b = b * w := (Subgroup.mem_center_iff.mp hw b).symm
  have hz1 : ∀ x : Q, ⁅z, x⁆ = 1 := fun x => by
    rw [commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.mp hz x).symm
  have hw1 : ∀ x : Q, ⁅x, w⁆ = 1 := fun x => by
    rw [commutatorElement_eq_one_iff_commute]
    exact Subgroup.mem_center_iff.mp hw x
  rw [hza, hwb]
  simp only [commutatorElement_mul_left_eq_conj_mul, commutatorElement_mul_right_eq_mul_conj,
    hz1, hw1, mul_one]
  group

private theorem k891normzcong_normal_le_center_or_eq_top {Q : Type} [Group Q]
    (hperf : commutator Q = ⊤) (hsimple : IsSimpleGroup (Q ⧸ Subgroup.center Q))
    (N : Subgroup Q) [N.Normal] : N ≤ Subgroup.center Q ∨ N = ⊤ := by
  set π := QuotientGroup.mk' (Subgroup.center Q) with hπ
  have hNn : (N.map π).Normal :=
    Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
    exact h
  · right
    have hNZ : ∀ q : Q, ∃ n ∈ N, n⁻¹ * q ∈ Subgroup.center Q := by
      intro q
      have : π q ∈ N.map π := h ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnq⟩ := this
      refine ⟨n, hn, ?_⟩
      rw [← QuotientGroup.ker_mk' (Subgroup.center Q), MonoidHom.mem_ker, map_mul, map_inv,
        ← hπ, hnq, inv_mul_cancel]
    have htop : (⊤ : Subgroup Q) = ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ := by
      rw [← _root_.commutator_def]
      exact hperf.symm
    rw [eq_top_iff, htop, Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨n₁, hn₁, hz₁⟩ := hNZ x
    obtain ⟨n₂, hn₂, hz₂⟩ := hNZ y
    have hx : x = (n₁⁻¹ * x) * n₁ := by
      have := (Subgroup.mem_center_iff.mp hz₁) n₁
      calc x = n₁ * (n₁⁻¹ * x) := by group
        _ = (n₁⁻¹ * x) * n₁ := this
    have hy : y = (n₂⁻¹ * y) * n₂ := by
      have := (Subgroup.mem_center_iff.mp hz₂) n₂
      calc y = n₂ * (n₂⁻¹ * y) := by group
        _ = (n₂⁻¹ * y) * n₂ := this
    have hcomm_eq : ⁅x, y⁆ = ⁅n₁, n₂⁆ := by
      rw [hx, hy]
      exact k891normzcong_commutatorElement_mul_of_mem_center hz₁ hz₂
    rw [hcomm_eq, commutatorElement_def]
    exact N.mul_mem (N.mul_mem (N.mul_mem hn₁ hn₂) (N.inv_mem hn₁)) (N.inv_mem hn₂)



open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement

private theorem k891normzcong_altTen_false
    {G : Type} [Group G] [Finite G] {D : Data G}
    {L S : Subgroup G} {n p : ℕ} (hp : p.Prime) (_hp2 : p ≠ 2) (hn2 : 2 ≤ n)
    (hPrime : R891PrimeCore)
    (hshape : R891SL3Two (Bar2 (R891X L (ZOf (S ⊓ L)) n)) n)
    (hXperf : ⁅R891X L (ZOf (S ⊓ L)) n, R891X L (ZOf (S ⊓ L)) n⁆ =
      R891X L (ZOf (S ⊓ L)) n)
    (H : Subgroup G) (hXH : R891X L (ZOf (S ⊓ L)) n ≤ H)
    (hXM : R891X L (ZOf (S ⊓ L)) n ≤ D.M)
    (hpdvd : p ∣ Nat.card (Bar2 (R891X L (ZOf (S ⊓ L)) n)))
    (hA5all : ∀ Y : Subgroup (F07.QuotK7 p H),
      Y ≤ F07.ImageModK p H (H ⊓ D.M) → ⁅Y, Y⁆ = Y →
      ∀ (S' : Type) [Group S'], IsSimpleGroup S' → ∀ f : ↥Y →* S',
        Function.Surjective f → IsAlt S' 5) : False := by
  classical
  refine letI : Fact p.Prime := ⟨hp⟩; ?_
  set Z : Subgroup G := ZOf (S ⊓ L) with hZdef
  set X : Subgroup G := R891X L Z n with hXdef
  have hQs : CFSG.Open.IsQuasisimple (Bar2 X) := by
    rcases hshape with ⟨hn1, -⟩ | ⟨-, -, hcov⟩ | ⟨-, -, hcov⟩
    · omega
    · exact hcov.1
    · exact hcov.1
  have hcenter3 : Nat.card (center (Bar2 X)) = 3 := by
    rcases hshape with ⟨hn1, -⟩ | ⟨-, -, hcov⟩ | ⟨-, -, hcov⟩
    · omega
    · exact hcov.2.1
    · exact hcov.2.1
  have hsimpleX : IsSimpleGroup (Bar2 X ⧸ center (Bar2 X)) := hQs.2
  let πH : ↥H →* F07.QuotK7 p H := QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)
  let Y : Subgroup (F07.QuotK7 p H) := F07.ImageModK p H X
  let q : ↥X →* ↥Y :=
    { toFun := fun x => ⟨πH ⟨(x : G), hXH x.2⟩,
        Subgroup.mem_map_of_mem πH (Subgroup.mem_subgroupOf.mpr x.2)⟩
      map_one' := Subtype.ext (by
        show πH (⟨(1 : G), hXH X.one_mem⟩ : ↥H) = 1
        rw [show (⟨(1 : G), hXH X.one_mem⟩ : ↥H) = 1 from Subtype.ext rfl]
        exact map_one πH)
      map_mul' := fun a b => Subtype.ext (by
        show πH (⟨((a * b : ↥X) : G), hXH (a * b).2⟩ : ↥H) =
          πH (⟨(a : G), hXH a.2⟩ : ↥H) * πH (⟨(b : G), hXH b.2⟩ : ↥H)
        rw [show (⟨((a * b : ↥X) : G), hXH (a * b).2⟩ : ↥H) =
          (⟨(a : G), hXH a.2⟩ : ↥H) * (⟨(b : G), hXH b.2⟩ : ↥H) from Subtype.ext rfl]
        exact map_mul πH _ _) }
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp y.2
    refine ⟨⟨(z : G), Subgroup.mem_subgroupOf.mp hz⟩, ?_⟩
    exact Subtype.ext (by simpa [q, πH] using hzy)
  let rX : ↥X →* Bar2 X := QuotientGroup.mk' (CFSG.pCore 2 ↥X)
  let SX := Bar2 X ⧸ center (Bar2 X)
  let r : ↥X →* SX := (QuotientGroup.mk' (center (Bar2 X))).comp rX
  have hr : Function.Surjective r :=
    (QuotientGroup.mk'_surjective (center (Bar2 X))).comp
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  let NX : Subgroup ↥X := (CFSG.pPrimeCore p ↥H).comap (Subgroup.inclusion hXH)
  have hqker : q.ker = NX := by
    ext x
    simp only [MonoidHom.mem_ker, NX, Subgroup.mem_comap]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (⟨(x : G), hXH x.2⟩ : ↥H)).mp
        (by simpa [q, πH] using congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext (by
        simpa [q, πH] using (QuotientGroup.eq_one_iff (⟨(x : G), hXH x.2⟩ : ↥H)).mpr hx)
  have hNXcenter : NX.map rX ≤ center (Bar2 X) := by
    have hNXn : NX.Normal := Subgroup.Normal.comap CFSG.pPrimeCore_normal (Subgroup.inclusion hXH)
    have hNrXn : (NX.map rX).Normal := hNXn.map rX (QuotientGroup.mk'_surjective _)
    refine letI : (NX.map rX).Normal := hNrXn; ?_
    rcases k891normzcong_normal_le_center_or_eq_top hQs.1 hsimpleX (NX.map rX) with h | h
    · exact h
    · exfalso
      have hpNX : ¬ p ∣ Nat.card ↥NX := by
        refine letI : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal; ?_
        have hle : NX.map (Subgroup.inclusion hXH) ≤ CFSG.pPrimeCore p ↥H := by
          intro y hy
          obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hy
          exact hn
        have hcard : Nat.card ↥(NX.map (Subgroup.inclusion hXH)) = Nat.card ↥NX :=
          Subgroup.card_map_of_injective (Subgroup.inclusion_injective hXH)
        have hdvd : Nat.card (NX.map (Subgroup.inclusion hXH)) ∣
            Nat.card (CFSG.pPrimeCore p ↥H) := Subgroup.card_dvd_of_le hle
        intro hpd
        exact (hp.coprime_iff_not_dvd.mp CFSG.pPrimeCore_coprime_card)
          (hpd.trans (hcard ▸ hdvd))
      have hdvd : Nat.card (Bar2 X) ∣ Nat.card ↥NX := by
        have h1 : Nat.card (NX.map rX) = Nat.card (Bar2 X) := by
          rw [h, Subgroup.card_top]
        rw [← h1]
        exact Subgroup.card_map_dvd NX rX
      exact hpNX (hpdvd.trans hdvd)
  have hker : q.ker ≤ r.ker := by
    rw [hqker]
    intro x hx
    rw [MonoidHom.mem_ker]
    show (QuotientGroup.mk' (center (Bar2 X))) (rX x) = 1
    exact (QuotientGroup.eq_one_iff (rX x)).mpr (hNXcenter (Subgroup.mem_map_of_mem rX hx))
  let eY := QuotientGroup.quotientKerEquivOfSurjective q hq
  let sX : (↥X ⧸ q.ker) →* SX := QuotientGroup.lift q.ker r hker
  let f : ↥Y →* SX := sX.comp eY.symm.toMonoidHom
  have hf : Function.Surjective f := by
    have hsX : Function.Surjective sX :=
      QuotientGroup.lift_surjective_of_surjective q.ker r hr hker
    exact hsX.comp eY.symm.surjective
  have hYle : Y ≤ F07.ImageModK p H (H ⊓ D.M) := by
    show F07.ImageModK p H X ≤ F07.ImageModK p H (H ⊓ D.M)
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H (le_inf hXH hXM))
  have hYperf : ⁅Y, Y⁆ = Y := by
    show ⁅F07.ImageModK p H X, F07.ImageModK p H X⁆ = F07.ImageModK p H X
    rw [F07.ImageModK, ← Subgroup.map_commutator]
    have hsubperf : ⁅X.subgroupOf H, X.subgroupOf H⁆ = X.subgroupOf H := by
      rw [← CFSG.LocalAnalysis.GLTheoremB.subgroupOf_commutator (X := H) hXH hXH, hXperf]
    rw [hsubperf]
  have hAltSX : IsAlt SX 5 := hA5all Y hYle hYperf SX hsimpleX f hf
  obtain ⟨e5⟩ := hAltSX
  have hcardSX : Nat.card SX = 60 := by
    rw [Nat.card_congr e5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    norm_num
  have hcardBar2 : Nat.card (Bar2 X) = 180 := by
    have h1 : Nat.card (Bar2 X) = Nat.card SX * Nat.card (center (Bar2 X)) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (center (Bar2 X))
    rw [h1, hcardSX, hcenter3]
  have hord := hPrime.2.1 (Bar2 X) n hshape
  have hpi : R891Pi n = 1 ∨ R891Pi n = -1 := by
    rcases Nat.even_or_odd n with h | h
    · exact Or.inl (by rw [R891Pi]; exact Even.neg_one_pow h)
    · exact Or.inr (by rw [R891Pi]; exact Odd.neg_one_pow h)
  have hge : (60480 : ℤ) ≤ 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) - R891Pi n) := by
    have h3n : 6 ≤ 3 * n := by omega
    have h2n : 4 ≤ 2 * n := by omega
    have hA : (64 : ℤ) ≤ 2 ^ (3 * n) := by
      calc (64 : ℤ) = 2 ^ 6 := by norm_num
        _ ≤ 2 ^ (3 * n) := pow_le_pow_right₀ (by norm_num) h3n
    have hB : (15 : ℤ) ≤ 2 ^ (2 * n) - 1 := by
      have h16 : (16 : ℤ) ≤ 2 ^ (2 * n) := by
        calc (16 : ℤ) = 2 ^ 4 := by norm_num
          _ ≤ 2 ^ (2 * n) := pow_le_pow_right₀ (by norm_num) h2n
      omega
    have hC : (63 : ℤ) ≤ 2 ^ (3 * n) - R891Pi n := by
      rcases hpi with h | h <;> rw [h] <;> omega
    have hA0 : (0 : ℤ) ≤ 2 ^ (3 * n) := by positivity
    have hB0 : (0 : ℤ) ≤ 2 ^ (2 * n) - 1 := by linarith
    have hC0 : (0 : ℤ) ≤ 2 ^ (3 * n) - R891Pi n := by linarith
    have hAB : (64 : ℤ) * 15 ≤ 2 ^ (3 * n) * (2 ^ (2 * n) - 1) :=
      mul_le_mul hA hB (by norm_num) hA0
    have hAB0 : (0 : ℤ) ≤ 2 ^ (3 * n) * (2 ^ (2 * n) - 1) := by positivity
    calc (60480 : ℤ) = 64 * 15 * 63 := by norm_num
      _ ≤ 2 ^ (3 * n) * (2 ^ (2 * n) - 1) * (2 ^ (3 * n) - R891Pi n) :=
          mul_le_mul hAB hC (by norm_num) hAB0
  rw [← hord] at hge
  rw [hcardBar2] at hge
  norm_num at hge

private theorem k891normzcong_arith {p n N : ℕ} (hpp : p.Prime) (hp2 : p ≠ 2)
    (hcard : (N : ℤ) = (2 : ℤ) ^ (3 * n) * ((2 : ℤ) ^ (2 * n) - 1) *
      ((2 : ℤ) ^ (3 * n) - R891Pi n))
    (hdvd6 : p ∣ 2 ^ (6 * n) - 1) (hNnot : ¬ p ∣ N) :
    ((2 : ℤ) ^ (3 * n) ≡ -R891Pi n [ZMOD p]) ∧
      ¬ ((2 : ℤ) ^ n ≡ -R891Pi n [ZMOD p]) := by
  have hpi : R891Pi n = 1 ∨ R891Pi n = -1 := by
    rcases Nat.even_or_odd n with h | h
    · exact Or.inl (by rw [R891Pi]; exact Even.neg_one_pow h)
    · exact Or.inr (by rw [R891Pi]; exact Odd.neg_one_pow h)
  have hprimeZ : Prime (p : ℤ) := by
    rw [Int.prime_iff_natAbs_prime]
    simpa using hpp
  have hNnotZ : ¬ (p : ℤ) ∣ (N : ℤ) := fun h => hNnot (Int.natCast_dvd_natCast.mp h)
  have hnotA : ¬ (p : ℤ) ∣ (2 : ℤ) ^ (3 * n) := by
    intro h
    have h2 : (p : ℤ) ∣ 2 := hprimeZ.dvd_of_dvd_pow h
    have h2' : p ∣ 2 := by exact_mod_cast h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).mp h2')
  have hdvd6Z : (p : ℤ) ∣ (2 : ℤ) ^ (6 * n) - 1 := by
    have h := Int.natCast_dvd_natCast.mpr hdvd6
    have hcast : ((2 ^ (6 * n) - 1 : ℕ) : ℤ) = (2 : ℤ) ^ (6 * n) - 1 := by
      rw [Nat.cast_sub ((Nat.one_le_two_pow (n := 6 * n)))]
      push_cast; ring
    rwa [hcast] at h
  have hfac : (2 : ℤ) ^ (6 * n) - 1 =
      ((2 : ℤ) ^ (3 * n) - R891Pi n) * ((2 : ℤ) ^ (3 * n) + R891Pi n) := by
    have hsq : ((2 : ℤ) ^ (3 * n)) ^ 2 = (2 : ℤ) ^ (6 * n) := by
      rw [← pow_mul]; congr 1; ring
    have hpi2 : R891Pi n ^ 2 = 1 := by rcases hpi with h | h <;> rw [h] <;> norm_num
    rw [← hsq]; ring_nf; rw [hpi2]
  have hprod : ¬ (p : ℤ) ∣ ((2 : ℤ) ^ (2 * n) - 1) * ((2 : ℤ) ^ (3 * n) - R891Pi n) := by
    intro h
    apply hNnotZ
    rw [hcard, mul_assoc]
    exact dvd_mul_of_dvd_right h _
  have hnotB : ¬ (p : ℤ) ∣ (2 : ℤ) ^ (2 * n) - 1 :=
    fun h => hprod (dvd_mul_of_dvd_left h _)
  have hnotC : ¬ (p : ℤ) ∣ (2 : ℤ) ^ (3 * n) - R891Pi n :=
    fun h => hprod (dvd_mul_of_dvd_right h _)
  have hdvd : (p : ℤ) ∣ (2 : ℤ) ^ (3 * n) + R891Pi n := by
    have h : (p : ℤ) ∣ ((2 : ℤ) ^ (3 * n) - R891Pi n) * ((2 : ℤ) ^ (3 * n) + R891Pi n) := by
      rw [← hfac]; exact hdvd6Z
    rcases hprimeZ.dvd_mul.mp h with h1 | h1
    · exact absurd h1 hnotC
    · exact h1
  constructor
  · rw [Int.modEq_iff_dvd]
    have := dvd_neg.mpr hdvd
    convert this using 1; ring
  · intro hmod
    have h2 : ((2 : ℤ) ^ (2 * n) ≡ 1 [ZMOD p]) := by
      have h := Int.ModEq.pow 2 hmod
      have hpi2 : R891Pi n ^ 2 = 1 := by rcases hpi with h' | h' <;> rw [h'] <;> norm_num
      have hmul : ((2 : ℤ) ^ n) ^ 2 = (2 : ℤ) ^ (2 * n) := by
        rw [← pow_mul]; congr 1; ring
      have hpneg : (-R891Pi n) ^ 2 = R891Pi n ^ 2 := by ring
      rw [hmul, hpneg, hpi2] at h
      exact h
    rw [Int.modEq_iff_dvd] at h2
    apply hnotB
    have h3 : (p : ℤ) ∣ (2 : ℤ) ^ (2 * n) - 1 := by
      have h2' : (p : ℤ) ∣ -((2 : ℤ) ^ (2 * n) - 1) := by
        convert h2 using 1; ring
      exact dvd_neg.mp h2'
    exact h3


private theorem k891normzcong_false_of_pdvd {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (h72 : R72 D) (hKF7 : KStrongEmbedded72) (hPrime : R891PrimeCore)
    (L S : Subgroup G) (n p : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (hshape : R891SL3Two (Bar2 (R891X L (ZOf (S ⊓ L)) n)) n)
    (hrank : R891Rank893 D L) (hnotle : R891NotLe D L S)
    (hpp : p.Prime) (hp2 : p ≠ 2) (hpSig : p ∈ D.sig) (hn2 : 2 ≤ n)
    (hpdvd : p ∣ Nat.card (Bar2 (R891X L (ZOf (S ⊓ L)) n))) : False := by
  classical
  refine letI : Fact p.Prime := ⟨hpp⟩; ?_
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hset.mem
  have hsp : IsStronglyPEmbedded p D.M := sp_of_mem_sig hSg hns hpSig
  refine letI : IsSimpleGroup G := D.standing.simple; ?_
  have hcenterG : Subgroup.center G = ⊥ :=
    CFSG.GorensteinWalter.Helpers.center_eq_bot_of_noncommutative D.standing.nonab
  set Z : Subgroup G := ZOf (S ⊓ L) with hZdef
  set X : Subgroup G := R891X L Z n with hXdef
  set H : Subgroup G := centralizer (Z : Set G) with hHdef
  have hHne : H ≠ ⊤ := by
    intro htop
    have hZtop : Z ≤ Subgroup.center G := by
      intro z hz
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ centralizer (Z : Set G) := by
        rw [← hHdef]
        exact htop ▸ Subgroup.mem_top g
      exact (Subgroup.mem_centralizer_iff.mp hg z hz).symm
    have hZbot : Z = ⊥ := le_bot_iff.mp (hcenterG ▸ hZtop)
    have hcardZ : Nat.card Z = 3 := hbasic.zOrder
    rw [hZbot, Subgroup.card_bot] at hcardZ
    omega
  have hrank2 : 1 < CFSG.Open.pRank p (H ⊓ D.M) := by
    have h2 := k891normzcong_two_le_pRank_centralizer hpp hp2 hset hbasic hrank hpSig hpdvd
    have h2' : 2 ≤ CFSG.Open.pRank p (H ⊓ D.M) := by
      rw [show H ⊓ D.M = D.M ⊓ centralizer (Z : Set G) by
        rw [hHdef]
        exact inf_comm _ _]
      exact h2
    omega
  have hS7 : F07.Sec7Hyp D p H := ⟨hpp, hp2, hsp, hHne, hnotle.2, hrank2⟩
  have hXperf : ⁅X, X⁆ = X := by
    rw [hXdef]; exact k891normzcong_X_perfect (by omega : n ≠ 1)
  have hXleH : X ≤ H := by
    rw [hXdef, hHdef]; exact (k891normzcong_R891X_le L Z n).trans inf_le_right
  have hXleM : X ≤ D.M := by
    rw [hXdef]
    exact (k891normzcong_R891X_le L Z n).trans inf_le_left |>.trans hset.mem.1.le
  have hpX : p ∣ Nat.card X := by
    have h2 : Nat.card (Bar2 X) ∣ Nat.card X := by
      show Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ∣ Nat.card ↥X
      exact Subgroup.card_quotient_dvd_card _
    exact hpdvd.trans h2
  rcases solvable_or_altTen_of_sec7Hyp h72 hKF7 hS7 with hsol | ⟨hp5, hNorm, hF, hAlt, hA5all⟩
  · have hJN : X ≤ H ⊓ D.M := le_inf hXleH hXleM
    have hJcore : X ≤ F07.PPrimeCoreIn p H :=
      le_pPrimeCoreIn_of_isSolvable inf_le_left hJN hXperf hsol
    have hcop : Nat.Coprime p (Nat.card (F07.PPrimeCoreIn p H)) := by
      refine letI : (CFSG.pPrimeCore p ↥H).Normal := CFSG.pPrimeCore_normal; ?_
      have hcard : Nat.card (F07.PPrimeCoreIn p H) = Nat.card (CFSG.pPrimeCore p ↥H) :=
        Subgroup.card_map_of_injective H.subtype_injective
      rw [hcard]
      exact CFSG.pPrimeCore_coprime_card
    exact (hpp.coprime_iff_not_dvd.mp hcop) (hpX.trans (Subgroup.card_dvd_of_le hJcore))
  · exact k891normzcong_altTen_false hpp hp2 hn2 hPrime hshape hXperf H hXleH hXleM hpdvd hA5all

theorem s891_norm_z_cong
    {G : Type} [Group G] [Finite G] (D : Data G)
    (hSg : SigmaStd D) (h72 : R72 D) (hPrime : R891PrimeCore)
    (L S R A : Subgroup G) (n : ℕ) (hset : R891Set D L S n) (hbasic : R891Basic D L S)
    (hctx : R891Ctx D L S n R A) (hrank : R891Rank893 D L) (hnotle : R891NotLe D L S) :
    R891Cong D n := by
  have hKF7 := kStrongEmbedded72_holds
  classical
  intro p hpSig
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hpSig
  refine letI : Fact p.Prime := ⟨hpp⟩; ?_
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hset.mem
  have hsp : IsStronglyPEmbedded p D.M := sp_of_mem_sig hSg hns hpSig
  have hp3 : p ≠ 3 := by
    intro h3; subst h3; exact hset.notStrong hsp
  have hp4 : p ≠ 4 := by rintro rfl; norm_num at hpp
  have hp2le : 2 ≤ p := hpp.two_le
  have hp5 : 5 ≤ p := by omega
  have hn0 : n ≠ 0 := by
    intro hn0
    subst hn0
    have hD4 := (hPrime.1 (Bar2 L) 0 hset.d4).1
    norm_num at hD4
    exact Nat.card_pos.ne' hD4
  have hn1 : 1 ≤ n := Nat.pos_of_ne_zero hn0
  have hpDvd6 : p ∣ 2 ^ (6 * n) - 1 := by
    have hD4 := hPrime.1 (Bar2 L) n hset.d4
    have hrankbar2 : CFSG.Open.pRank p (⊤ : Subgroup (Bar2 L)) = 2 := by
      have hbar := CFSG.AGLEmbedding.pRank_barM_eq hpp hp2 L L le_rfl
      have hbarM : CFSG.AGLEmbedding.barM L L = ⊤ := by
        rw [CFSG.AGLEmbedding.barM, Subgroup.subgroupOf_self, Subgroup.map_top,
          MonoidHom.range_eq_top]
        exact QuotientGroup.mk'_surjective _
      rw [hbarM] at hbar
      rw [hbar]
      exact (hrank p hpSig).1
    exact (hD4.2 p hpp hp5).2.1.mp hrankbar2
  have hXi : ¬ p ∣ Nat.card (Bar2 (R891X L (ZOf (S ⊓ L)) n)) := by
    intro hpdvd
    by_cases hn1' : n = 1
    · subst hn1'
      have hcard := hPrime.2.1 (Bar2 (R891X L (ZOf (S ⊓ L)) 1)) 1 hctx.xShape.xShape
      have hp7 : p = 7 := by
        have h63 : p ∣ 63 := by norm_num at hpDvd6 ⊢; exact hpDvd6
        have h321 : p ∣ 3 * 21 := by norm_num at h63 ⊢; exact h63
        rcases hpp.dvd_mul.mp h321 with h3 | h21
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h3) hp3
        · have h37 : p ∣ 3 * 7 := by norm_num at h21 ⊢; exact h21
          rcases hpp.dvd_mul.mp h37 with h3 | h7
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).mp h3) hp3
          · exact (Nat.prime_dvd_prime_iff_eq hpp Nat.prime_seven).mp h7
      have h216 : Nat.card (Bar2 (R891X L (ZOf (S ⊓ L)) 1)) = 216 := by
        norm_num [R891Pi] at hcard
        exact_mod_cast hcard
      rw [hp7, h216] at hpdvd
      norm_num at hpdvd
    · have hn2 : 2 ≤ n := by omega
      exact k891normzcong_false_of_pdvd D hSg h72 hKF7 hPrime L S n p hset hbasic
        hctx.xShape.xShape hrank hnotle hpp hp2 hpSig hn2 hpdvd
  have hcard := hPrime.2.1 (Bar2 (R891X L (ZOf (S ⊓ L)) n)) n hctx.xShape.xShape
  exact k891normzcong_arith hpp hp2 hcard hpDvd6 hXi


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
