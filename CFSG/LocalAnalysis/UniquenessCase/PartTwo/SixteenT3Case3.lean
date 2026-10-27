module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase153
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R1613gCase168
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCOdd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLinesPlanes
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.HardMathSupport.Foote.E27.TableMat
public import CFSG.LieType.CurtisTits.SpecialLinear
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoConfig
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoEscape
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycSmall
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrHom
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrXGen
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ZZPrimeDefs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeMax
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalOddCentralizer
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotCatAlt
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDeltaBound
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyOddOMinus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenWitt
public import CFSG.Quasithin.Background.G11Stmts
public import CFSG.RankThree.GroupTheory.SteinbergBMTwoPartCommutatorsOdd
public import CFSG.RankThree.PartOne.KC.LinearPrimeFieldActorSolvableCore
public import CFSG.RankThree.PartOne.KC.OrthogonalHighWittFixedSpace
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldFixed
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.RankThree.SteinbergR3EOrthogonalCoprimeCyclic
public import Certificates.Data.E27Q2O

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16t_pCoreOf_le_fstarBar (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    (p : ℕ) [Fact p.Prime] : pCoreOf p (Mbar D.M V₀ V hV) ≤ fstarBar D.M V₀ V hV := by
  unfold pCoreOf fstarBar Fstar
  refine Subgroup.map_mono ?_
  rw [genFittingFStar.eq_sup]
  exact (CFSG.pCore_le_fitting _ p).trans le_sup_left

theorem s16t_fstarBar_conj_mem (D : Data G) {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {φ : MulAut (Vtil V₀ V hV)} (hφ : φ ∈ Mbar D.M V₀ V hV) {x : MulAut (Vtil V₀ V hV)}
    (hx : x ∈ fstarBar D.M V₀ V hV) : φ * x * φ⁻¹ ∈ fstarBar D.M V₀ V hV := by
  have hN : (Subgroup.comap (Mbar D.M V₀ V hV).subtype (fstarBar D.M V₀ V hV)).Normal := by
    show (Subgroup.comap (Mbar D.M V₀ V hV).subtype
      ((genFittingFStar ↥(Mbar D.M V₀ V hV)).map (Mbar D.M V₀ V hV).subtype)).Normal
    rw [Subgroup.comap_map_eq_self_of_injective (Mbar D.M V₀ V hV).subtype_injective]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal _
  have hxM : x ∈ Mbar D.M V₀ V hV := Subgroup.map_subtype_le _ hx
  exact hN.conj_mem ⟨x, hxM⟩ hx ⟨φ, hφ⟩

private theorem s16t_c3_mem_stabTil {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (m : D.M) : (m : G) ∈ stabTil V₀ V :=
  le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀ m.2

private theorem s16t_c3_barSub_conj_le (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    {E : Subgroup (MulAut (Vtil V₀ V hV))}
    (hEn : ∀ φ ∈ Mbar D.M V₀ V hV, ∀ x ∈ E, φ * x * φ⁻¹ ∈ E)
    (hLE : barSub V₀ V hV L ≤ E) (m : D.M) :
    barSub V₀ V hV (conjSubgroup L (m : G)) ≤ E := by
  have hm : (m : G) ∈ stabTil V₀ V := s16t_c3_mem_stabTil h m
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV hm L]
  intro y hy
  rw [Subgroup.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  have hα : (actTil V₀ V hV ⟨(m : G), hm⟩)⁻¹ ∈ Mbar D.M V₀ V hV :=
    Subgroup.inv_mem _ (actTil_mem_barSub V₀ V hV m.2 hm)
  exact hEn _ hα x (hLE hx)

private theorem s16t_c3_card_barSub_conj (D : Data G) {V₀ V L : Subgroup G}
    (h : Hyp151 D V₀ V L) (hV : IsElemAbelian 2 V)
    (hL3 : Nat.card ↥(barSub V₀ V hV L) = 3) (m : D.M) :
    Nat.card ↥(barSub V₀ V hV (conjSubgroup L (m : G))) = 3 := by
  have hm : (m : G) ∈ stabTil V₀ V := s16t_c3_mem_stabTil h m
  rw [s15_Infra_barSub_conjSubgroup V₀ V hV hm L,
    Subgroup.card_map_of_injective (MulAut.conj _).injective]
  exact hL3

theorem s16t_s15_le_two (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hL : barSub V₀ V hV L ≠ ⊥)
    {E : Subgroup (MulAut (Vtil V₀ V hV))} (hE : Nat.card ↥E = 9)
    (hEn : ∀ φ ∈ Mbar D.M V₀ V hV, ∀ x ∈ E, φ * x * φ⁻¹ ∈ E)
    (hLE : barSub V₀ V hV L ≤ E) (hL3 : Nat.card ↥(barSub V₀ V hV L) = 3) :
    s15 D.M V₀ V hV L ≤ 2 := by
  by_contra hle
  rw [not_le] at hle
  have hcard : ∀ m : D.M, Nat.card ↥(barSub V₀ V hV (conjSubgroup L (m : G))) = 3 :=
    s16t_c3_card_barSub_conj D h hV hL3
  have hleE : ∀ m : D.M, barSub V₀ V hV (conjSubgroup L (m : G)) ≤ E :=
    s16t_c3_barSub_conj_le D h hV hEn hLE
  have hrange : s15 D.M V₀ V hV L =
      (Set.range fun m : D.M => barSub V₀ V hV (conjSubgroup L (m : G))).ncard :=
    s15_Core_s15_eq_ncard_range h
  rw [hrange] at hle
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite _)).1 hle
  obtain ⟨m₁, rfl⟩ := ha
  obtain ⟨m₂, hb'⟩ := hb
  obtain ⟨m₃, hc'⟩ := hc
  rw [← hb'] at hab hbc
  rw [← hc'] at hac hbc
  have hn₂ : (m₂ : G) * (m₁ : G)⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hmem
    exact hab ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV m₁.2 m₂.2).1 hmem).symm
  have hn₃ : (m₃ : G) * (m₁ : G)⁻¹ ∉ nBar D.M V₀ V hV L := by
    intro hmem
    exact hac ((s15_Infra_mul_inv_mem_nBar_iff h.hyp125 hV m₁.2 m₃.2).1 hmem).symm
  have hcomm₂ : commSub (commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))))
      (barSub V₀ V hV (conjSubgroup L (m₂ : G))) = ⊥ :=
    (s15_Kbar_commute_conj h m₁.2 m₂.2 hn₂).2
  have hcomm₃ : commSub (commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))))
      (barSub V₀ V hV (conjSubgroup L (m₃ : G))) = ⊥ :=
    (s15_Kbar_commute_conj h m₁.2 m₃.2 hn₃).2
  have hUle₂ : commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))) ≤
      fixV (barSub V₀ V hV (conjSubgroup L (m₂ : G))) := commSub_eq_bot_iff.mp hcomm₂
  have hUle₃ : commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))) ≤
      fixV (barSub V₀ V hV (conjSubgroup L (m₃ : G))) := commSub_eq_bot_iff.mp hcomm₃
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE9 : Nat.card ↥E = 3 ^ 2 := by rw [hE]; norm_num
  have hsup23 : barSub V₀ V hV (conjSubgroup L (m₂ : G)) ⊔
      barSub V₀ V hV (conjSubgroup L (m₃ : G)) = E :=
    CFSG.LocalAnalysis.RankThreeTheoremC.sup_eq_of_card_eq_prime
      (hcard m₂) (hcard m₃) hbc (hleE m₂) (hleE m₃) hE9
  have hfix : commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))) ≤
      fixV (barSub V₀ V hV (conjSubgroup L (m₁ : G))) := by
    have h1 : commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))) ≤
        fixV (barSub V₀ V hV (conjSubgroup L (m₂ : G)) ⊔
          barSub V₀ V hV (conjSubgroup L (m₃ : G))) := by
      rw [FixVLat.fixV_sup_eq]
      exact le_inf hUle₂ hUle₃
    have h2 : fixV (barSub V₀ V hV (conjSubgroup L (m₂ : G)) ⊔
          barSub V₀ V hV (conjSubgroup L (m₃ : G))) ≤
        fixV (barSub V₀ V hV (conjSubgroup L (m₁ : G))) := by
      intro v hv
      rw [mem_fixV] at hv ⊢
      intro x hx
      exact hv x (by rw [hsup23]; exact hleE m₁ hx)
    exact h1.trans h2
  have hbot : commSub (commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))))
      (barSub V₀ V hV (conjSubgroup L (m₁ : G))) = ⊥ := commSub_eq_bot_iff.mpr hfix
  have hUU : commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))) = ⊥ := by
    have hthis := s15_Core_commSub_wTil_conj h m₁.2
    rw [show wTil V₀ V hV (conjSubgroup L (m₁ : G)) =
      commSub ⊤ (barSub V₀ V hV (conjSubgroup L (m₁ : G))) from rfl] at hthis
    exact hthis.symm.trans hbot
  have hK₁bot : barSub V₀ V hV (conjSubgroup L (m₁ : G)) = ⊥ :=
    s15_Lin_eq_bot_of_commSub_top_eq_bot hUU
  exact hL ((s15_Core_barSub_conj_eq_bot_iff h m₁.2).1 hK₁bot)

theorem s16t_rk_vtil_le (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    (h : Hyp151 D ⊥ V L) (hV : IsElemAbelian 2 V) (hL : barSub ⊥ V hV L ≠ ⊥) :
    rk ↥(⊤ : Subgroup (Vtil ⊥ V hV)) ≤ s15 D.M ⊥ V hV L * rk ↥(wTil ⊥ V hV L) := by
  classical
  let K : D.M → Subgroup (MulAut (Vtil ⊥ V hV)) :=
    fun m => barSub ⊥ V hV (conjSubgroup L (m : G))
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp125.pairFacts.le_normalizer h.hyp125.pairFacts.le_normalizer₀
  have hspan : (⨆ m : D.M, wTil ⊥ V hV (conjSubgroup L (m : G))) = ⊤ := by
    have h1 := iSup_wConj_eq D h1217 h hV hL
    rw [s15_Two_wConj_eq_range D.M ⊥ V L hV, iSup_range] at h1
    have hle : ∀ m : D.M, conjSubgroup (wSub ⊥ V hV L) (m : G) ≤ V := by
      intro m x hx
      rw [mem_conjSubgroup_iff] at hx
      exact (Subgroup.mem_normalizer_iff.1 (h.hyp125.pairFacts.le_normalizer m.2) x).2
        (preTil_le ⊥ V hV _ hx)
    have h2 : (⨆ m : D.M, imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L) (m : G))) = ⊤ := by
      have h := congrArg (imgTil ⊥ V hV) h1
      rwa [s15_Core_imgTil_iSup ⊥ V hV
          (fun m : D.M => conjSubgroup (wSub ⊥ V hV L) (m : G)) hle,
        s15_Infra_imgTil_top] at h
    rw [← h2]
    refine iSup_congr fun m => ?_
    show wTil ⊥ V hV (conjSubgroup L (m : G)) =
      imgTil ⊥ V hV (conjSubgroup (wSub ⊥ V hV L) (m : G))
    rw [← s15_Infra_wSub_conjSubgroup ⊥ V L hV (hMs m.2)]
    exact (imgTil_preTil ⊥ V hV (wTil ⊥ V hV (conjSubgroup L (m : G)))).symm
  haveI : Fintype ↥(Set.range K) := (Set.finite_range K).fintype
  have hsup : (⨆ b : ↥(Set.range K), commSub ⊤ (b : Subgroup (MulAut (Vtil ⊥ V hV)))) = ⊤ := by
    rw [iSup_range' (fun b : Subgroup (MulAut (Vtil ⊥ V hV)) => commSub ⊤ b) K]
    exact hspan
  have hrk : ∀ m : D.M, rk ↥(commSub ⊤ (K m)) = rk ↥(wTil ⊥ V hV L) := by
    intro m
    have hwt : commSub ⊤ (K m) =
        (wTil ⊥ V hV L).map ((actTil ⊥ V hV ⟨(m : G), hMs m.2⟩)⁻¹).toMonoidHom :=
      s15_Infra_wTil_conjSubgroup ⊥ V L hV (hMs m.2)
    rw [hwt, s15_Lin_rk_map]
  have hsum : (∑ b : ↥(Set.range K),
        rk ↥(commSub ⊤ (b : Subgroup (MulAut (Vtil ⊥ V hV))))) =
      s15 D.M ⊥ V hV L * rk ↥(wTil ⊥ V hV L) := by
    have hterm : ∀ b : ↥(Set.range K),
        rk ↥(commSub ⊤ (b : Subgroup (MulAut (Vtil ⊥ V hV)))) = rk ↥(wTil ⊥ V hV L) := by
      intro b
      obtain ⟨m, hm⟩ := b.2
      rw [← hm]
      exact hrk m
    rw [Finset.sum_congr rfl (fun b _ => hterm b), Finset.sum_const, Finset.card_univ,
      Fintype.card_eq_nat_card, Nat.card_coe_set_eq, smul_eq_mul]
    congr 1
    exact (s15_Core_s15_eq_ncard_range h).symm
  calc rk ↥(⊤ : Subgroup (Vtil ⊥ V hV))
      = rk ↥(⨆ b : ↥(Set.range K), commSub ⊤ (b : Subgroup (MulAut (Vtil ⊥ V hV)))) := by
        rw [hsup]
    _ ≤ ∑ b : ↥(Set.range K),
          rk ↥(commSub ⊤ (b : Subgroup (MulAut (Vtil ⊥ V hV)))) :=
        r1613g_rk_iSup_le _
    _ = s15 D.M ⊥ V hV L * rk ↥(wTil ⊥ V hV L) := hsum

theorem s16t_false_of_case153_3 (D : Data G) (h1217 : R1217 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (h : Case153_3 D ⊥ V hV L) :
    False := by
  obtain ⟨hcard, hrk⟩ := r1613g_case153_3_summary D hc.conc h
  obtain ⟨hE, hrk8, -⟩ := r1613g_case168_eight_of_card_three D hcard hrk hc.concl168
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hLp : IsPGroup 3 ↥(lBar ⊥ V hV L) := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hcard)
  have hLE : lBar ⊥ V hV L ≤ fstarBar D.M ⊥ V hV :=
    (s16c13bc_lBar_le_pCoreOf D hV hc Nat.prime_three hLp hc.ne_bot).trans
      (s16t_pCoreOf_le_fstarBar D hV 3)
  have hE9 : Nat.card ↥(fstarBar D.M ⊥ V hV) = 9 := by
    simpa using s16c167_card_isElemAbelianOfRank hE
  have hs := s16t_s15_le_two D hc.setting.hyp151 hV hc.ne_bot hE9
    (fun φ hφ x hx => s16t_fstarBar_conj_mem D hV hφ hx) hLE hcard
  have hb := s16t_rk_vtil_le D h1217 hc.setting.hyp151 hV hc.ne_bot
  rw [hrk8] at hb
  have := Nat.mul_le_mul hs hrk
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
