module

public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeK2
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteenLift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Shape
public import CFSG.Quasithin.EmptyFaithful.S151S4D

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def RSchurOm6 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], CFSG.Open.IsQuasisimple X →
    IsU4 (X ⧸ Subgroup.center X) 1 → Nat.card (Subgroup.center X) ∣ 2

private theorem s16c1_statedClassicalModel_psu_four_one {L : Type} [Group L]
    {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hK : Nat.card K = 2 ^ 1) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (e : L ⧸ Subgroup.center L ≃* StatedOmega (StatedQuadMinus 3 K b c) ⧸
      Subgroup.center (StatedOmega (StatedQuadMinus 3 K b c))) :
    StatedClassicalModel (L ⧸ Subgroup.center L) .PSU 4 2 1 := by
  obtain ⟨E, _, h, ⟨eSU⟩⟩ :=
    CFSG.ComponentClassification.RankTwoClassical.nonempty_statedOmega_quadMinus_three_equiv
      (m := 1) hK hirr
  have hE := h.card_eq_sq
  have := h.finite
  have hnq : ((4 : ℕ), 2 ^ 1) ≠ (3, 2) := by decide
  refine ⟨⟨Nat.prime_two, le_refl 1, by norm_num, hnq⟩, E, inferInstance, h.finite, hE,
    ⟨(e.trans (QuotientGroup.congr _ _ eSU (Subgroup.map_center_eq _))).trans
      (QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hE (by norm_num)
          hnq).2)⟩⟩

theorem isU4_of_isOmegaMinus_six {X : Type} [Group X] (h : IsOmegaMinus X 6 1) : IsU4 X 1 := by
  have hdiv : (6 : ℕ) / 2 = 3 := by norm_num
  simp only [IsOmegaMinus, hdiv] at h
  obtain ⟨-, K, hKfield, hKfinite, b, c, hcard, hirr, ⟨e⟩⟩ := h
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  haveI : Fintype K := Fintype.ofFinite K
  have hcard2 : Nat.card K = 2 := by rw [hcard]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime (p := 2) (by rw [Fintype.card_eq_nat_card, hcard2])
  have hfacts :=
    CFSG.ComponentClassification.RankTwoClassical.isSimpleGroup_statedOmega_quadMinus_small
      (n := 3) (b := b) (c := c) (Or.inr rfl) hirr
  haveI : IsSimpleGroup (StatedOmega (StatedQuadMinus 3 K b c)) := hfacts.1
  have hqΩ :=
    CFSG.ComponentClassification.RankTwoClassical.isQuasisimple_of_isSimpleGroup hfacts.2.2
  have hSbot : (StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
      (StatedOmega (StatedQuadMinus 3 K b c)) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K).subgroupOf
        (StatedOmega (StatedQuadMinus 3 K b c))) with hS | hS
    · exact hS
    · exfalso
      have hle : StatedOmega (StatedQuadMinus 3 K b c) ≤
          StatedScalars (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K :=
        Subgroup.subgroupOf_eq_top.1 hS
      exact hfacts.2.2 fun x y => Subtype.ext <| by
        have hx : (x : Matrix.GeneralLinearGroup (Fin (3 - 1) ⊕ Fin (3 - 1) ⊕ Fin 2) K) ∈
            Subgroup.center _ := by
          rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
          exact hle x.2
        exact (Subgroup.mem_center_iff.mp hx (y : _)).symm
  have eN : StatedProj (StatedOmega (StatedQuadMinus 3 K b c)) ≃*
      StatedOmega (StatedQuadMinus 3 K b c) :=
    (QuotientGroup.quotientMulEquivOfEq hSbot).trans QuotientGroup.quotientBot
  have eX : X ≃* StatedOmega (StatedQuadMinus 3 K b c) := e.trans eN
  have hZ : Subgroup.center X = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center X) eX.injective).1 <| by
      rw [Subgroup.map_center_eq eX, hqΩ.2]
  have e' : X ⧸ Subgroup.center X ≃*
      StatedOmega (StatedQuadMinus 3 K b c) ⧸
        Subgroup.center (StatedOmega (StatedQuadMinus 3 K b c)) :=
    QuotientGroup.congr _ _ eX (Subgroup.map_center_eq eX)
  have hmodel : CFSG.Blueprint.LieModel (X ⧸ Subgroup.center X) .PSU 4 2 1 :=
    (CFSG.Blueprint.LieModel.classical_iff (t := .PSU) (by decide)).2
      (s16c1_statedClassicalModel_psu_four_one hcard hirr e')
  exact CFSG.Blueprint.LieModel.of_quotient_center hZ hmodel

theorem isU4_bar2_of_covers (hSchur : RSchurOm6) {M K : Subgroup G} (hK : K ∈ calC M)
    {Y : Type} [Group Y] (hY : IsOmegaMinus Y 6 1) (e : (Bar2 K ⧸ Subgroup.center (Bar2 K)) ≃* Y) :
    IsU4 (Bar2 K) 1 := by
  have hU4bar : IsU4 (Bar2 K ⧸ Subgroup.center (Bar2 K)) 1 :=
    CFSG.Blueprint.LieModel.of_mulEquiv e.symm (isU4_of_isOmegaMinus_six hY)
  have hcard : Nat.card (Subgroup.center (Bar2 K)) ∣ 2 :=
    hSchur (Bar2 K) hK.2.2 hU4bar
  have hZpg : IsPGroup 2 (Subgroup.center (Bar2 K)) :=
    IsPGroup.of_card_dvd_pow (p := 2) (n := 1) (by simpa using hcard)
  have hZle : Subgroup.center (Bar2 K) ≤ CFSG.pCore 2 (Bar2 K) :=
    le_sSup (s := {N : Subgroup (Bar2 K) | N.Normal ∧ IsPGroup 2 N}) ⟨inferInstance, hZpg⟩
  rw [CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveThirteen.pCore_bar2_eq_bot K] at hZle
  have hZ : Subgroup.center (Bar2 K) = ⊥ := le_bot_iff.1 hZle
  exact CFSG.Blueprint.LieModel.of_quotient_center hZ hU4bar

theorem sect16_of_barSub_eq (D : Data G) {V₀ V L K : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) (hKM : K ≤ D.M) (hKperf : ⁅K, K⁆ = K)
    (hbar : barSub V₀ V hV K = barSub V₀ V hV L) :
    Sect16 D V₀ V K hV ∧ Case167_1 D V₀ V hV K := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.setting.hyp16.hyp125.pairFacts.le_normalizer
      hS.setting.hyp16.hyp125.pairFacts.le_normalizer₀
  have hMemNBar : ∀ g ∈ D.M, g ∈ nBar D.M V₀ V hV K := by
    intro g hgM
    rw [s15_Three_mem_nBar (D := D) (V₀ := V₀) (V := V) (L := K) hV]
    refine ⟨hgM, hMs hgM, ?_⟩
    have hμ : actTil V₀ V hV ⟨g, hMs hgM⟩ ∈ Mbar D.M V₀ V hV :=
      actTil_mem_barSub V₀ V hV hgM (hMs hgM)
    have hN : actTil V₀ V hV ⟨g, hMs hgM⟩ ∈
        normalizer ((lBar V₀ V hV L : Subgroup (MulAut (Vtil V₀ V hV))) :
          Set (MulAut (Vtil V₀ V hV))) :=
      mBar_le_normalizer_lBar D hS hc hμ
    rw [show lBar V₀ V hV L = barSub V₀ V hV L from rfl] at hN
    rwa [← hbar] at hN
  have h151 : Hyp151 D V₀ V K :=
    { hyp125 := hS.setting.hyp151.hyp125
      le := hKM
      twoResidual_eq := CFSG.Quasithin.S151S4.twoResidual_eq_self_of_perfect hKperf
      fstar_eq := by rw [hbar]; exact hS.setting.hyp151.fstar_eq
      commute := fun g hgM hgNot => absurd (hMemNBar g hgM) hgNot }
  have hconc : Conc4_136 D V₀ V hV K := by
    simpa only [Conc4_136, lBar, hbar] using hS.conc
  have hbarL : lBar V₀ V hV K = lBar V₀ V hV L := hbar
  have hcK : Case167_1 D V₀ V hV K := by
    refine ⟨?_, ?_, hc.2.2.1, hc.2.2.2⟩
    · rw [hbarL]; exact hc.1
    · rw [hbarL]; exact hc.2.1
  have hS16 : Sect16 D V₀ V K hV :=
    { setting := ⟨hS.setting.hyp16, h151⟩
      ne_bot := by rw [hbar]; exact hS.ne_bot
      conc := hconc }
  exact ⟨hS16, hcK⟩

theorem exists_calC_cover (D : Data G) (hSimple : RSimple153) (h127 : R127 D) (h119 : F11.R119 D)
    (h1217 : R1217 D) (hSchur : RSchurOm6) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (hc : Case167_1 D V₀ V hV L) :
    ∃ K : Subgroup G, K ∈ calC D.M ∧ barSub V₀ V hV K = barSub V₀ V hV L ∧
      Sect16 D V₀ V K hV ∧ Case167_1 D V₀ V hV K ∧ IsU4 (Bar2 K) 1 := by
  obtain ⟨K, hKc, m, hm, hKbar, ⟨e⟩⟩ := s15_Three_cover_K hSimple h127 h119 h1217
    hS.setting.hyp151 hV (s15Shape_of_case167_1 D hS hc) (s15KNatPerf_of_case167_1 D hS hc)
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hS.setting.hyp151.hyp125.pairFacts.le_normalizer
      hS.setting.hyp151.hyp125.pairFacts.le_normalizer₀
  have hbar : barSub V₀ V hV K = barSub V₀ V hV L := by
    rw [hKbar]
    have hmstab : m ∈ stabTil V₀ V := hMs hm
    rw [s15_Infra_barSub_conjSubgroup V₀ V hV hmstab L]
    have hμ : actTil V₀ V hV ⟨m, hmstab⟩ ∈ Mbar D.M V₀ V hV :=
      actTil_mem_barSub V₀ V hV hm hmstab
    have hN : actTil V₀ V hV ⟨m, hmstab⟩ ∈
        normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV))) :=
      mBar_le_normalizer_lBar D hS hc hμ
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
      ((normalizer (barSub V₀ V hV L : Set (MulAut (Vtil V₀ V hV)))).inv_mem hN)
  have hKM : K ≤ D.M := hKc.1.le
  refine ⟨K, hKc, hbar, ?_⟩
  obtain ⟨hS', hc'⟩ := sect16_of_barSub_eq D hS hc hKM hKc.2.1 hbar
  exact ⟨hS', hc', isU4_bar2_of_covers hSchur hKc hc.1 e⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
