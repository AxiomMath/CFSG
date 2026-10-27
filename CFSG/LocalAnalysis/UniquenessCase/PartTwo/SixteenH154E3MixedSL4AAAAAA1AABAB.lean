module

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16Frat
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.Coordinator.InndiagProxy
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Eseven
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_sl4_elemAbelian_lift
    (D : Data G) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V))
    {Ebar : Subgroup (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))}
    (hEbarM : Ebar ≤ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (hEbarC : Ebar ≤ centSub (wTil ⊥ V h.hyp151.isElemAbelian L))
    (hEbarAb : IsElemAbelian 3 Ebar) (hEbarCard : 9 ≤ Nat.card ↥Ebar) :
    ∃ E : Subgroup G, E ≤ D.M ∧
      E ≤ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L)) ∧
      IsElemAbelian 3 E ∧ 9 ≤ Nat.card ↥E := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨E, hEM, hEp, hEbar⟩ :=
    close16_exists_lift_barSub hMs le_rfl hEbarM (p := 3) (by norm_num) hEbarAb.isPGroup
  have hdisj : E ⊓ F11.CTilde D.M ⊥ V = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (H := E)
      (K := F11.CTilde D.M ⊥ V) ?_).eq_bot
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 3)).1 hEp
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.prime_three.coprime_iff_not_dvd).2 h3C)
  have hEab : IsElemAbelian 3 E := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      refine Subtype.ext ?_
      have haE : (a : G) ∈ E := a.2
      have hbE : (b : G) ∈ E := b.2
      have hastab : (a : G) ∈ stabTil ⊥ V := hMs (hEM haE)
      have hbstab : (b : G) ∈ stabTil ⊥ V := hMs (hEM hbE)
      have hzE : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ E :=
        E.mul_mem (E.mul_mem (E.mul_mem haE hbE) (E.inv_mem haE)) (E.inv_mem hbE)
      have hzstab : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈ stabTil ⊥ V :=
        (stabTil ⊥ V).mul_mem
          ((stabTil ⊥ V).mul_mem
            ((stabTil ⊥ V).mul_mem hastab hbstab) ((stabTil ⊥ V).inv_mem hastab))
          ((stabTil ⊥ V).inv_mem hbstab)
      have hacta : actTil ⊥ V hV ⟨(a : G), hastab⟩ ∈ Ebar := by
        have h := actTil_mem_barSub ⊥ V hV haE hastab
        rwa [hEbar] at h
      have hactb : actTil ⊥ V hV ⟨(b : G), hbstab⟩ ∈ Ebar := by
        have h := actTil_mem_barSub ⊥ V hV hbE hbstab
        rwa [hEbar] at h
      have hzC : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈
          F11.CTilde D.M ⊥ V := by
        rw [mem_cTilde_iff hV h.hyp151.hyp125.pairFacts.le_normalizer]
        refine ⟨hEM hzE, hzstab, ?_⟩
        haveI : IsMulCommutative ↥Ebar := hEbarAb.1
        have hzeq : (⟨(a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹, hzstab⟩ :
              ↥(stabTil ⊥ V)) =
            (⟨(a : G), hastab⟩ : ↥(stabTil ⊥ V)) * ⟨(b : G), hbstab⟩ *
              (⟨(a : G), hastab⟩ : ↥(stabTil ⊥ V))⁻¹ *
              (⟨(b : G), hbstab⟩ : ↥(stabTil ⊥ V))⁻¹ :=
          Subtype.ext rfl
        have hcomm : (⟨actTil ⊥ V hV ⟨(a : G), hastab⟩, hacta⟩ : ↥Ebar) *
            ⟨actTil ⊥ V hV ⟨(b : G), hbstab⟩, hactb⟩ =
            ⟨actTil ⊥ V hV ⟨(b : G), hbstab⟩, hactb⟩ *
            ⟨actTil ⊥ V hV ⟨(a : G), hastab⟩, hacta⟩ :=
          mul_comm' _ _
        have hval : actTil ⊥ V hV ⟨(a : G), hastab⟩ * actTil ⊥ V hV ⟨(b : G), hbstab⟩ =
            actTil ⊥ V hV ⟨(b : G), hbstab⟩ * actTil ⊥ V hV ⟨(a : G), hastab⟩ :=
          congrArg Subtype.val hcomm
        rw [hzeq, map_mul, map_mul, map_mul, map_inv, map_inv, hval]
        group
      have hz : (a : G) * (b : G) * (a : G)⁻¹ * (b : G)⁻¹ ∈
          E ⊓ F11.CTilde D.M ⊥ V := ⟨hzE, hzC⟩
      rw [hdisj, Subgroup.mem_bot] at hz
      have hz' : (a : G) * (b : G) * ((b : G) * (a : G))⁻¹ = 1 := by
        convert hz using 1
        group
      exact mul_inv_eq_one.mp hz'
    · intro x hx
      have hxstab : x ∈ stabTil ⊥ V := hMs (hEM hx)
      have hact : actTil ⊥ V hV ⟨x, hxstab⟩ ∈ Ebar := by
        have h := actTil_mem_barSub ⊥ V hV hx hxstab
        rwa [hEbar] at h
      have h3 : (actTil ⊥ V hV ⟨x, hxstab⟩) ^ 3 = 1 := hEbarAb.2 _ hact
      have hx3E : x ^ 3 ∈ E := E.pow_mem hx 3
      have hx3C : x ^ 3 ∈ F11.CTilde D.M ⊥ V := by
        rw [mem_cTilde_iff hV h.hyp151.hyp125.pairFacts.le_normalizer]
        refine ⟨hEM hx3E, (stabTil ⊥ V).pow_mem hxstab 3, ?_⟩
        have hpow : (⟨x, hxstab⟩ : ↥(stabTil ⊥ V)) ^ 3 =
            ⟨x ^ 3, (stabTil ⊥ V).pow_mem hxstab 3⟩ := Subtype.ext rfl
        rw [← hpow, map_pow, h3]
      have hx3 : x ^ 3 ∈ E ⊓ F11.CTilde D.M ⊥ V := ⟨hx3E, hx3C⟩
      rw [hdisj, Subgroup.mem_bot] at hx3
      exact hx3
  refine ⟨E, hEM, ?_, hEab, ?_⟩
  · intro g hg
    rw [mem_preBarSub]
    refine ⟨hEM hg, hMs (hEM hg), ?_⟩
    have h1 : actTil ⊥ V hV ⟨g, hMs (hEM hg)⟩ ∈ Ebar := by
      have h := actTil_mem_barSub ⊥ V hV hg (hMs (hEM hg))
      rwa [hEbar] at h
    exact hEbarC h1
  · have hdvd : Nat.card ↥(barSub ⊥ V hV E) ∣ Nat.card ↥E := by
      have hh := s16c7_card_mul_card_preBarSub hV (hEM.trans hMs) (Q := ⊥) bot_le
      rw [Subgroup.card_bot, mul_one] at hh
      exact ⟨Nat.card ↥(preBarSub E ⊥ V hV ⊥),
        hh.trans (mul_comm (Nat.card ↥(preBarSub E ⊥ V hV ⊥))
          (Nat.card ↥(barSub ⊥ V hV E)))⟩
    calc 9 ≤ Nat.card ↥Ebar := hEbarCard
      _ = Nat.card ↥(barSub ⊥ V hV E) := by rw [hEbar]
      _ ≤ Nat.card ↥E := Nat.le_of_dvd (card_subgroup_pos E) hdvd

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
