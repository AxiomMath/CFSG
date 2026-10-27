module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Input
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Lift
import CFSG.Quasithin.Background.E3MParamAttained
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

namespace MinChoiceSupport

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

@[expose] def Conc4_136Min (D : Data G) (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (L : Subgroup G) : Prop :=
  ∃ t ∈ Mbar D.M V₀ V hV,
    t ^ 2 = 1 ∧ t ≠ 1 ∧
    rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 ∧
    rk ↥(commSub ⊤ (Subgroup.zpowers t)) = mBar D.M V₀ V hV ∧
    Conc4_136W (Mbar D.M V₀ V hV) t (lBar V₀ V hV L)

@[expose] def R4_136Min (D : Data G) : Prop :=
  ∀ (V₀ V : Subgroup G) (h : Hyp16 D V₀ V),
    ∃ L : Subgroup G, Setting16 D V₀ V L ∧
      barSub V₀ V h.hyp125.isElemAbelian L ≠ ⊥ ∧
      Conc4_136Min D V₀ V h.hyp125.isElemAbelian L

theorem Conc4_136Min.toConc4_136 {D : Data G} {V₀ V : Subgroup G}
    {hV : IsElemAbelian 2 V} {L : Subgroup G}
    (h : Conc4_136Min D V₀ V hV L) : Conc4_136 D V₀ V hV L := by
  obtain ⟨t, ht, ht2, ht1, hrk, -, hC⟩ := h
  exact ⟨t, ht, ht2, ht1, hrk, hC⟩

theorem r4_136Min_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h127 : R127 D) (h1214 : F12.R1214 D) (h136 : W4Lem13_6) : R4_136Min D := by
  intro V₀ V h
  have hV := h.hyp125.isElemAbelian
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  have hev : Even (Nat.card ↥(Mbar D.M V₀ V hV)) :=
    even_card_mbar_of_hyp16 D hx h61 h127 h
  obtain ⟨t, ht, hto, htval⟩ :=
    E3.exists_involution_rkIdx_fixV_eq_mParam (Mbar D.M V₀ V hV) hev
  have hEq : rk ↥(commSub ⊤ (Subgroup.zpowers t)) = mBar D.M V₀ V hV := by
    unfold mBar
    calc rk ↥(commSub ⊤ (Subgroup.zpowers t))
        = rk ↥(commV (Subgroup.zpowers t)) := by rw [commV_eq_commSub]
      _ = rkIdx (fixV (Subgroup.zpowers t)) := by rw [rkIdx_fixV_zpowers]
      _ = E3.mParam (Mbar D.M V₀ V hV) := htval
  have hmBar_le : mBar D.M V₀ V hV ≤ 3 := by
    have h1 : ¬ (3 < mBar D.M V₀ V hV) := fun hlt =>
      h.not_gt ((Hyp125.mBarGT_iff_lt_mBar h.hyp125 3).2 hlt)
    omega
  have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 := by
    rw [hEq]
    exact hmBar_le
  have ht2 : t ^ 2 = 1 := by
    rw [← hto]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hto
    exact absurd hto (by decide)
  have hM1 : Mbar D.M V₀ V hV ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at ht
    exact ht1 ht
  obtain ⟨Lbar, hC⟩ := h136 (Vtil V₀ V hV)
    (s15_Infra_vtil_sq_eq_one V₀ V hV)
    (Mbar D.M V₀ V hV)
    (isKGroup_mbar D hV hMs)
    (fun _ hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h.hyp125 hP hN h2)
    (TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h.hyp125 hM1) t ht hto hrk
  have hle := hC.le
  have h2 := hC.twoResidual_eq
  have hbar := barSub_liftO2 hV hMs hle h2
  refine ⟨liftO2 D.M V₀ V hV Lbar,
    ⟨h, hyp151_liftO2 D h.hyp125 hle h2 hC.fstar_eq hC.2.1⟩, ?_, ?_⟩
  · rw [hbar]
    exact hC.ne_bot
  · refine ⟨t, ht, ht2, ht1, hrk, hEq, ?_⟩
    rw [lBar, hbar]
    exact hC

end MinChoiceSupport

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
