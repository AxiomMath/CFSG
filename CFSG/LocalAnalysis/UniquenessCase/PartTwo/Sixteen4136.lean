module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Input
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Mbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen4136Lift
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSeventeen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem r4_136_holds (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h136 : W4Lem13_6) : R4_136 D := by
  intro V₀ V h
  have hpf := h.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil hpf.le_normalizer hpf.le_normalizer₀
  obtain ⟨t, ht, ht2, hrk⟩ := exists_involution_of_hyp16 D hx h61 h127 h
  have hM1 : Mbar D.M V₀ V h.hyp125.isElemAbelian ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.mem_bot] at ht
    rw [ht, orderOf_one] at ht2
    exact absurd ht2 (by decide)
  obtain ⟨Lbar, hC⟩ := h136 (Vtil V₀ V h.hyp125.isElemAbelian)
    (s15_Infra_vtil_sq_eq_one V₀ V h.hyp125.isElemAbelian)
    (Mbar D.M V₀ V h.hyp125.isElemAbelian)
    (isKGroup_mbar D h.hyp125.isElemAbelian hMs)
    (fun _ hP hN h2 => s15_Kbar_eq_bot_of_normal_isPGroup D h.hyp125 hP hN h2)
    (TwelveSeventeen.isBasicModule D hx h61 h127 h1214 h.hyp125 hM1) t ht ht2 hrk
  have hle := hC.le
  have h2 := hC.twoResidual_eq
  have hbar := barSub_liftO2 h.hyp125.isElemAbelian hMs hle h2
  refine ⟨liftO2 D.M V₀ V h.hyp125.isElemAbelian Lbar,
    ⟨h, hyp151_liftO2 D h.hyp125 hle h2 hC.fstar_eq hC.2.1⟩, ?_, ?_⟩
  · rw [hbar]
    exact hC.ne_bot
  · refine ⟨t, ht, ?_, ?_, hrk, ?_⟩
    · rw [← ht2]
      exact pow_orderOf_eq_one t
    · intro h1
      rw [h1, orderOf_one] at ht2
      exact absurd ht2 (by decide)
    · rw [lBar, hbar]
      exact hC

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
