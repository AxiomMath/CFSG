module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Gen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Gap64
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC2363a
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC23Odd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenFiveTen
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qm
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalFamily
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinearStrong
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs12b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Model
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.Quasithin.Background.HFF
public import CFSG.Quasithin.Background.HPairBridge
public import CFSG.Quasithin.Background.HSL3Inner
public import CFSG.Sporadic.Schreier.J4SCommGenBase1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c23_false_of_v1_eq_bot (D : Data G) (hSg : UC6S846.SigmaStd D) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h129 : R129_1 D) (h1217 : R1217 D)
    (h119 : R119W D) (h145 : Thm145 D) {V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D ⊥ V L hV) (hc : Case167_2 D ⊥ V hV L)
    (hv1 : v1Sub D.M ⊥ V hV L = ⊥) : False := by
  have h151 := hS.setting.hyp151
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have h115 : F11.R115 D := uc22p22q_r115_of D hx h61
  obtain ⟨x, hxM, hxn⟩ := c23_exists_mem_not_nBar D h151 hV hc.2.2.1
  have hu := c23_unique₁ D hSg h61 h127 h1217 hS (Or.inl hc)
  refine h129 ⊥ V h151.hyp125 (s15_FiveTen_isTI_of_uniqueMax D hV hP.le_normalizer ?_)
  intro w hwV hw1
  by_cases h1 : w ∈ wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L
  · exact hu w h1 hw1
  by_cases h2 : x * w * x⁻¹ ∈ wSub ⊥ V hV L ⊔ v1Sub D.M ⊥ V hV L
  · refine c23_uniqueMax_of_conj D hxM (hu _ h2 ?_)
    intro h
    apply hw1
    calc w = x⁻¹ * (x * w * x⁻¹) * x := by group
      _ = 1 := by rw [h]; group
  refine c23_uniqueMax_generic D hx h115 h127 h1217 h119 h145 hS hc hv1 hxM hxn hwV ?_
  have hMs : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  rw [hv1, sup_bot_eq] at h1 h2
  unfold c23Omega
  simp only [Set.mem_setOf_eq]
  refine ⟨fun hmem => h1 ?_, fun hmem => h2 ?_⟩
  · exact (mem_preTil_iff_of_mem ⊥ V hV _ hwV).2 hmem
  · have h3 : w ∈ wSub ⊥ V hV (conjSubgroup L x) :=
      (mem_preTil_iff_of_mem ⊥ V hV _ hwV).2 hmem
    rw [s15_Infra_wSub_conjSubgroup ⊥ V L hV (hMs hxM),
      CFSG.Quasithin.mem_conjSubgroup_iff] at h3
    exact h3

theorem r16_64_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h127 : R127 D) (h129 : R129_1 D) (h1217 : R1217 D)
    (h119 : R119W D) (h145 : Thm145 D) (h63 : R16_63 D) (hgap : C23Gap64 D) : R16_64 D := by
  intro V₀ V L hV hS hsit hc
  by_cases hv1 : v1Sub D.M V₀ V hV L = ⊥
  · have h0 : V₀ = ⊥ := le_bot_iff.1 (hv1 ▸ s15_Infra_le_v1Sub D.M V₀ V hV L)
    subst h0
    exact c23_false_of_v1_eq_bot D hSg hx h61 h127 h129 h1217 h119 h145 hS hc hv1
  · exact hgap hSg hx h61 h127 h129 h1217 h119 h145 h63 V₀ V L hV hS hc hsit.2 hv1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
