module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClC
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClRStar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClGeo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

@[expose] def W3Lem612 (G : Type) [Group G] [Finite G] : Prop :=
  ∀ {n : ℕ} {M V : Subgroup G} {g : G}, Hyp612 n M V g →
    H3Cond n (conjSubgroup M g) (conjSubgroup V g) g⁻¹ → InCalOStar n M ⊥ V g

theorem r16_33_close_holds (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (h21 : R1621 D) (h22 : R1622 D) (h61 : UC6.R6_1 D) (hext : DataExt D) (h5 : R16_5 D)
    (hw : W3Lem612 G) : R16_33_close D := by
  classical
  intro V₀ V L hV hS m hm hm2 hV0 hnc
  subst hm2
  subst hV0
  have hexA : ∃ A ∈ E3.gammaSet V 2 D.T, ¬ A ≤ centralizer (V : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hnc
    refine centralizer_cClos_le_of_commutator_eq_bot D hS.setting.hyp16.hyp125 ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.2 (E3.wClos_le_of_forall hcon)
  obtain ⟨A, hAT, hAc⟩ := hexA
  obtain ⟨hAT', g, hAg, hAm⟩ := hAT
  have hAM : A ≤ D.M := hAT'.trans D.sylowM.le
  have hAB : A ≤ BOf D.M V g := le_inf hAg hAM
  have hh : C33Hyp D.M V g :=
    ⟨by have := E3.mQuot_mono (V := conjSubgroup V g) hAB; omega,
      fun h => hAc (hAB.trans h)⟩
  have hSet : C33Setting D.M V := c33_setting_of_case1633 D hSg h1219 h21 h22 h61 hext h5 hS hm
  have hr : (2 : ℕ∞) < rStarMV D.M V := c33_lt_rStarMV D h61 hext h5 h22 hS hm
  exact ⟨conjSubgroup V g, g, rfl,
    hw (c33_hyp612 geoDichotomy_holds hSet hh hr) (c33_h3 (hSet.conj g) g⁻¹)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
