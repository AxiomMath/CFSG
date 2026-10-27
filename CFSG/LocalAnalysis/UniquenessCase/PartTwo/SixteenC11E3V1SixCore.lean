module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3V1SixGap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11V1HardSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1TwoCommonFam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCATwoRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3Ctx

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G] [Finite G]

section Certified


theorem s1611e3_v1_case1_aSet_empty_core (hGap : S1611e3V1SixGap) {D : Data G}
    (h : S1611e3Std D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} (hc : Counterex16 D ⊥ V L hV) (hs : s15 D.M ⊥ V hV L = 1)
    (h1 : Case168_1 D ⊥ V hV L) (hV1 : v1Sub D.M ⊥ V hV L ≠ ⊥) :
    ∀ E ∈ calABar 2 D.M ⊥ V hV, False := by
  classical
  have h125 : Hyp125 D ⊥ V := hc.setting.hyp16.hyp125
  have hsumI := h1.2.2.1
  have hsum : SumOfNat (fun H U Z => AlternatingNatural H U Z 6) (lStar D.M ⊥ V hV L)
      (⊤ : Subgroup (vStar D.M ⊥ V hV L)) ⊥ 2 := by
    obtain ⟨I₁, I₂, -, -, hi₁, -, hU, hN₁, hN₂, -⟩ := hsumI
    refine s16c13bcA_sumOfNat_of_two hN₁ hN₂ ?_ ?_
    · rw [bot_sup_eq] at hi₁
      exact le_bot_iff.1 hi₁
    · rw [bot_sup_eq] at hU
      exact hU
  have htop : wStar D.M ⊥ V hV L = ⊤ :=
    s15_Three_wStar_eq_top D h.h1217 hc.setting.hyp151 hV hc.ne_bot hs
  have hsum' : SumOfNat (fun H U Z => AlternatingNatural H U Z 6) (lStar D.M ⊥ V hV L)
      (wStar D.M ⊥ V hV L) ⊥ 2 := by
    rw [htop]
    exact hsum
  have hF : s16e_two_Fam D ⊥ V L hV (fun H U Z => AlternatingNatural H U Z 6) :=
    s16e_two_fam_alt D hV (by omega) h1.2.1 hsum'
  obtain ⟨κ, e, I₀, I₁, hκsurj, hesurj, hκequiv, hκker, hcomm, hfix, hv1, -, -, -, -, -, -⟩ :=
    s16c11_v1_setup_data D (h.in10 h125) h.h1217 hc hs hF
  intro E hE
  exact hGap (Vtil ⊥ V hV) (vStar D.M ⊥ V hV L) (s15_Infra_vtil_sq_eq_one ⊥ V hV)
    (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) (lStar D.M ⊥ V hV L) κ e
    (s16e_two_lBar_le D hc.setting.hyp151 hV) h1.1 h1.2.1 hsumI hκsurj hesurj hκequiv hκker
    hcomm hfix (fun hker => hV1 (hv1 hker)) E hE

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
