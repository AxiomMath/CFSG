module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.BBarSporadicTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.MBarSporadicTable
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SporadicNotClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenTwentyThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeParabolicsHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section OrderCertificates


theorem b17_23Bound_holds (D : Data G) (V₀ V : Subgroup G)
    (hV : Hyp125 D V₀ V) (hx : DataExt D) (h61 : UC6.R6_1 D) (h127 : R127 D)
    (h1214 : F12.R1214 D) (h4128 : W4Lem12_8) (h416 : Inputs1719.W4Lem4_16)
    (hrow : Inputs1719.W4Thm11_1RowM .He) : B17_23Bound D V₀ V hV := by
  intro L c hN hHe _ hL1 _ hdich H₁ H₂ H₃ hT₁ hT₂ hT₃ hH₁ hH₂ hH₃ hF₁ hF₂ hF₃ hgen
  have hL := c.mem_calC
  have hV' := hV.isElemAbelian
  have hsimple : IsSimpleGroup (Bar2 L) := by
    obtain ⟨e⟩ := hHe
    exact e.isSimpleGroup_congr.mpr CFSG.Sporadic.He.isSimpleGroup_He
  have hZ : Subgroup.center (Bar2 L) = ⊥ := uc22p21k_center_eq_bot hL.2.2
  have hs : IsSpor (BarInf L) .He :=
    isSpor_barInf_of_isSpor_bar2 hL CFSG.Sporadic.He.isSimpleGroup_He hHe
  have hfix := fixV_barSub_eq_bot_of_dichotomy hV hL hN hdich
    (not_classicalEvenAltG2Der_of_isSpor_He hHe)
  refine ⟨?_, ?_⟩
  · have hLstab : L ≤ stabTil V₀ V :=
      hL.1.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
    have hTstab : D.T ≤ stabTil V₀ V :=
      D.sylowM.le.trans (le_stabTil hV.pairFacts.le_normalizer hV.pairFacts.le_normalizer₀)
    have hLT : L ⊔ D.T ≤ stabTil V₀ V := sup_le hLstab hTstab
    have hsupbar : barSub V₀ V hV' (L ⊔ D.T) = barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T :=
      s16c7_barSub_sup V₀ V hV' hLstab hTstab
    let Δ : Set (Subgroup (MulAut (Vtil V₀ V hV'))) :=
      {barSub V₀ V hV' H₁, barSub V₀ V hV' H₂, barSub V₀ V hV' H₃}
    have hmemΔ : ∀ {H : Subgroup G}, H ≤ L ⊔ D.T → D.T ≤ H →
        barSub V₀ V hV' H ≤ barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T ∧
          barSub V₀ V hV' D.T ≤ barSub V₀ V hV' H := fun hHle hTle =>
      ⟨hsupbar ▸ barSub_mono V₀ V hV' hHle, barSub_mono V₀ V hV' hTle⟩
    have hΔ : ∀ H ∈ Δ, H ≤ barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T ∧
        barSub V₀ V hV' D.T ≤ H := by
      rintro H (rfl | rfl | rfl)
      · exact hmemΔ hH₁ hT₁
      · exact hmemΔ hH₂ hT₂
      · exact hmemΔ hH₃ hT₃
    have hgenΔ : (⨆ H ∈ Δ, H) = barSub V₀ V hV' L ⊔ barSub V₀ V hV' D.T := by
      have h12 : barSub V₀ V hV' (H₁ ⊔ H₂) = barSub V₀ V hV' H₁ ⊔ barSub V₀ V hV' H₂ :=
        s16c7_barSub_sup V₀ V hV' (hH₁.trans hLT) (hH₂.trans hLT)
      have h123 : barSub V₀ V hV' (H₁ ⊔ H₂ ⊔ H₃) =
          barSub V₀ V hV' (H₁ ⊔ H₂) ⊔ barSub V₀ V hV' H₃ :=
        s16c7_barSub_sup V₀ V hV' (sup_le (hH₁.trans hLT) (hH₂.trans hLT)) (hH₃.trans hLT)
      rw [← hsupbar, ← hgen, h123, h12]
      simp only [Δ, iSup_insert, iSup_singleton, sup_assoc]
    have hfin : Δ.Finite := Set.toFinite Δ
    have hk : fIndexSum Δ ≤ ((3 : ℕ) : ℕ∞) := by
      have h1 := fIndexSum_le_ncard_of_inFSq_one hfin (Δ := Δ) (by
        rintro H (rfl | rfl | rfl)
        · exact inFSq_barSub_of_le_sup_T hV hL hZ hL1 hH₁ hF₁
        · exact inFSq_barSub_of_le_sup_T hV hL hZ hL1 hH₂ hF₂
        · exact inFSq_barSub_of_le_sup_T hV hL hZ hL1 hH₃ hF₃)
      have h2 : Δ.ncard ≤ 3 := by
        refine (Set.ncard_insert_le _ _).trans ?_
        have := Set.ncard_insert_le (barSub V₀ V hV' H₂) {barSub V₀ V hV' H₃}
        rw [Set.ncard_singleton] at this
        omega
      exact h1.trans (by exact_mod_cast h2)
    exact bBar_le_of_delta D hV (Inputs1719.w4Lem4_16b_of_w4Lem4_16 h416) hL hN hL1 hfix Δ 3
      hfin hΔ hgenΔ hk
  · have hm := tableM_le_mBar D hx h61 h127 h1214 h4128 hV hL hL1 hrow hs
      (not_lieModel_psl_two_of_isSpor_He hs)
    simpa only [Inputs1719.tableM] using hm


theorem seventeen_twentythree_holds
    (D : Data G) (V₀ V : Subgroup G) (hV : Hyp125 D V₀ V)
    (h17_20 : R17_20At D V₀ V) (h17_21 : R17_21At D V₀ V) (h17_22 : R17_22At D V₀ V)
    (h869 : F08.R869 D) (h127 : R127 D)
    (h640 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_40_2 D) (hFF : W4Thm12McClurg)
    (hx : DataExt D) (h61 : CFSG.LocalAnalysis.UniquenessCase.UC6.R6_1 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h126 : R126 D) (h111 : W3Thm111 G)
    (h1214 : F12.R1214 D) (h4128 : W4Lem12_8) (h416 : Inputs1719.W4Lem4_16)
    (hrow : Inputs1719.W4Thm11_1RowM .He)
    (hOut : Inputs1719.K_HeOuterParabolics) :
    R17_23At D V₀ V :=
  seventeen_twentythree D V₀ V hV h17_20 h17_21 h17_22 h869 h127 h640 hFF hx h61 h1114 h162
    hTor h1482 h126 h111
    (b17_23Bound_holds D V₀ V hV hx h61 h127 h1214 h4128 h416 hrow)
    (Inputs1719.k_HeParabolics_of_outer hOut)

end OrderCertificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
