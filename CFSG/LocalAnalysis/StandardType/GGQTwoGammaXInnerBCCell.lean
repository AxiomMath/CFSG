module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXInnerBCDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXInnerCell
public import CFSG.LocalAnalysis.StandardType.GGWAutModelNorm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma ggQ2xb_entry_of_reindex {n : ℕ} {ι : Type} (e : Fin n ≃ ι)
    {C : Matrix ι ι ℤ} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (h : C = Matrix.reindex e e C₀ ∨ C = (Matrix.reindex e e C₀).transpose) :
    (∀ i j, C (e i) (e j) = C₀ i j) ∨ (∀ i j, C (e i) (e j) = C₀ j i) := by
  rcases h with h | h
  · left
    intro i j
    rw [h]
    exact congrArg₂ C₀ (Equiv.symm_apply_apply e i) (Equiv.symm_apply_apply e j)
  · right
    intro i j
    rw [h]
    exact congrArg₂ C₀ (Equiv.symm_apply_apply e j) (Equiv.symm_apply_apply e i)

private lemma ggQ2xb_det_of_reindex {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Fin n ≃ ι) {C : Matrix ι ι ℤ} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (h : C = Matrix.reindex e e C₀ ∨ C = (Matrix.reindex e e C₀).transpose) :
    C.det = C₀.det := by
  rcases h with h | h
  · rw [h, Matrix.det_reindex_self e C₀]
  · rw [h, Matrix.det_transpose, Matrix.det_reindex_self e C₀]

private theorem ggQ2xb_cell_of_inputs (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j) (hW : GGQ2WeylInner n C₀)
    (hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0) (hcard : 3 ≤ Fintype.card M.Λ) :
    GGQ2GammaX 3 B Bs x L D J := by
  refine ggQ2xd_gammaX_of_datumPM hLB hP hS rfl hCav M ?_
  intro u₀ hu₀ hfix hdim h4 hTF T hTnorm
  exact GGQ2WDatum.pmW_of_det M.toWDatum u₀ hfix hcard hdet C₀ e hC hW T hTnorm

private theorem ggQ2xb_cell_of_BC (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {r : ℕ} (hr : 4 ≤ r)
    (hW : ∃ e : Fin r ≃ M.Λ, M.coxeter = (CoxeterMatrix.B r).reindex e) :
    GGQ2GammaX 3 B Bs x L D J := by
  obtain ⟨e, he⟩ := hW
  have hC : GGIntCartan ((CoxeterMatrix.B r).reindex e) M.cartan := by
    rw [← he]; exact M.isCartan
  have hC0 : GGIntCartan ((CoxeterMatrix.B r).reindex e)
      (Matrix.reindex e e (CartanMatrix.B r)) := (ggIntCartan_B r).reindex e
  have hone : GGAtMostOneMultipleEdge ((CoxeterMatrix.B r).reindex e) :=
    (ggAtMostOneMultipleEdge_B r).reindex e
  have heq := hC.eq_or_eq_transpose hC0 hone
  have hcard : 3 ≤ Fintype.card M.Λ := by
    rw [← Fintype.card_congr e, Fintype.card_fin]
    omega
  rcases ggQ2xb_entry_of_reindex e heq with hentry | hentry
  · have hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
      rw [ggQ2xb_det_of_reindex e heq, CartanMatrix.B_det (show 0 < r by omega)]
      intro hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      norm_num at hz
    exact ggQ2xb_cell_of_inputs hLB hP hS hCav M (CartanMatrix.B r) e hentry
      (ggQ2WeylInner_B (by omega)) hdet hcard
  · have hentryC : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.C r i j := by
      intro i j
      rw [hentry i j]
      exact congrFun (congrFun (CartanMatrix.B_transpose r) i) j
    have hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
      rw [ggQ2xb_det_of_reindex e heq, CartanMatrix.B_det (show 0 < r by omega)]
      intro hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      norm_num at hz
    exact ggQ2xb_cell_of_inputs hLB hP hS hCav M (CartanMatrix.C r) e hentryC
      (ggQ2WeylInner_C (by omega)) hdet hcard

theorem ggQ2_gammaX_of_innerBCLabel (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel} (hLW : GGQ2LabelWeyl lab M.coxeter)
    (hinn : GGQ2InnerLabelBC lab) : GGQ2GammaX 3 B Bs x L D J := by
  classical
  rcases hinn with ⟨htag, h4⟩ | ⟨htag, hodd, h5⟩
  · rcases htag with htag | htag
    · exact ggQ2xb_cell_of_BC hLB hP hS hCav M h4
        (by simpa only [GGQ2LabelWeyl, htag] using hLW)
    · exact ggQ2xb_cell_of_BC hLB hP hS hCav M h4
        (by simpa only [GGQ2LabelWeyl, htag] using hLW)
  · have hLW' : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (ggCoxeterMatrixD lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hC : GGIntCartan ((ggCoxeterMatrixD lab.rank).reindex e) M.cartan := by
      rw [← he]; exact M.isCartan
    have hC0 : GGIntCartan ((ggCoxeterMatrixD lab.rank).reindex e)
        (Matrix.reindex e e (CartanMatrix.D lab.rank)) := (ggIntCartan_D lab.rank).reindex e
    have hone : GGAtMostOneMultipleEdge ((ggCoxeterMatrixD lab.rank).reindex e) :=
      (ggAtMostOneMultipleEdge_D lab.rank).reindex e
    have heq := hC.eq_or_eq_transpose hC0 hone
    have hcard : 3 ≤ Fintype.card M.Λ := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
      omega
    have hentry : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.D lab.rank i j := by
      rcases ggQ2xb_entry_of_reindex e heq with h | h
      · exact h
      · intro i j
        rw [h i j]
        exact congrFun (congrFun (CartanMatrix.D_transpose lab.rank) i) j
    have hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
      rw [ggQ2xb_det_of_reindex e heq, CartanMatrix.D_det (show 2 ≤ lab.rank by omega)]
      intro hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      norm_num at hz
    exact ggQ2xb_cell_of_inputs hLB hP hS hCav M (CartanMatrix.D lab.rank) e hentry
      (ggQ2WeylInner_D_odd (by omega) hodd) hdet hcard

end CFSG.StandardType

end
