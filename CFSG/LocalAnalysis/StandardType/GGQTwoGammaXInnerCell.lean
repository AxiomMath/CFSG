module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXInnerDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGammaXDetCell
public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrDatumInner
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylA
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE7
public import CFSG.LocalAnalysis.StandardType.GGQTwoLemma112WeylE8

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2xi_entry_of_reindex {n : ℕ} {ι : Type} (e : Fin n ≃ ι)
    {C : Matrix ι ι ℤ} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (h : C = Matrix.reindex e e C₀ ∨ C = (Matrix.reindex e e C₀).transpose)
    (hsymm : ∀ i j, C₀ i j = C₀ j i) :
    ∀ i j, C (e i) (e j) = C₀ i j := by
  rintro i j
  rcases h with h | h
  · rw [h]
    exact congrArg₂ C₀ (Equiv.symm_apply_apply e i) (Equiv.symm_apply_apply e j)
  · rw [h]
    exact (congrArg₂ C₀ (Equiv.symm_apply_apply e j) (Equiv.symm_apply_apply e i)).trans
      (hsymm j i)

private lemma ggQ2xi_det_of_reindex {n : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (e : Fin n ≃ ι) {C : Matrix ι ι ℤ} {C₀ : Matrix (Fin n) (Fin n) ℤ}
    (h : C = Matrix.reindex e e C₀ ∨ C = (Matrix.reindex e e C₀).transpose) :
    C.det = C₀.det := by
  rcases h with h | h
  · rw [h, Matrix.det_reindex_self e C₀]
  · rw [h, Matrix.det_transpose, Matrix.det_reindex_self e C₀]

private theorem ggQ2xi_cell_of_inputs (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {n : ℕ} (C₀ : Matrix (Fin n) (Fin n) ℤ) (e : Fin n ≃ M.Λ)
    (hC : ∀ i j, M.cartan (e i) (e j) = C₀ i j) (hW : GGQ2WeylInner n C₀)
    (hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0) (hcard : 3 ≤ Fintype.card M.Λ) :
    GGQ2GammaX 3 B Bs x L D J := by
  refine ggQ2xd_gammaX_of_datumPM hLB hP hS rfl hCav M ?_
  intro u₀ hu₀ hfix hdim h4 hTF T hTnorm
  exact GGQ2WDatum.pmW_of_det M.toWDatum u₀ hfix hcard hdet C₀ e hC hW T hTnorm

theorem ggQ2_gammaX_of_innerLabel (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput)
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hCav : 4 ∣ Nat.card (ggAutomizer J Bs))
    (M : GGQ2LDatum 3 Bs L x) {lab : LargeEvenLabel} (hLW : GGQ2LabelWeyl lab M.coxeter)
    (hinn : GGQ2InnerLabel lab) : GGQ2GammaX 3 B Bs x L D J := by
  classical
  rcases hinn with ⟨htag, h4, hndvd⟩ | htag | htag
  · have hLW' : ∃ e : Fin lab.rank ≃ M.Λ,
        M.coxeter = (CoxeterMatrix.A lab.rank).reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hC : GGIntCartan ((CoxeterMatrix.A lab.rank).reindex e) M.cartan := by
      rw [← he]; exact M.isCartan
    have hC0 : GGIntCartan ((CoxeterMatrix.A lab.rank).reindex e)
        (Matrix.reindex e e (CartanMatrix.A lab.rank)) :=
      (ggIntCartan_A lab.rank).reindex e
    have hone : GGAtMostOneMultipleEdge ((CoxeterMatrix.A lab.rank).reindex e) :=
      (ggAtMostOneMultipleEdge_A lab.rank).reindex e
    have heq := hC.eq_or_eq_transpose hC0 hone
    have hsymm : ∀ i j, CartanMatrix.A lab.rank i j = CartanMatrix.A lab.rank j i :=
      fun i j => congrFun (congrFun (CartanMatrix.A_transpose lab.rank) j) i
    have hentry : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.A lab.rank i j :=
      ggQ2xi_entry_of_reindex e heq hsymm
    have hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
      rw [ggQ2xi_det_of_reindex e heq, CartanMatrix.A_det]
      intro hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      exact hndvd (by exact_mod_cast hz)
    have hcard : 3 ≤ Fintype.card M.Λ := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
      omega
    exact ggQ2xi_cell_of_inputs hLB hP hS hCav M (CartanMatrix.A lab.rank) e hentry
      (ggQ2WeylInner_A h4) hdet hcard
  · have hLW' : ∃ e : Fin 7 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₇.reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hC : GGIntCartan (CoxeterMatrix.E₇.reindex e) M.cartan := by
      rw [← he]; exact M.isCartan
    have hC0 : GGIntCartan (CoxeterMatrix.E₇.reindex e)
        (Matrix.reindex e e (CartanMatrix.E 7)) := ggIntCartan_E₇.reindex e
    have hone : GGAtMostOneMultipleEdge (CoxeterMatrix.E₇.reindex e) :=
      ggAtMostOneMultipleEdge_E₇.reindex e
    have heq := hC.eq_or_eq_transpose hC0 hone
    have hsymm : ∀ i j, CartanMatrix.E 7 i j = CartanMatrix.E 7 j i :=
      fun i j => congrFun (congrFun (CartanMatrix.E_transpose 7) j) i
    have hentry : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E 7 i j :=
      ggQ2xi_entry_of_reindex e heq hsymm
    have hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
      rw [ggQ2xi_det_of_reindex e heq, CartanMatrix.E₇_det]
      intro hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      norm_num at hz
    have hcard : 3 ≤ Fintype.card M.Λ := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
      norm_num
    exact ggQ2xi_cell_of_inputs hLB hP hS hCav M (CartanMatrix.E 7) e hentry
      ggQ2WeylInner_E7 hdet hcard
  · have hLW' : ∃ e : Fin 8 ≃ M.Λ, M.coxeter = CoxeterMatrix.E₈.reindex e := by
      simpa only [GGQ2LabelWeyl, htag] using hLW
    obtain ⟨e, he⟩ := hLW'
    have hC : GGIntCartan (CoxeterMatrix.E₈.reindex e) M.cartan := by
      rw [← he]; exact M.isCartan
    have hC0 : GGIntCartan (CoxeterMatrix.E₈.reindex e)
        (Matrix.reindex e e (CartanMatrix.E 8)) := ggIntCartan_E₈.reindex e
    have hone : GGAtMostOneMultipleEdge (CoxeterMatrix.E₈.reindex e) :=
      ggAtMostOneMultipleEdge_E₈.reindex e
    have heq := hC.eq_or_eq_transpose hC0 hone
    have hsymm : ∀ i j, CartanMatrix.E 8 i j = CartanMatrix.E 8 j i :=
      fun i j => congrFun (congrFun (CartanMatrix.E_transpose 8) j) i
    have hentry : ∀ i j, M.cartan (e i) (e j) = CartanMatrix.E 8 i j :=
      ggQ2xi_entry_of_reindex e heq hsymm
    have hdet : ((M.cartan.det : ℤ) : ZMod 3) ≠ 0 := by
      rw [ggQ2xi_det_of_reindex e heq, CartanMatrix.E₈_det]
      intro hz
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hz
      norm_num at hz
    have hcard : 3 ≤ Fintype.card M.Λ := by
      rw [← Fintype.card_congr e, Fintype.card_fin]
      norm_num
    exact ggQ2xi_cell_of_inputs hLB hP hS hCav M (CartanMatrix.E 8) e hentry
      ggQ2WeylInner_E8 hdet hcard

end CFSG.StandardType

end
