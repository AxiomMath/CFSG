module

public import CFSG.LocalAnalysis.StandardType.GGQ2EichlerDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggE7R_det_eq : (CartanMatrix.E 7).det = 2 := by
  have h7 := CartanMatrix.E_det (n := 7) (by norm_num)
  norm_num at h7
  exact h7

private lemma ggE7R_det_cast_ne_zero :
    (((CartanMatrix.E 7).det : ℤ) : ZMod 3) ≠ 0 := by
  rw [ggE7R_det_eq]
  decide

private lemma ggE7R_root_eq_zero
    {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin 7 → U) (α : Fin 7 → Module.Dual (ZMod 3) U)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hα : ∀ i j, α i (h j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3))
    {w : U} (hw : ∀ i, α i w = 0) : w = 0 := by
  by_contra hw0
  have hwspan : w ∈ Submodule.span (ZMod 3) (Set.range h) := by
    rw [hspan]
    exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hwspan
  have hMdet :
      (Matrix.map (CartanMatrix.E 7) (Int.castRingHom (ZMod 3))).det ≠ 0 := by
    have hmap := RingHom.map_det (Int.castRingHom (ZMod 3)) (CartanMatrix.E 7)
    have h1 :
        (Matrix.map (CartanMatrix.E 7) (Int.castRingHom (ZMod 3))).det =
          (((CartanMatrix.E 7).det : ℤ) : ZMod 3) := hmap.symm
    rw [h1]
    exact ggE7R_det_cast_ne_zero
  have hc0 : c = 0 := by
    apply Matrix.eq_zero_of_mulVec_eq_zero
      (M := Matrix.map (CartanMatrix.E 7) (Int.castRingHom (ZMod 3))) hMdet
    funext i
    have hsum : (∑ j, c j * ((CartanMatrix.E 7 i j : ℤ) : ZMod 3)) = 0 := by
      have hcomp : α i w = ∑ j, c j * ((CartanMatrix.E 7 i j : ℤ) : ZMod 3) := by
        rw [← hc, map_sum]
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [map_smul, hα]
        rfl
      rw [← hcomp, hw i]
    show (∑ j, Matrix.map (CartanMatrix.E 7) (Int.castRingHom (ZMod 3)) i j * c j) = 0
    rw [← hsum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Matrix.map_apply]
    exact mul_comm _ _
  have hwzero : w = 0 := by
    rw [← hc]
    simp [hc0]
  exact hw0 hwzero

theorem ggWeylNoEichlerRho_E7 (hE7 : GGWeylE7NoEichler) :
    GGWeylNoEichlerRho (CartanMatrix.E 7) := by
  unfold GGWeylNoEichlerRho
  intro U _ _ h α hind hspan hα g hg hgne
  have hnot : ¬ GGEichler g := hE7 U h α hind hspan hα g hg
  unfold GGEichler at hnot
  have hne : ∃ v, g (g v) + g v + v ≠ 0 := by
    by_contra hcon
    apply hnot
    refine ⟨hgne, fun v => ?_⟩
    by_contra hv
    exact hcon ⟨v, hv⟩
  obtain ⟨v, hv⟩ := hne
  refine ⟨v, ?_⟩
  by_contra hcon
  exact hv (ggE7R_root_eq_zero h α hspan hα (fun i => by
    by_contra hci
    exact hcon ⟨i, hci⟩))

end CFSG.StandardType

end
