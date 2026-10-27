module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClTrans
public import CFSG.LocalAnalysis.WeakClosure81.SixTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56ClDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.WeakClosure81

variable {G : Type} [Group G]

theorem c33Orth_conj {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G) (h : C33Orth V hV) :
    C33Orth (conjSubgroup V g) (E3.isElemAbelian_conjSubgroup hV g) := by
  obtain ⟨S, hSK, hSN⟩ := h
  refine ⟨S.ofEquiv (intModConj V hV g).symm, hSK, ?_⟩
  rw [S.omega_ofEquiv, MulEquiv.symm_symm]
  have h1 : autI (E3.isElemAbelian_conjSubgroup hV g) (⊤ : Subgroup G) =
      (autI hV ⊤).map (MulAut.congr (intModConj V hV g)).toMonoidHom := by
    rw [← autI_conjSubgroup hV ⊤ g, E3.conjSubgroup_top]
  rw [h1]
  exact (map_le_normalizer_map_iff (MulAut.congr (intModConj V hV g)) _ _).2 hSN

theorem autI_conjSubgroup_inv {V : Subgroup G} (hV : IsElemAbelian 2 V) (A : Subgroup G) (g : G) :
    autI (E3.isElemAbelian_conjSubgroup hV g) A =
      (autI hV (conjSubgroup A g⁻¹)).map (MulAut.congr (intModConj V hV g)).toMonoidHom := by
  rw [← autI_conjSubgroup hV (conjSubgroup A g⁻¹) g, E3.conjSubgroup_inv_conj]

theorem C33Setting.conj [Finite G] {M V : Subgroup G} (hS : C33Setting M V) (g : G) :
    C33Setting (conjSubgroup M g) (conjSubgroup V g) where
  elemAbelian := E3.isElemAbelian_conjSubgroup hS.elemAbelian g
  normalizer_eq := by rw [← E3.conjSubgroup_normalizer, hS.normalizer_eq]
  orth := c33Orth_conj hS.elemAbelian g hS.orth
  gamma_le := by
    intro i hi A hA
    rw [E3.gammaSet_conjV] at hA
    have h1 := E3.conj_mem_gammaSet g⁻¹ hA
    rw [conjSubgroup_conjSubgroup_inv] at h1
    have h2 := hS.gamma_le i hi _ h1
    rw [← E3.conjSubgroup_centralizer, E3.le_conjSubgroup_iff_inv_le]
    exact h2
  aSet_two := by
    intro A hA hnc
    rw [E3.gammaSet_conjV] at hA
    have h1 := E3.conj_mem_gammaSet g⁻¹ hA
    rw [conjSubgroup_conjSubgroup_inv] at h1
    have hnc' : ¬ conjSubgroup A g⁻¹ ≤ Subgroup.centralizer (V : Set G) := by
      intro h
      apply hnc
      rw [← E3.conjSubgroup_centralizer, E3.le_conjSubgroup_iff_inv_le]
      exact h
    have h2 := hS.aSet_two _ h1 hnc'
    have h3 := (aSet_map_congr_equiv_iff (intModConj V hS.elemAbelian g) 2 _ _).2 h2
    have e2 : autI (E3.isElemAbelian_conjSubgroup hS.elemAbelian g) (⊤ : Subgroup G) =
        (autI hS.elemAbelian ⊤).map (MulAut.congr (intModConj V hS.elemAbelian g)).toMonoidHom := by
      rw [← autI_conjSubgroup hS.elemAbelian ⊤ g, E3.conjSubgroup_top]
    rw [autI_conjSubgroup_inv hS.elemAbelian A g, e2]
    exact h3
  lt_rMV := by rw [rMV_conj hS.normalizer_eq g]; exact hS.lt_rMV

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
