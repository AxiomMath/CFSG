module

public import CFSG.Quasithin.Background.HStandard
public import CFSG.RankThree.OrthogonalInvolutions.Witt
public import CFSG.LieType.Universal.Spin.Forms
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H
open CFSG.LieType.Universal.Spin (quadMinus coe_quadMinus)
open CFSG.LieType.Universal.Spin (nondegenerate_polarBilin_quadMinus_of_finite)
open CFSG.ClassicalGroups.Orthogonal (toLinEquiv toLinEquiv_apply)

private abbrev s16h_wittIota : Type := Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2

theorem s16h_H5O4a_witt {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {v w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K}
    (hv : v ≠ 0) (hw : w ≠ 0) (hQ : StatedQuadMinus 2 K b c w = StatedQuadMinus 2 K b c v) :
    ∃ h ∈ natImage (CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c)),
      toAddMap h v = w := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hQn : (QuadraticMap.polarBilin (quadMinus 2 K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  obtain ⟨g, hg, hgv⟩ :=
    CFSG.RankThree.OrthogonalInvolutions.exists_mem_orthogonalGroup_apply_eq hQn (k := 1)
      (fun _ : Fin 1 => v) (fun _ : Fin 1 => w)
      ((linearIndependent_unique_iff (v := fun _ : Fin 1 => v)).mpr (by simpa using hv))
      ((linearIndependent_unique_iff (v := fun _ : Fin 1 => w)).mpr (by simpa using hw))
      (fun _ => by
        show quadMinus 2 K b c w = quadMinus 2 K b c v
        rw [congrFun (coe_quadMinus 2 K b c) w, congrFun (coe_quadMinus 2 K b c) v]
        exact hQ)
      (fun _ _ => by
        rw [CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul (Q := quadMinus 2 K b c) w,
          CFSG.ClassicalGroups.Orthogonal.polar_self_eq_two_mul (Q := quadMinus 2 K b c) v,
          h2]
        ring)
  let G : GL s16h_wittIota K := (toLinEquiv s16h_wittIota K).symm g
  have hGg : toLinEquiv s16h_wittIota K G = g :=
    MulEquiv.apply_symm_apply (toLinEquiv s16h_wittIota K) g
  have hGmem : G ∈ CFSG.MatrixModel.isometryCore (StatedQuadMinus 2 K b c) := by
    refine Subgroup.subset_closure ?_
    intro x
    have hgx := (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg) x
    have hgx' : g x = Matrix.mulVec (G : Matrix s16h_wittIota s16h_wittIota K) x := by
      rw [← hGg, toLinEquiv_apply]
    rw [← congrFun (coe_quadMinus 2 K b c)
          (Matrix.mulVec (G : Matrix s16h_wittIota s16h_wittIota K) x),
        ← congrFun (coe_quadMinus 2 K b c) x, ← hgx']
    exact hgx
  refine ⟨matHom G, ⟨⟨G, hGmem⟩, rfl⟩, ?_⟩
  rw [matHom_apply, toAddMap_matAut]
  rw [← toLinEquiv_apply, hGg]
  simpa using hgv 0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
