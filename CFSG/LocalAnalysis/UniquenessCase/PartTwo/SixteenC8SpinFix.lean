module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.StandardType CFSG.StandardType.Triality CFSG.LieType.D4Small CFSG.LieType.SpinGeom
open scoped Matrix

private abbrev sixteenC8SpinFixAct (h : Om8 (ZMod 2)) :
    Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2) :=
  ((h : GL (Fin (2 * 4)) (ZMod 2)) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2))

private theorem sixteenC8SpinFix_xvec_eq_zero (v : Fin (2 * 4) → ZMod 2)
    (hv : ∀ h ∈ spinSeven (ZMod 2),
      sixteenC8SpinFixAct h *ᵥ frameE (ZMod 2) 0 = frameE (ZMod 2) 0 →
        sixteenC8SpinFixAct h *ᵥ v = v) :
    xvec (ZMod 2) v = 0 := by
  funext k
  obtain ⟨i, hik⟩ := exists_ne k
  obtain ⟨h, hmem, hact⟩ := exists_mem_spinSeven_spinElt (K := ZMod 2)
    (0 : Fin 3 → ZMod 2) (0 : Fin 3 → ZMod 2) (Matrix.transvection i k (1 : ZMod 2))
    (Matrix.det_transvection_of_ne i k hik (1 : ZMod 2))
  have hfix : sixteenC8SpinFixAct h *ᵥ frameE (ZMod 2) 0 = frameE (ZMod 2) 0 := by
    rw [hact (frameE (ZMod 2) 0), spinElt_frameE_zero]
  have hspin : spinElt (ZMod 2) 0 0 (Matrix.transvection i k (1 : ZMod 2)) v = v := by
    rw [← hact v]
    exact hv h hmem hfix
  have hx' : Matrix.transvection i k (1 : ZMod 2) *ᵥ xvec (ZMod 2) v =
      xvec (ZMod 2) v := by
    have h := xvec_spinElt (K := ZMod 2) (0 : Fin 3 → ZMod 2) (0 : Fin 3 → ZMod 2)
      (Matrix.transvection i k (1 : ZMod 2)) v
    rw [hspin] at h
    simpa using h.symm
  have hi := congrFun hx' i
  rw [transvection_mulVec_apply] at hi
  simpa using hi

private theorem sixteenC8SpinFix_yvec_eq_zero (v : Fin (2 * 4) → ZMod 2)
    (hv : ∀ h ∈ spinSeven (ZMod 2),
      sixteenC8SpinFixAct h *ᵥ frameE (ZMod 2) 0 = frameE (ZMod 2) 0 →
        sixteenC8SpinFixAct h *ᵥ v = v) :
    yvec (ZMod 2) v = 0 := by
  funext k
  obtain ⟨j, hjk⟩ := exists_ne k
  have hkj : k ≠ j := Ne.symm hjk
  obtain ⟨h, hmem, hact⟩ := exists_mem_spinSeven_spinElt (K := ZMod 2)
    (0 : Fin 3 → ZMod 2) (0 : Fin 3 → ZMod 2) (Matrix.transvection k j (1 : ZMod 2))
    (Matrix.det_transvection_of_ne k j hkj (1 : ZMod 2))
  have hfix : sixteenC8SpinFixAct h *ᵥ frameE (ZMod 2) 0 = frameE (ZMod 2) 0 := by
    rw [hact (frameE (ZMod 2) 0), spinElt_frameE_zero]
  have hspin : spinElt (ZMod 2) 0 0 (Matrix.transvection k j (1 : ZMod 2)) v = v := by
    rw [← hact v]
    exact hv h hmem hfix
  have hy' : ((Matrix.transvection k j (1 : ZMod 2)).adjugate)ᵀ *ᵥ yvec (ZMod 2) v =
      yvec (ZMod 2) v := by
    have h := yvec_spinElt (K := ZMod 2) (0 : Fin 3 → ZMod 2) (0 : Fin 3 → ZMod 2)
      (Matrix.transvection k j (1 : ZMod 2)) v
    rw [hspin] at h
    simpa [altMat_zero] using h.symm
  have hj := congrFun hy' j
  rw [adjugate_transvection k j hkj, transvection_transpose, transvection_mulVec_apply] at hj
  simpa using hj

private theorem sixteenC8SpinFix_coordY_eq_zero (v : Fin (2 * 4) → ZMod 2)
    (hv : ∀ h ∈ spinSeven (ZMod 2),
      sixteenC8SpinFixAct h *ᵥ frameE (ZMod 2) 0 = frameE (ZMod 2) 0 →
        sixteenC8SpinFixAct h *ᵥ v = v) :
    coordY (ZMod 2) v 0 = 0 := by
  have hx := sixteenC8SpinFix_xvec_eq_zero v hv
  obtain ⟨h, hmem, hact⟩ := exists_mem_spinSeven_spinElt (K := ZMod 2)
    (0 : Fin 3 → ZMod 2) (Pi.single 0 (1 : ZMod 2)) (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))
    Matrix.det_one
  have hfix : sixteenC8SpinFixAct h *ᵥ frameE (ZMod 2) 0 = frameE (ZMod 2) 0 := by
    rw [hact (frameE (ZMod 2) 0), spinElt_frameE_zero]
  have hspin : spinElt (ZMod 2) 0 (Pi.single 0 (1 : ZMod 2)) 1 v = v := by
    rw [← hact v]
    exact hv h hmem hfix
  have h := xvec_spinElt (K := ZMod 2) (0 : Fin 3 → ZMod 2) (Pi.single 0 (1 : ZMod 2))
    (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) v
  rw [hspin] at h
  rw [hx] at h
  have h0 := congrFun h 0
  simpa using h0.symm

theorem fixed_of_stab_frameE (v : Fin (2 * 4) → ZMod 2)
    (hv : ∀ h ∈ spinSeven (ZMod 2),
      ((h : GL (Fin (2 * 4)) (ZMod 2)) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ
          frameE (ZMod 2) 0 = frameE (ZMod 2) 0 →
        ((h : GL (Fin (2 * 4)) (ZMod 2)) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) (ZMod 2)) *ᵥ v = v) :
    v = 0 ∨ v = frameE (ZMod 2) 0 := by
  have hx := sixteenC8SpinFix_xvec_eq_zero v hv
  have hy := sixteenC8SpinFix_yvec_eq_zero v hv
  have hy₀ := sixteenC8SpinFix_coordY_eq_zero v hv
  have hx' : (fun j : Fin 3 => coordX (ZMod 2) v j.succ) = 0 := hx
  have hy' : (fun j : Fin 3 => coordY (ZMod 2) v j.succ) = 0 := hy
  have hcoords := frameVec_coords v
  rw [hx', hy', hy₀] at hcoords
  have hvf : v = frameVec (ZMod 2) (coordX (ZMod 2) v 0) 0 0 0 := hcoords.symm
  have hfv : frameVec (ZMod 2) (coordX (ZMod 2) v 0) 0 0 0 =
      coordX (ZMod 2) v 0 • frameE (ZMod 2) 0 := by
    simp [frameVec]
  have hveq : v = coordX (ZMod 2) v 0 • frameE (ZMod 2) 0 := hvf.trans hfv
  rcases (show ∀ c : ZMod 2, c = 0 ∨ c = 1 by decide) (coordX (ZMod 2) v 0) with h | h
  · left
    rw [hveq, h]
    simp
  · right
    rw [hveq, h]
    simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
