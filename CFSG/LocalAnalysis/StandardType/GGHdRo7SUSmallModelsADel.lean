module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUSmallModelsAQ9

public section

namespace CFSG.StandardType.HdRo7SU.Small

open CFSG.StandardType
open CFSG.StandardType.TypeAReflOver

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] noncomputable def hdRo7SmAAux_delEmbed : SMV 7 →ₗ[ZMod 3] SMV 8 :=
  LinearMap.pi (fun j : Fin 8 =>
    if h : j.val < 7 then (LinearMap.proj ⟨j.val, h⟩ : SMV 7 →ₗ[ZMod 3] ZMod 3)
    else (-1 : ZMod 3) • ∑ i, (LinearMap.proj i : SMV 7 →ₗ[ZMod 3] ZMod 3))

@[expose] noncomputable def hdRo7SmAAux_delProj : SMV 8 →ₗ[ZMod 3] SMV 7 :=
  LinearMap.pi fun i : Fin 7 => (LinearMap.proj i.castSucc : SMV 8 →ₗ[ZMod 3] ZMod 3)

@[simp] theorem hdRo7SmAAux_delEmbed_castSucc (v : SMV 7) (i : Fin 7) :
    hdRo7SmAAux_delEmbed v i.castSucc = v i := by
  simp [hdRo7SmAAux_delEmbed, LinearMap.pi_apply]

@[simp] theorem hdRo7SmAAux_delEmbed_last (v : SMV 7) :
    hdRo7SmAAux_delEmbed v (Fin.last 7) = -∑ i, v i := by
  rw [hdRo7SmAAux_delEmbed, LinearMap.pi_apply, dif_neg (by decide)]
  simp only [LinearMap.smul_apply, smul_eq_mul, LinearMap.sum_apply, LinearMap.proj_apply]
  exact neg_one_mul _

@[simp] theorem hdRo7SmAAux_delProj_apply (W : SMV 8) (i : Fin 7) :
    hdRo7SmAAux_delProj W i = W (Fin.castSucc i) := by
  simp [hdRo7SmAAux_delProj, LinearMap.pi_apply]

theorem hdRo7SmAAux_delProj_embed (v : SMV 7) :
    hdRo7SmAAux_delProj (hdRo7SmAAux_delEmbed v) = v := by
  ext i; simp

theorem hdRo7SmAAux_delEmbed_sum_zero (v : SMV 7) :
    ∑ j, hdRo7SmAAux_delEmbed v j = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp only [hdRo7SmAAux_delEmbed_castSucc, hdRo7SmAAux_delEmbed_last]
  abel

theorem hdRo7SmAAux_delEmbed_proj (W : SMV 8) (hW : ∑ j, W j = 0) :
    hdRo7SmAAux_delEmbed (hdRo7SmAAux_delProj W) = W := by
  ext j
  rw [Fin.sum_univ_castSucc] at hW
  by_cases h : j.val < 7
  · have hj : j = (⟨j.val, h⟩ : Fin 7).castSucc := Fin.ext rfl
    rw [hj, hdRo7SmAAux_delEmbed_castSucc, hdRo7SmAAux_delProj_apply]
  · have hj : j = Fin.last 7 := Fin.ext (by simp only [Fin.val_last]; omega)
    rw [hj, hdRo7SmAAux_delEmbed_last]
    simp only [hdRo7SmAAux_delProj_apply]
    exact neg_eq_iff_add_eq_zero.mpr hW

theorem hdRo7SmAAux_permLin_sum_zero (σ : Equiv.Perm (Fin 8)) (W : SMV 8)
    (hW : ∑ j, W j = 0) : ∑ j, hdRo7SmAAux_permLin 8 σ W j = 0 := by
  simp only [hdRo7SmAAux_permLin_apply]
  rw [Equiv.sum_comp σ.symm W, hW]

end CFSG.StandardType.HdRo7SU.Small
