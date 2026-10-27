module

public import CFSG.Quasithin.Vol2.Ch3E213MP5B
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2ProjectiveLine
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import Mathlib.LinearAlgebra.Projectivization.Cardinality

public section

namespace CFSG.Quasithin.Ch3E213M.P5

open Matrix CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.GorensteinWalter
open scoped MatrixGroups

variable {k : Type} [Field k]

local notation "M2" => Matrix (Fin 2) (Fin 2) k
local notation "M3" => Matrix (Fin 3) (Fin 3) k

@[expose] def cornerMat (g : M2) : M3 := !![g 0 0, 0, g 0 1; 0, 1, 0; g 1 0, 0, g 1 1]

theorem det_cornerMat (g : M2) : (cornerMat g).det = g.det := by
  rw [cornerMat, Matrix.det_fin_three, Matrix.det_fin_two]
  simp

theorem cornerMat_mul (g h : M2) : cornerMat (g * h) = cornerMat g * cornerMat h := by
  ext i j
  simp only [cornerMat, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_three]
  fin_cases i <;> fin_cases j <;> simp

variable (k) in
@[expose] def corner : SL(2, k) →* Matrix.SpecialLinearGroup (Fin 3) k where
  toFun g := ⟨cornerMat (g : M2), by rw [det_cornerMat]; exact g.2⟩
  map_one' := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_one]
    change cornerMat (1 : M2) i j = (1 : M3) i j
    fin_cases i <;> fin_cases j <;> simp [cornerMat]
  map_mul' g h := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    change cornerMat ((g : M2) * (h : M2)) i j = (cornerMat (g : M2) * cornerMat (h : M2)) i j
    rw [cornerMat_mul]

theorem coe_corner (g : SL(2, k)) :
    ((corner k g : Matrix.SpecialLinearGroup (Fin 3) k) : M3) = cornerMat (g : M2) := rfl

variable (k) in
@[expose] def cornerHom : SL(2, k) →* projectiveSL 3 k := (proj 3 k).comp (corner k)

theorem cornerHom_apply (g : SL(2, k)) : cornerHom k g = proj 3 k (corner k g) := rfl

theorem exists_scalar_of_proj_eq {g : SL(2, k)} {x : Matrix.SpecialLinearGroup (Fin 3) k}
    (h : proj 3 k x = proj 3 k (corner k g)) :
    ∃ c : k, cornerMat (g : M2) = (x : M3) * scalar (Fin 3) c := by
  obtain ⟨s, -, hs⟩ := proj_eq_proj_iff.mp h
  refine ⟨(s : k), ?_⟩
  rw [← coe_corner, ← hs, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel_left]

theorem cornerHom_injective : Function.Injective (cornerHom k) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  rw [MonoidHom.mem_ker, cornerHom_apply, ← map_one (proj 3 k)] at hg
  obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq hg.symm
  rw [Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul] at hc
  have h11 : (1 : k) = c := by simpa [cornerMat] using congrFun (congrFun hc 1) 1
  subst h11
  rw [Subgroup.mem_bot]
  ext i j
  have h := congrFun (congrFun hc (if i = 0 then 0 else 2)) (if j = 0 then 0 else 2)
  fin_cases i <;> fin_cases j <;> simpa [cornerMat] using h

theorem corner_sl2UpperUnipotent (x : k) : corner k (sl2UpperUnipotent x) = uu 0 0 x := by
  ext i j
  rw [coe_corner, coe_uu]
  fin_cases i <;> fin_cases j <;> simp [cornerMat, sl2UpperUnipotent]

theorem map_sl2UpperUnipotent : (sl2UpperUnipotentSubgroup k).map (cornerHom k) = pzz k := by
  rw [cornerHom, ← Subgroup.map_map, pzz]
  congr 1
  ext g
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨x, rfl⟩ := (mem_sl2UpperUnipotentSubgroup_iff y).1 hy
    exact ⟨x, corner_sl2UpperUnipotent x⟩
  · rintro ⟨x, rfl⟩
    exact ⟨sl2UpperUnipotent x, (mem_sl2UpperUnipotentSubgroup_iff _).2 ⟨x, rfl⟩,
      corner_sl2UpperUnipotent x⟩

theorem projUnitriangular_inf_range :
    projUnitriangular 3 k ⊓ (cornerHom k).range = pzz k := by
  refine le_antisymm ?_ (le_inf (pzz_le_pa1.trans pa1_le) ?_)
  · rintro y ⟨⟨u, hu, rfl⟩, ⟨g, hg⟩⟩
    rw [cornerHom_apply] at hg
    obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq hg.symm
    obtain ⟨a, b, c', rfl⟩ := exists_eq_uu hu
    have h11 : (1 : k) = c := by
      simpa [cornerMat, coe_uu, Matrix.mul_apply, Fin.sum_univ_three] using
        congrFun (congrFun hc 1) 1
    subst h11
    have h01 : (0 : k) = a := by
      simpa [cornerMat, coe_uu, Matrix.mul_apply, Fin.sum_univ_three] using
        congrFun (congrFun hc 0) 1
    have h12 : (0 : k) = b := by
      simpa [cornerMat, coe_uu, Matrix.mul_apply, Fin.sum_univ_three] using
        congrFun (congrFun hc 1) 2
    subst h01 h12
    exact ⟨uu 0 0 c', ⟨c', rfl⟩, rfl⟩
  · rw [← map_sl2UpperUnipotent]
    exact Subgroup.map_le_range _ _

theorem projUpperTriangular_inf_range :
    projUpperTriangular 3 k ⊓ (cornerHom k).range = (sl2Borel k).map (cornerHom k) := by
  refine le_antisymm ?_ (le_inf ?_ (Subgroup.map_le_range _ _))
  · rintro y ⟨⟨u, hu, rfl⟩, ⟨g, hg⟩⟩
    rw [cornerHom_apply] at hg
    obtain ⟨c, hc⟩ := exists_scalar_of_proj_eq hg.symm
    have h20 := congrFun (congrFun hc 2) 0
    simp only [cornerMat, Matrix.mul_apply, Fin.sum_univ_three] at h20
    simp [mem_upperTriangular.1 hu 2 0 (by decide), mem_upperTriangular.1 hu 2 1 (by decide)]
      at h20
    exact ⟨g, (sl2_mem_stabilizer_infinity_iff g).2 h20, hg⟩
  · rintro _ ⟨g, hg, rfl⟩
    replace hg := (sl2_mem_stabilizer_infinity_iff g).1 hg
    refine ⟨corner k g, fun i j hij => ?_, rfl⟩
    rw [coe_corner]
    fin_cases i <;> fin_cases j <;> simp_all [cornerMat]

end CFSG.Quasithin.Ch3E213M.P5
