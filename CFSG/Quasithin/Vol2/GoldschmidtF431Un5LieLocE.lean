module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocD
public import CFSG.LocalAnalysis.EvenBN.U5.ModelSylowRank
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieDefs

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un.L5

set_option linter.unusedSectionVars false

open Matrix Subgroup CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.LocalAnalysis.ComponentInitial

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} [CharP K 2]

abbrev Ct (h : UnitaryFieldData 2 f K) : Subgroup (hypPSU h 2 1) :=
  Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1))

theorem mem_Ct_iff {x : hypPSU h 2 1} : x ∈ Ct h ↔ x * t5Y h = t5Y h * x := by
  rw [Subgroup.mem_centralizer_singleton_iff]

theorem hypProj_mem_Ct {g : hypSU h 2 1} (e : g * z₂SU h = z₂SU h * g) :
    hypProj h 2 1 g ∈ Ct h := by
  rw [mem_Ct_iff]
  change hypProj h 2 1 g * hypProj h 2 1 (z₂SU h) = hypProj h 2 1 (z₂SU h) * hypProj h 2 1 g
  rw [← map_mul, ← map_mul, e]

theorem comm_zt : z5Y h * t5Y h = t5Y h * z5Y h := v5Y_comm z5Y_mem_v5Y t5Y_mem_v5Y

theorem vY_le_v5Y : vY h ≤ v5Y h := Subgroup.map_mono (Vt_le_Vsub h)

theorem vY_le_Ct : vY h ≤ Ct h := fun _ hv => mem_Ct_iff.2 (v5Y_comm (vY_le_v5Y hv) t5Y_mem_v5Y)

theorem vY_ab {a b : hypPSU h 2 1} (ha : a ∈ vY h) (hb : b ∈ vY h) : a * b = b * a :=
  v5Y_comm (vY_le_v5Y ha) (vY_le_v5Y hb)

theorem vY_sq {a : hypPSU h 2 1} (ha : a ∈ vY h) : a ^ 2 = 1 := v5Y_sq (vY_le_v5Y ha)

theorem z5Y_mem_vY : z5Y h ∈ vY h := ⟨z₁SU h, Rt_le_Vt h z₁SU_mem_Rt, rfl⟩

theorem ucY_le_vY : ucY h ≤ vY h := Subgroup.map_mono (Uct_le_Vt h)

theorem t5Y_mem_ucY : t5Y h ∈ ucY h := ⟨z₂SU h, z₂SU_mem_Uct, rfl⟩

theorem rY_le_vY : rY h ≤ vY h := Subgroup.map_mono (Rt_le_Vt h)

theorem vY_le_kY : vY h ≤ kY h := Subgroup.map_mono Vt_le_Kt

theorem levHom_comm_z₂SU (A : SpecialLinearGroup (Fin 2) h.fixedField) :
    levHom h A * z₂SU h = z₂SU h * levHom h A := by
  have := levHom_conj_z₂SU A
  rwa [mul_inv_eq_iff_eq_mul] at this

theorem kY_le_Ct : kY h ≤ Ct h := by
  rw [kY, Subgroup.map_le_iff_le_comap]
  refine sup_le (fun g hg => ?_) (fun g hg => ?_)
  · exact hypProj_mem_Ct (Vsub_comm (Vt_le_Vsub h hg) (vSU_mem_Vsub (isHerm_swap h)))
  · obtain ⟨A, rfl⟩ := hg
    exact hypProj_mem_Ct (levHom_comm_z₂SU A)

theorem kY_perfect (hf : 2 ≤ f) : ⁅kY h, kY h⁆ = kY h := by
  rw [kY, ← Subgroup.map_commutator]
  exact congrArg (Subgroup.map (hypProj h 2 1)) (Kt_perfect hf)

theorem eq_smul_J_of_mem_Uct {u : hypSU h 2 1} (hu : u ∈ Uct h) :
    ∃ b : K, Yof u = b • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K) := by
  obtain ⟨Y, hY, ⟨h00, h11, h01⟩, rfl⟩ := mem_vsub_iff.1 hu
  refine ⟨Y 0 1, ?_⟩
  rw [Yof_vSU hY]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h11, h01]

theorem levHom_comm_Uct (A : SpecialLinearGroup (Fin 2) h.fixedField) {u : hypSU h 2 1}
    (hu : u ∈ Uct h) : levHom h A * u = u * levHom h A := by
  obtain ⟨b, hb⟩ := eq_smul_J_of_mem_Uct hu
  obtain ⟨hm, hY⟩ := Yof_levHom_conj A (Uct_le_Vsub h hu)
  have e : levHom h A * u * (levHom h A)⁻¹ = u := by
    refine Yof_injOn h hm (Uct_le_Vsub h hu) ?_
    rw [hY, hb, Matrix.mul_smul, Matrix.smul_mul, mul_J_mul_transpose (det_slM A)]
  rwa [mul_inv_eq_iff_eq_mul] at e

theorem Kt_cent_Uct {k u : hypSU h 2 1} (hk : k ∈ Kt h) (hu : u ∈ Uct h) : k * u = u * k := by
  have : Kt h ≤ Subgroup.centralizer (Uct h : Set (hypSU h 2 1)) := by
    refine sup_le (fun g hg v hv => ?_) (fun g hg v hv => ?_)
    · exact (Vsub_comm (Uct_le_Vsub h hv) (Vt_le_Vsub h hg))
    · obtain ⟨A, rfl⟩ := hg
      exact (levHom_comm_Uct A hv).symm
  exact (Subgroup.mem_centralizer_iff.1 (this hk) u hu).symm

theorem kY_cent_ucY {k u : hypPSU h 2 1} (hk : k ∈ kY h) (hu : u ∈ ucY h) : k * u = u * k := by
  obtain ⟨k₀, hk₀, rfl⟩ := hk
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  rw [← map_mul, ← map_mul, Kt_cent_Uct hk₀ hu₀]

theorem z5Y_cent {y : hypPSU h 2 1} (hy : y ∈ hypProjUnitriangular h 2 1) :
    y * z5Y h = z5Y h * y := by
  obtain ⟨u, hu, rfl⟩ := hy
  change hypProj h 2 1 u * hypProj h 2 1 (z₁SU h) = hypProj h 2 1 (z₁SU h) * hypProj h 2 1 u
  rw [← map_mul, ← map_mul, ZPsub_commute z₁SU_mem_ZPsub hu]

theorem lift_comm_of_mem_U {w : hypSU h 2 1} (hw : w ∈ hypUnitriangular h 2 1)
    (hc : hypProj h 2 1 w ∈ Ct h) : w * z₂SU h = z₂SU h * w := by
  have hz : z₂SU h ∈ hypUnitriangular h 2 1 :=
    (Z₂Psub_le_A₂sub.trans A₂sub_le_U) z₂SU_mem_Z₂Psub
  have e : w * z₂SU h * w⁻¹ = z₂SU h := by
    refine hypProj_eq_of_mem_U (mul_mem (mul_mem hw hz) (inv_mem hw)) hz ?_
    have := mem_Ct_iff.1 hc
    change hypProj h 2 1 w * hypProj h 2 1 (z₂SU h) = hypProj h 2 1 (z₂SU h) * hypProj h 2 1 w
      at this
    rw [map_mul, map_mul, map_inv, mul_inv_eq_iff_eq_mul]
    exact this
  rwa [mul_inv_eq_iff_eq_mul] at e

theorem U_comm_Uct {w u : hypSU h 2 1} (hw : w ∈ hypUnitriangular h 2 1)
    (hwz : w * z₂SU h = z₂SU h * w) (hu : u ∈ Uct h) : w * u = u * w := by
  obtain ⟨a, x, C, -, hw'⟩ := exists_coord hw
  have hJ : mat (z₂SU h) = oddUni h 0 !![0, 1; 1, 0] := mat_vSU _
  have e1 : w * z₂SU h * w⁻¹ = z₂SU h := by rwa [mul_inv_eq_iff_eq_mul]
  have e2 := U_conj_V hw' hJ
  rw [e1, hJ] at e2
  have hAJ := (oddUni_inj e2).2
  obtain ⟨b, hb⟩ := eq_smul_J_of_mem_Uct hu
  have hu' : mat u = oddUni h 0 (b • (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)) := by
    obtain ⟨-, Y, hY⟩ := Uct_le_Vsub h hu
    rw [hY]
    congr 2
    rw [← hb, Yof_eq hY]
  have e3 := U_conj_V hw' hu'
  rw [Matrix.mul_smul, Matrix.smul_mul, ← hAJ, ← hu'] at e3
  have e4 : w * u * w⁻¹ = u := mat_injective e3
  rwa [mul_inv_eq_iff_eq_mul] at e4

theorem P_U_Y {y : hypPSU h 2 1} (hy : y ∈ hypProjUnitriangular h 2 1 ⊓ Ct h) {u : hypPSU h 2 1}
    (hu : u ∈ ucY h) : y * u = u * y := by
  obtain ⟨⟨w, hw, rfl⟩, hC⟩ := hy
  obtain ⟨u₀, hu₀, rfl⟩ := hu
  rw [← map_mul, ← map_mul, U_comm_Uct hw (lift_comm_of_mem_U hw hC) hu₀]

end CFSG.Quasithin.H13.F431.Un.L5
