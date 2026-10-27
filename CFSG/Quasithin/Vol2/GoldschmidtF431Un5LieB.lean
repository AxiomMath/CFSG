module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieA
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModU5Par

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

section Cent

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem proj_mem_u5PtP_iff {g : hypSU h 2 1} : hypProj h 2 1 g ∈ u5PtP h ↔ g ∈ u5PtStab h := by
  rw [← Subgroup.mem_comap, u5PtP, comap_projIsoStabilizer]

theorem proj_mem_u5LnP_iff {g : hypSU h 2 1} : hypProj h 2 1 g ∈ u5LnP h ↔ g ∈ u5LnStab h := by
  rw [← Subgroup.mem_comap, u5LnP, comap_projIsoStabilizer]

theorem commute_of_proj_commute {s g : hypSU h 2 1} (hs : s * s = 1)
    (hg : hypProj h 2 1 g ∈ Subgroup.centralizer ({hypProj h 2 1 s} : Set (hypPSU h 2 1))) :
    g * s = s * g := by
  have h1 : hypProj h 2 1 g * hypProj h 2 1 s = hypProj h 2 1 s * hypProj h 2 1 g :=
    Subgroup.mem_centralizer_singleton_iff.1 hg
  have hπ : hypProj h 2 1 (g * s * g⁻¹) = hypProj h 2 1 s := by
    rw [map_mul, map_mul, map_inv, h1]
    group
  have hsq : (g * s * g⁻¹) * (g * s * g⁻¹) = 1 := by
    calc (g * s * g⁻¹) * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs]; group
  have := eq_of_innM_eq_of_sq (u5_center_eq_bot h)
    (MulEquiv.ext fun y => by simp only [innM_apply, hπ]) hsq hs
  calc g * s = (g * s * g⁻¹) * g := by group
    _ = s * g := by rw [this]

theorem hsq_z₁SU : z₁SU h * z₁SU h = 1 := Vsub_sq (vSU_mem_Vsub (isHerm_e₁₁ h))

theorem hsq_z₂SU : z₂SU h * z₂SU h = 1 := Vsub_sq (vSU_mem_Vsub (isHerm_swap h))

theorem cent_z_Y : Subgroup.centralizer ({z5Y h} : Set (hypPSU h 2 1)) ≤ u5PtP h := by
  intro x hx
  obtain ⟨g, rfl⟩ := hypProj_surjective h 2 1 x
  have hc := commute_of_proj_commute hsq_z₁SU hx
  rw [proj_mem_u5PtP_iff, mem_u5PtStab_iff]
  intro a ha
  have hM : Commute (Matrix.single ιe₁ ιf₁ (1 : K)) (mat g) := by
    have := congrArg mat hc
    rw [mat_mul, mat_mul, mat_z₁SU_eq, mul_add, add_mul, mul_one, one_mul] at this
    exact (add_left_cancel this).symm
  exact Matrix.col_eq_zero_of_commute_single hM ha

theorem cent_t_Y : Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) ≤ u5LnP h := by
  intro x hx
  obtain ⟨g, rfl⟩ := hypProj_surjective h 2 1 x
  have hc := commute_of_proj_commute hsq_z₂SU hx
  rw [proj_mem_u5LnP_iff, mem_u5LnStab_iff]
  have hM : mat g * (Matrix.single ιe₁ ιf₂ (1 : K) + Matrix.single ιe₂ ιf₁ 1) =
      (Matrix.single ιe₁ ιf₂ (1 : K) + Matrix.single ιe₂ ιf₁ 1) * mat g := by
    have := congrArg mat hc
    rw [mat_mul, mat_mul, mat_z₂SU_eq, mul_add, add_mul, mul_one, one_mul] at this
    exact add_left_cancel this
  intro a b hb ha
  have ha' : a ≠ ιe₁ ∧ a ≠ ιe₂ := by
    rcases ha with rfl | rfl | rfl <;> decide
  rcases hb with rfl | rfl
  · have := congrFun (congrFun hM a) ιf₂
    simpa [Matrix.mul_add, Matrix.add_mul, ha'.1, ha'.2, ιe₁, ιe₂, ιf₁, ιf₂] using this
  · have := congrFun (congrFun hM a) ιf₁
    simpa [Matrix.mul_add, Matrix.add_mul, ha'.1, ha'.2, ιe₁, ιe₂, ιf₁, ιf₂] using this

theorem conj_sSU_z₁SU : sSU h * z₁SU h * (sSU h)⁻¹ = z₁SU h := by
  apply mat_injective
  ext a b
  rw [conj_sSU_apply, mat_z₁SU_eq]
  rcases Sec53F.Unit.hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases Sec53F.Unit.hypIndex_cases b with rfl | rfl | rfl | rfl | rfl <;>
    simp [σs, ιe₁, ιe₂, ιz, ιf₁, ιf₂, Equiv.swap_apply_def]

theorem conj_rSU_z₂SU : rSU h * z₂SU h * (rSU h)⁻¹ = z₂SU h := by
  apply mat_injective
  ext a b
  rw [conj_rSU_apply, mat_z₂SU_eq]
  rcases Sec53F.Unit.hypIndex_cases a with rfl | rfl | rfl | rfl | rfl <;>
    rcases Sec53F.Unit.hypIndex_cases b with rfl | rfl | rfl | rfl | rfl <;>
    simp [σr, ιe₁, ιe₂, ιz, ιf₁, ιf₂, Equiv.swap_apply_def]

theorem nz_Y : ¬ Subgroup.centralizer ({z5Y h} : Set (hypPSU h 2 1)) ≤ u5LnP h := by
  intro hle
  have hc : hypProj h 2 1 (sSU h) ∈ Subgroup.centralizer ({z5Y h} : Set (hypPSU h 2 1)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, z5Y, ← map_mul, ← map_mul]
    congr 1
    have e := conj_sSU_z₁SU (h := h)
    rw [mul_inv_eq_iff_eq_mul] at e
    exact e
  have h1 := proj_mem_u5LnP_iff.1 (hle hc)
  rw [mem_u5LnStab_iff] at h1
  have h0 := h1 ιf₂ ιe₂ (Or.inr rfl) (Or.inr (Or.inl rfl))
  rw [mat_sSU] at h0
  simp [σs, ιe₂, ιf₂] at h0

theorem nt_Y : ¬ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) ≤ u5PtP h := by
  intro hle
  have hc : hypProj h 2 1 (rSU h) ∈ Subgroup.centralizer ({t5Y h} : Set (hypPSU h 2 1)) := by
    rw [Subgroup.mem_centralizer_singleton_iff, t5Y, ← map_mul, ← map_mul]
    congr 1
    have e := conj_rSU_z₂SU (h := h)
    rw [mul_inv_eq_iff_eq_mul] at e
    exact e
  have h1 := proj_mem_u5PtP_iff.1 (hle hc)
  rw [mem_u5PtStab_iff] at h1
  have h0 := h1 ιe₂ (by decide)
  rw [mat_rSU] at h0
  simp [σr, ιe₁, ιe₂, ιf₁, ιf₂, Equiv.swap_apply_def] at h0

end Cent

end CFSG.Quasithin.H13.F431.Un
