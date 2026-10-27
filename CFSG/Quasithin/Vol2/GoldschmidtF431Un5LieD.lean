module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieC
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieB

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.RankThree.PartOne.U5K.Hyp CFSG.LocalAnalysis.EvenBN.U5 CFSG.Quasithin.H13.Sec53F.Unit

section Core

variable {f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K}

theorem lev_mem_u5LnStab (A : Matrix (Fin 2) (Fin 2) K) (hA : IsUnit A.det) :
    lev (hK := h) A hA ∈ u5LnStab h := by
  rw [mem_u5LnStab_iff]
  intro a b hb ha
  rw [mat_lev]
  rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl <;>
    simp [oddDiag, ιz, ιe₁, ιe₂, ιf₁, ιf₂]

theorem U_le_u5LnP : hypProjUnitriangular h 2 1 ≤ u5LnP h := by
  intro x hx
  have : x ∈ u5PtP h ⊓ u5LnP h := by
    rw [u5PtP_inf_u5LnP, ← normalizer_U_eq_borel_Y]
    exact Subgroup.le_normalizer hx
  exact this.2

theorem isSylowTwoOf_U_u5LnP : IsSylowTwoOf (hypProjUnitriangular h 2 1) (u5LnP h) :=
  F7.isSylowTwoOf_mono_right (u5_sylow h) U_le_u5LnP le_top

theorem mat_e₂e₁_of_proj_mem {g : hypSU h 2 1}
    (hg : hypProj h 2 1 g ∈ hypProjUnitriangular h 2 1) : mat g ιe₂ ιe₁ = 0 := by
  obtain ⟨u, hu, e⟩ := hg
  have hz : u⁻¹ * g ∈ hypScalars h 2 1 := by
    rw [← ker_hypProj, MonoidHom.mem_ker, map_mul, map_inv, e, inv_mul_cancel]
  obtain ⟨c, -, -, hc⟩ := hz
  have h2 : mat (u⁻¹ * g) = Matrix.scalar _ (c : K) := by
    change ((u⁻¹ * g : hypSU h 2 1) : GL (HypIndex 2 1) K).1 = _
    rw [hc]
    rfl
  have hm : mat g = mat u * Matrix.scalar _ (c : K) := by
    calc mat g = mat (u * (u⁻¹ * g)) := by rw [mul_inv_cancel_left]
      _ = mat u * mat (u⁻¹ * g) := mat_mul _ _
      _ = mat u * Matrix.scalar _ (c : K) := by rw [h2]
  rw [hm]
  simp [Matrix.mul_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
    U_lower hu (a := ιe₂) (b := ιe₁) (by decide)]

theorem pCoreOf_u5LnP_le_S : pCoreOf 2 (u5LnP h) ≤ (Ssub h).map (hypProj h 2 1) := by
  intro x hx
  have hxU : x ∈ hypProjUnitriangular h 2 1 :=
    pCoreOf_le_of_isSylowTwoOf isSylowTwoOf_U_u5LnP hx
  obtain ⟨u, hu, rfl⟩ := hxU
  have hlP : hypProj h 2 1 (lev swapM isUnit_det_swapM) ∈ u5LnP h :=
    proj_mem_u5LnP_iff.2 (lev_mem_u5LnStab _ _)
  have h1 : hypProj h 2 1 (lev swapM isUnit_det_swapM) * hypProj h 2 1 u *
      (hypProj h 2 1 (lev swapM isUnit_det_swapM))⁻¹ ∈ pCoreOf 2 (u5LnP h) :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 _ hlP) _).1 hx
  have h2 : hypProj h 2 1 (lev swapM isUnit_det_swapM * u * (lev swapM isUnit_det_swapM)⁻¹) ∈
      hypProjUnitriangular h 2 1 := by
    rw [map_mul, map_mul, map_inv]
    exact pCoreOf_le_of_isSylowTwoOf isSylowTwoOf_U_u5LnP h1
  have h3 := mat_e₂e₁_of_proj_mem h2
  rw [swap_conj_entry hu] at h3
  exact ⟨u, (mem_Ssub_iff hu).2 h3, rfl⟩

end Core

end CFSG.Quasithin.H13.F431.Un
