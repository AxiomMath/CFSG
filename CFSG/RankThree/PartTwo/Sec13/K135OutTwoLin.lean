module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherOuterQuotients
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBUProjectivePlaneCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec13.F135Last

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane CFSG.Assembly.LowTwoRank

theorem ot_linear_D_cyclic_mod_inner {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) :
    ∃ g ∈ linearAutGroup n K, ∀ x ∈ linearAutGroup n K, ∃ k : ℤ,
      g ^ k * x ∈ (MulAut.conj : projectiveSL n K →* MulAut (projectiveSL n K)).range := by
  haveI : Finite Kˣ := Finite.of_injective (Units.val : Kˣ → K) Units.val_injective
  haveI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Kˣ)
  obtain ⟨M, hM⟩ := Matrix.GeneralLinearGroup.det_surjective (n := Fin n) (R := K) u
  refine ⟨conjAut n K M, conjAut_mem_linearAutGroup M, ?_⟩
  intro x hx
  obtain ⟨A, rfl⟩ := mem_linearAutGroup_iff.mp hx
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hu (Matrix.GeneralLinearGroup.det A))
  refine ⟨-j, ?_⟩
  rw [← map_zpow (conjAut n K) M (-j), ← map_mul]
  have hdet : Matrix.GeneralLinearGroup.det (M ^ (-j) * A) = 1 := by
    rw [map_mul, map_zpow, hM, ← hj, ← _root_.zpow_add]
    simp
  have hmem : M ^ (-j) * A ∈
      (SpecialLinearGroup.toGL : SpecialLinearGroup (Fin n) K →* GL (Fin n) K).range := by
    rw [SpecialLinearGroup.range_toGL_eq_ker_det, MonoidHom.mem_ker]
    exact hdet
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp hmem
  refine MonoidHom.mem_range.mpr ⟨proj n K s, ?_⟩
  rw [← hs, conjAut_toGL]

theorem ot_semilinear_le_linear {K : Type} [Field K] [Finite K] {n : ℕ}
    (h : Subsingleton (K ≃+* K)) :
    semilinearAutGroup n K ≤ linearAutGroup n K := by
  rw [semilinearAutGroup, Subgroup.closure_le]
  rintro _ (hD | ⟨σ, rfl⟩)
  · exact hD
  · rw [Subsingleton.elim σ 1, map_one]
    exact one_mem _

end CFSG.RankThree.PartTwo.Sec13.F135Last
