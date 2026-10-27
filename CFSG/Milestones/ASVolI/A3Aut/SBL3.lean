module

public import CFSG.Milestones.ASVolI.A3Aut.SBBase

public section

namespace CFSG.ASVolI

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

section Linear

variable {K : Type} [Field K]

theorem burnsideAut_transvection_zero_one (c : K) :
    Matrix.transvection (0 : Fin 2) 1 c = !![1, c; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transvection, Matrix.single_apply]

theorem burnsideAut_transvection_one_zero (c : K) :
    Matrix.transvection (1 : Fin 2) 0 c = !![1, 0; c, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transvection, Matrix.single_apply]

theorem burnsideAut_not_isSolvable_of_reflection_mem {n : ℕ} [Finite K] (hK : 4 ≤ Nat.card K)
    {M : Subgroup (SpecialLinearGroup (Fin n) K)} (hU : unitriangular n K ≤ M) {i : ℕ}
    (hi : 1 ≤ i) (hin : i < n) (hr : reflection n K i hi hin ∈ M) : ¬ Group.IsSolvable ↥M := by
  set x : Fin n := ⟨i - 1, by omega⟩ with hx
  set y : Fin n := ⟨i, hin⟩ with hy
  have hxy : x < y := by rw [Fin.lt_def]; simp only [hx, hy]; omega
  have hne : x ≠ y := hxy.ne
  have hrefl : reflGroup n K i ≤ M := by
    refine sup_le hU ((Subgroup.closure_le _).2 (Set.singleton_subset_iff.2 ?_))
    rw [SetLike.mem_coe, reflElt_of_lt hi hin]
    exact hr
  have hup : ∀ c : K, SpecialLinearGroup.transvection hne c ∈ M := fun c =>
    hU (transvection_mem_unitriangular hxy c)
  have hlow : ∀ c : K, SpecialLinearGroup.transvection hne.symm c ∈ M := fun c =>
    hrefl (lower_transvection_mem_reflGroup hi hin hne.symm rfl (by simp only [hx]; omega) c)
  set ι : SpecialLinearGroup (Fin n) K →* GL (Fin n) K := SpecialLinearGroup.toGL with hι
  set φ : SpecialLinearGroup (Fin 2) K →* GL (Fin n) K := SymplecticTorusWeyl.pairGL hne with hφ
  have hrange : φ.range ≤ M.map ι := by
    rw [MonoidHom.range_eq_map, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2)
      (K := K), MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨g, ⟨a, b, hab, c, rfl⟩, rfl⟩
    fin_cases a <;> fin_cases b
    · exact absurd rfl hab
    · refine ⟨SpecialLinearGroup.transvection hne c, hup c, Units.ext ?_⟩
      change (SpecialLinearGroup.transvection hne c : Matrix (Fin n) (Fin n) K) =
        SymplecticTorusWeyl.pairMat x y (Matrix.transvection (0 : Fin 2) 1 c)
      rw [burnsideAut_transvection_zero_one, SymplecticHigher.pairMat_up hne]
      rfl
    · refine ⟨SpecialLinearGroup.transvection hne.symm c, hlow c, Units.ext ?_⟩
      change (SpecialLinearGroup.transvection hne.symm c : Matrix (Fin n) (Fin n) K) =
        SymplecticTorusWeyl.pairMat x y (Matrix.transvection (1 : Fin 2) 0 c)
      rw [burnsideAut_transvection_one_zero, SymplecticHigher.pairMat_low hne]
      rfl
    · exact absurd rfl hab
  have hφ1 : φ (SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (1 : K)) ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) x y) h
    change SymplecticTorusWeyl.pairMat x y (Matrix.transvection (0 : Fin 2) 1 (1 : K)) x y =
      (1 : Matrix (Fin n) (Fin n) K) x y at h1
    rw [burnsideAut_transvection_zero_one, SymplecticHigher.pairMat_up hne,
      Matrix.one_apply_ne hne] at h1
    simp [Matrix.add_apply, Matrix.single_apply, Matrix.one_apply_ne hne] at h1
  haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K hK
  intro hs
  have hs' : Group.IsSolvable ↥(M.map ι) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective M ι SpecialLinearGroup.toGL_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  exact burnsideAut_not_isSolvable_of_perfect_hom φ hφ1 hrange hs'

theorem burnsideAut_sl3_solvable_le [Finite K] (hK : 4 ≤ Nat.card K)
    {M : Subgroup (SpecialLinearGroup (Fin 3) K)} (hU : unitriangular 3 K ≤ M)
    (hM : Group.IsSolvable ↥M) : M ≤ upperTriangular 3 K := by
  have hcuts : borelOvergroupCuts M = {1, 2} := by
    ext i
    constructor
    · rintro ⟨hi, hin, -⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      omega
    · intro hi
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hi
      have h1 : 1 ≤ i := by omega
      have h3 : i < 3 := by omega
      exact ⟨h1, h3, fun hr => burnsideAut_not_isSolvable_of_reflection_mem hK hU h1 h3 hr hM⟩
  have hle := ((linear_unitriangular_overgroup_subflag_containment (n := 3) (K := K)).1 M hU).1
  rwa [hcuts, ← upperTriangular_eq_flagStabilizer] at hle

theorem burnsideAut_solvBorel_projectiveSL3 [Finite K] (hK : 4 ≤ Nat.card K) :
    burnsideAut_SolvBorel (projectiveSL 3 K) (projUnitriangular 3 K) := by
  refine burnsideAut_solvBorel_of_comap (proj 3 K) (proj_surjective 3 K) ?_ ?_
    (fun Y hUY hY => burnsideAut_sl3_solvable_le hK hUY hY)
  · intro a ha b _
    rw [ker_proj] at ha
    exact ((Subgroup.mem_center_iff.1 (scalars_le_center 3 K ha)) b).symm
  · exact Subgroup.le_normalizer_iff.2 fun b hb u hu => LinearFlag.conj_mem_unitriangular hb hu

end Linear

end CFSG.ASVolI
