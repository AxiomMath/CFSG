module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_10_12

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowth

open Matrix CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.External
open scoped LinearAlgebra.Projectivization

universe u

variable {K : Type u} [Field K]

@[expose] def unitaryCoordinatePoint (i : Fin 3) : ℙ K (Fin 3 → K) :=
  Projectivization.mk K (Pi.single i 1) (Pi.single_ne_zero_iff.mpr one_ne_zero)

@[expose] def unitaryMiddleStabilizer (J : HermitianForm 3 K) :
    Subgroup (ProjectiveSpecialUnitaryMatrixGroup J) :=
  (MulAction.stabilizer (ProjGenLinGroup (Fin 3) K)
    (unitaryCoordinatePoint (K := K) 1)).comap
      (ProjectiveSpecialUnitaryMatrixGroup J).subtype

@[expose] def unitaryCoordinatePairPreserving (J : HermitianForm 3 K)
    (g : ProjectiveSpecialUnitaryMatrixGroup J) : Prop :=
  (((g : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
      unitaryCoordinatePoint (K := K) 0) ∧
    ((g : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
      unitaryCoordinatePoint (K := K) 2)) ∨
  (((g : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 0 =
      unitaryCoordinatePoint (K := K) 2) ∧
    ((g : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 2 =
      unitaryCoordinatePoint (K := K) 0))

theorem unitary_projective_coordinate_maps_iff (A : GL (Fin 3) K)
    (i j : Fin 3) :
    ProjGenLinGroup.mk A • unitaryCoordinatePoint (K := K) i =
        unitaryCoordinatePoint (K := K) j ↔
      ∀ k : Fin 3, k ≠ j → (A : Matrix (Fin 3) (Fin 3) K) k i = 0 := by
  rw [unitaryCoordinatePoint, Projectivization.PGL.mk_smul_mk,
    unitaryCoordinatePoint, Projectivization.mk_eq_mk_iff']
  change (∃ a : K, a • Pi.single j 1 =
    (A : Matrix (Fin 3) (Fin 3) K).mulVec (Pi.single i 1)) ↔ _
  rw [Matrix.mulVec_single_one]
  constructor
  · rintro ⟨a, ha⟩ k hkj
    simpa [Matrix.col, Pi.single_apply, hkj] using (congrFun ha k).symm
  · intro h
    refine ⟨(A : Matrix (Fin 3) (Fin 3) K) j i, ?_⟩
    funext k
    by_cases hkj : k = j
    · subst k
      simp [Matrix.col]
    · simp [Matrix.col, hkj, h k hkj]

theorem unitary_outer_plane_preserves_middle (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (A : GL (Fin 3) K) (hA : A ∈ J.unitarySubgroup)
    (h10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0)
    (h12 : (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0) :
    (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧
      (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
  let M : Matrix (Fin 3) (Fin 3) K := A
  have hdet : M.det = M 1 1 * (M 0 0 * M 2 2 - M 0 2 * M 2 0) := by
    dsimp only [M]
    simp only [Matrix.det_fin_three, h10, h12]
    ring
  have hminor : M 0 0 * M 2 2 - M 0 2 * M 2 0 ≠ 0 := by
    intro hz
    exact A.det_ne_zero (by rw [hdet, hz, mul_zero])
  have hconjminor :
      J.conj (M 0 0) * J.conj (M 2 2) -
        J.conj (M 0 2) * J.conj (M 2 0) ≠ 0 := by
    simpa only [map_sub, map_mul] using (map_ne_zero J.conj).mpr hminor
  have hgram := (J.mem_unitarySubgroup_iff A).mp hA
  have hfirst : J.conj (M 0 0) * M 2 1 + J.conj (M 2 0) * M 0 1 = 0 := by
    simpa [M, hJ, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, h10, add_comm] using congrArg (fun B => B 0 1) hgram
  have hlast : J.conj (M 0 2) * M 2 1 + J.conj (M 2 2) * M 0 1 = 0 := by
    simpa [M, hJ, HermitianForm.conjTranspose, Matrix.mul_apply,
      Fin.sum_univ_three, h12, add_comm] using congrArg (fun B => B 2 1) hgram
  have h01 : M 0 1 * (J.conj (M 0 0) * J.conj (M 2 2) -
      J.conj (M 0 2) * J.conj (M 2 0)) = 0 := by
    linear_combination J.conj (M 0 0) * hlast - J.conj (M 0 2) * hfirst
  have h21 : M 2 1 * (J.conj (M 0 0) * J.conj (M 2 2) -
      J.conj (M 0 2) * J.conj (M 2 0)) = 0 := by
    linear_combination J.conj (M 2 2) * hfirst - J.conj (M 2 0) * hlast
  exact ⟨(mul_eq_zero.mp h01).resolve_right hconjminor,
    (mul_eq_zero.mp h21).resolve_right hconjminor⟩

theorem unitary_projective_pair_preserves_middle (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (g : ProjectiveSpecialUnitaryMatrixGroup J)
    (hpair : unitaryCoordinatePairPreserving J g) :
    g ∈ unitaryMiddleStabilizer J := by
  obtain ⟨A, hA, hAg⟩ := g.property
  have h10 : (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := by
    rcases hpair with hfixed | hswap
    · exact (unitary_projective_coordinate_maps_iff A 0 0).mp
        (hAg.symm ▸ hfixed.1) 1 (by decide)
    · exact (unitary_projective_coordinate_maps_iff A 0 2).mp
        (hAg.symm ▸ hswap.1) 1 (by decide)
  have h12 : (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
    rcases hpair with hfixed | hswap
    · exact (unitary_projective_coordinate_maps_iff A 2 2).mp
        (hAg.symm ▸ hfixed.2) 1 (by decide)
    · exact (unitary_projective_coordinate_maps_iff A 2 0).mp
        (hAg.symm ▸ hswap.2) 1 (by decide)
  obtain ⟨h01, h21⟩ := unitary_outer_plane_preserves_middle J hJ A
    (J.specialSubgroup_le_unitarySubgroup hA) h10 h12
  change (g : ProjGenLinGroup (Fin 3) K) • unitaryCoordinatePoint (K := K) 1 = _
  rw [← hAg]
  apply (unitary_projective_coordinate_maps_iff A 1 1).mpr
  intro k hk
  fin_cases k
  · exact h01
  · exact (hk rfl).elim
  · exact h21

theorem unitary_root_mem_middle_iff (J : HermitianForm 3 K)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0])
    (z : hermitianUnipotentCoord J) :
    hermitianUnipotentPSU J hJ z ∈ unitaryMiddleStabilizer J ↔ z.1.1 = 0 := by
  change ProjGenLinGroup.mk (hermitianUnipotentGL J z) •
    unitaryCoordinatePoint (K := K) 1 = unitaryCoordinatePoint (K := K) 1 ↔ _
  rw [unitary_projective_coordinate_maps_iff]
  constructor
  · intro h
    simpa [hermitianUnipotentGL_val, hermitianUnipotentMatrix] using h 0 (by decide)
  · intro hz k hk
    fin_cases k
    · simpa [hermitianUnipotentGL_val, hermitianUnipotentMatrix] using hz
    · exact (hk rfl).elim
    · simp [hermitianUnipotentGL_val, hermitianUnipotentMatrix]

theorem unitary_middle_stabilizer_proper [Finite K] (J : HermitianForm 3 K)
    (q : ℕ) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    unitaryMiddleStabilizer J < ⊤ := by
  obtain ⟨b, hb⟩ := huppert_II_10_4_trace_surjective J q hcard hfixed (-1)
    (by simp)
  let z : hermitianUnipotentCoord J := ⟨(1, b), by
    simp only [map_one, one_mul]
    rw [hb]
    simp⟩
  have hmove : hermitianUnipotentPSU J hJ z ∉ unitaryMiddleStabilizer J := by
    rw [unitary_root_mem_middle_iff]
    exact one_ne_zero
  apply lt_top_iff_ne_top.mpr
  intro htop
  exact hmove (htop ▸ Subgroup.mem_top _)

theorem unitary_middle_generators_proper [Finite K] (J : HermitianForm 3 K)
    (q : ℕ) (hcard : Nat.card K = q ^ 2)
    (hfixed : Nat.card {x : K // J.conj x = x} = q)
    (hJ : J.form = !![0, 0, 1; 0, 1, 0; 1, 0, 0]) :
    Subgroup.closure
      ({g : ProjectiveSpecialUnitaryMatrixGroup J |
          ∃ z : hermitianUnipotentCoord J, z.1.1 = 0 ∧
            hermitianUnipotentPSU J hJ z = g} ∪
        {g : ProjectiveSpecialUnitaryMatrixGroup J |
          unitaryCoordinatePairPreserving J g}) < ⊤ := by
  apply lt_of_le_of_lt _ (unitary_middle_stabilizer_proper J q hcard hfixed hJ)
  apply (Subgroup.closure_le _).mpr
  intro g hg
  rcases hg with ⟨z, hz, rfl⟩ | hpair
  · exact (unitary_root_mem_middle_iff J hJ z).mpr hz
  · exact unitary_projective_pair_preserves_middle J hJ g hpair

end CFSG.ShultStronglyClosedTI.TwoCoreGrowth
