module

public import CFSG.RankThree.PartOne.KF.U4Su3
public import CFSG.RankThree.PartOne.KF.R9Perm
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KF.R12Unitary

public section

namespace CFSG.RankThree.PartOne.LSTD

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryCoord

variable {f : ℕ} {K : Type} [Field K]

section Proj

theorem mem_map_projU_iff {X : Subgroup ↥(unitarySU 2 f K 5)} {x : ↥(unitarySU 2 f K 5)} :
    projU K f x ∈ X.map (projU K f) ↔ ∃ z ∈ scalarsU K f, x * z ∈ X := by
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨x⁻¹ * y, ?_, ?_⟩
    · rw [← ker_projU, MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel]
    · rw [mul_inv_cancel_left]
      exact hy
  · rintro ⟨z, hz, hxz⟩
    refine ⟨x * z, hxz, ?_⟩
    have : projU K f z = 1 := by
      rw [← MonoidHom.mem_ker, ker_projU]
      exact hz
    rw [map_mul, this, mul_one]

theorem projU_eq_iff {x y : ↥(unitarySU 2 f K 5)} :
    projU K f x = projU K f y ↔ ∃ z ∈ scalarsU K f, x = y * z := by
  constructor
  · intro h
    refine ⟨y⁻¹ * x, ?_, by group⟩
    rw [← ker_projU, MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  · rintro ⟨z, hz, rfl⟩
    have : projU K f z = 1 := by
      rw [← MonoidHom.mem_ker, ker_projU]
      exact hz
    rw [map_mul, this, mul_one]

theorem exists_of_mem_scalarsU {z : ↥(unitarySU 2 f K 5)} (hz : z ∈ scalarsU K f) :
    ∃ c : Kˣ, (z : GL (Fin 5) K) = diagU (fun _ => c) := by
  obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp hz : (z : GL (Fin 5) K) ∈ StatedScalars (Fin 5) K)
  refine ⟨c, ?_⟩
  rw [← hc]
  apply Units.ext
  rw [diagU_val]
  simp [Matrix.GeneralLinearGroup.scalar]

end Proj

section Perm

variable {n : ℕ}

theorem permGL_conj_eq_coordPerm (σ : Equiv.Perm (Fin n)) (g : GL (Fin n) K) :
    permGL σ * g * (permGL σ)⁻¹ = coordPerm K σ g := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, coe_permGL, coe_permGL_inv, coe_coordPerm]
  have h1 : (σ⁻¹.permMatrix K) * (g : Matrix (Fin n) (Fin n) K) =
      (g : Matrix (Fin n) (Fin n) K).submatrix (σ⁻¹ : Equiv.Perm (Fin n)) id :=
    PEquiv.toMatrix_toPEquiv_mul _ _
  have h2 : ((g : Matrix (Fin n) (Fin n) K).submatrix (σ⁻¹ : Equiv.Perm (Fin n)) id) *
      σ.permMatrix K = ((g : Matrix (Fin n) (Fin n) K).submatrix
        (σ⁻¹ : Equiv.Perm (Fin n)) id).submatrix id σ.symm :=
    PEquiv.mul_toMatrix_toPEquiv _ _
  rw [h1, h2]
  rfl

end Perm

end CFSG.RankThree.PartOne.LSTD
