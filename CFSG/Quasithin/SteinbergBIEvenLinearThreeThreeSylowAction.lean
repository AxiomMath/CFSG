module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.SteinbergBI

open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Setup.X7a
  CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.OuterAutomorphisms
open scoped Pointwise commutatorElement

variable {K : Type} [Field K]

theorem commutator_mem_unitriangular {n : ℕ} {b₁ b₂ : SpecialLinearGroup (Fin n) K}
    (h₁ : b₁ ∈ upperTriangular n K) (h₂ : b₂ ∈ upperTriangular n K) :
    b₁ * b₂ * b₁⁻¹ * b₂⁻¹ ∈ unitriangular n K := by
  set x : upperTriangular n K := ⟨b₁, h₁⟩
  set y : upperTriangular n K := ⟨b₂, h₂⟩
  have h : x * y * x⁻¹ * y⁻¹ ∈ (diagHomLin n K).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      mul_comm (diagHomLin n K x) (diagHomLin n K y)]
    group
  rw [ker_diagHomLin, Subgroup.mem_subgroupOf] at h
  exact h

end CFSG.Quasithin.SteinbergBI
