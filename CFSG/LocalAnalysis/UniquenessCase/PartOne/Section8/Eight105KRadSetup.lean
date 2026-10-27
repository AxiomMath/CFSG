module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusUnitaryFlag

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105

open CFSG.Open Subgroup Matrix
open CFSG.Assembly.LowTwoRank (StatedSU)
open scoped Pointwise

variable {K : Type} [Field K]

@[expose] noncomputable def eigSU {n q : ℕ} (y : StatedSU n q K) (μ : K) :
    Submodule K (Fin n → K) :=
  Module.End.eigenspace (Matrix.toLin' ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) μ

theorem mem_eigSU {n q : ℕ} {y : StatedSU n q K} {μ : K} {v : Fin n → K} :
    v ∈ eigSU y μ ↔ ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = μ • v := by
  rw [eigSU, Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

@[expose] def stabSU {n : ℕ} (q : ℕ) (W : Submodule K (Fin n → K)) :
    Subgroup (StatedSU n q K) :=
  (MulAction.stabilizer (GL (Fin n) K) W).subgroupOf (StatedSU n q K)

theorem mem_stabSU {n q : ℕ} {W : Submodule K (Fin n → K)} {y : StatedSU n q K} :
    y ∈ stabSU q W ↔ ∀ w ∈ W, ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ w ∈ W := by
  rw [stabSU, Subgroup.mem_subgroupOf, MulAction.mem_stabilizer_iff]
  exact CFSG.AGLEmbedding.ToralCensus.smul_eq_iff_mulVec_mem _ W

theorem centralizer_le_stabSU_eigSU {n q : ℕ} (b : StatedSU n q K) (μ : K) :
    centralizer ((zpowers b : Subgroup (StatedSU n q K)) : Set (StatedSU n q K)) ≤
      stabSU q (eigSU b μ) := by
  intro y hy
  have hyb : b * y = y * b := mem_centralizer_iff.mp hy b (mem_zpowers b)
  have hM : ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((y : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    have := congrArg (fun z : StatedSU n q K => ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
      hyb
    simpa using this
  rw [mem_stabSU]
  intro w hw
  rw [mem_eigSU] at hw ⊢
  rw [mulVec_mulVec, hM, ← mulVec_mulVec, hw, mulVec_smul]

theorem kOf_le_stabSU_eigSU [Finite K] {n q : ℕ} (b : StatedSU n q K) (μ : K) :
    UC22.F08.KOf8103 ⊤ (zpowers b) ≤ stabSU q (eigSU b μ) :=
  ((map_subtype_le _).trans inf_le_right).trans (centralizer_le_stabSU_eigSU b μ)

structure RadSetup {f : ℕ} (ε : ℕ) (b : StatedSU (2 * 2 + ε) (2 ^ f) K) (ω : K) : Prop where
  even : Even f
  le_one : ε ≤ 1
  ne_one : ω ≠ 1
  cube : ω ^ 3 = 1
  pow_three : b ^ 3 = 1
  finrank_eig : Module.finrank K (eigSU b ω) = 2
  finrank_eig_inv : Module.finrank K (eigSU b ω⁻¹) = 2

theorem RadSetup.symm {f ε : ℕ} {b : StatedSU (2 * 2 + ε) (2 ^ f) K} {ω : K}
    (hS : RadSetup ε b ω) : RadSetup ε b ω⁻¹ :=
  ⟨hS.even, hS.le_one, inv_ne_one.mpr hS.ne_one, by rw [inv_pow, hS.cube, inv_one],
    hS.pow_three, hS.finrank_eig_inv, by rw [inv_inv]; exact hS.finrank_eig⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K105
