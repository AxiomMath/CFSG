module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeUniModel

public section

namespace CFSG.StandardType.TablePThreeKG

open Matrix Module CFSG CFSG.Assembly CFSG.AGLEmbedding

abbrev cubeEigen {n : ℕ} {K : Type} [Field K] (d : GL (Fin n) K) (μ : K) : Submodule K (Fin n → K) :=
  Module.End.eigenspace (Matrix.toLin' (d : Matrix (Fin n) (Fin n) K)) μ

@[expose] def InCubeBlock {n : ℕ} {K : Type} [Field K] {q : ℕ} (d : GL (Fin n) K) (μ : K) (x : PSUg n K q) : Prop :=
  ∃ g : ↥(LargeEvenSUGroup (Fin n) K q), LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q) g = x ∧
    ∀ ν : K, ν ^ 3 = 1 → ν ≠ μ → ∀ v ∈ cubeEigen d ν,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v

@[expose] def CubeBlockQS {n : ℕ} {K : Type} [Field K] (q : ℕ) (d : GL (Fin n) K) (μ : K) : Prop :=
  (2 ≤ Module.finrank K (cubeEigen d μ) ∧ 4 ≤ q) ∨ 4 ≤ Module.finrank K (cubeEigen d μ)

@[expose] def eigSub {K : Type} [Field K] {n : ℕ} (q : ℕ) (d : GL (Fin n) K) (μ : K) :
    Subgroup ↥(LargeEvenSUGroup (Fin n) K q) where
  carrier := {g | ∀ ν : K, ν ^ 3 = 1 → ν ≠ μ → ∀ v ∈ cubeEigen d ν,
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v}
  mul_mem' := by
    intro a b ha hb ν hν hνμ v hv
    have hb' : ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
      hb ν hν hνμ v hv
    have ha' : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
      ha ν hν hνμ v hv
    have h2 : (((a * b : ↥(LargeEvenSUGroup (Fin n) K q)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) =
        ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
          ((b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
      rw [← Units.val_mul]
      rfl
    show (((a * b : ↥(LargeEvenSUGroup (Fin n) K q)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ v = v
    rw [h2, ← Matrix.mulVec_mulVec, hb', ha']
  one_mem' := by
    intro ν hν hνμ v hv
    show ((↑(1 : ↥(LargeEvenSUGroup (Fin n) K q)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ v = v
    simp
  inv_mem' := by
    intro a ha ν hν hνμ v hv
    have ha' : ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ v = v :=
      ha ν hν hνμ v hv
    have h1 : (((a⁻¹ : ↥(LargeEvenSUGroup (Fin n) K q)) : GL (Fin n) K) *
        (a : GL (Fin n) K)) = 1 := inv_mul_cancel (a : GL (Fin n) K)
    have h2 : (((a⁻¹ : ↥(LargeEvenSUGroup (Fin n) K q)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) * ((a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
      rw [← Units.val_mul, h1]
      rfl
    show (((a⁻¹ : ↥(LargeEvenSUGroup (Fin n) K q)) : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) *ᵥ v = v
    rw [← ha', Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, ha']

@[expose] def eigBlock {K : Type} [Field K] {n : ℕ} (q : ℕ) (d : GL (Fin n) K) (μ : K) :
    Subgroup (PSUg n K q) :=
  (eigSub q d μ).map (LargeEvenProjMk (LargeEvenSUGroup (Fin n) K q))

theorem mem_eigBlock_iff {K : Type} [Field K] {n : ℕ} {q : ℕ} {d : GL (Fin n) K} {μ : K}
    {x : PSUg n K q} : x ∈ eigBlock q d μ ↔ InCubeBlock d μ x := by
  rw [eigBlock, Subgroup.mem_map]
  unfold InCubeBlock
  constructor
  · rintro ⟨g, hg, hgx⟩
    exact ⟨g, hgx, hg⟩
  · rintro ⟨g, hgx, hg⟩
    exact ⟨g, hg, hgx⟩

end CFSG.StandardType.TablePThreeKG

end
