module

public import CFSG.RankThree.PartOne.N1322.CoreHyp
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartOne.N1322

open scoped Matrix
open CFSG.Assembly.LowTwoRank (StatedSL)

variable {K : Type*} [Field K]

@[expose] def tvGL (K : Type*) [Field K] : GL (Fin 3) K where
  val := !![1, 1, 0; 0, 1, 0; 0, 0, 1]
  inv := !![1, -1, 0; 0, 1, 0; 0, 0, 1]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

theorem tvGL_val : ((tvGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
    !![1, 1, 0; 0, 1, 0; 0, 0, 1] := rfl

theorem tvGL_det : ((tvGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  simp [tvGL, Matrix.det_fin_three]

theorem tvGL_mulVec (x : Fin 3 → K) :
    ((((tvGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) *ᵥ x) =
      (x 1) • (Pi.single 0 1 : Fin 3 → K) := by
  ext i
  rw [tvGL_val]
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, Matrix.one_apply]

theorem tvGL_rank : (((tvGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1).rank = 1 := by
  have hrange : LinearMap.range
      ((((tvGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1).mulVecLin) =
        Submodule.span K {(Pi.single 0 1 : Fin 3 → K)} := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [Matrix.mulVecLin_apply, tvGL_mulVec]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem]
      refine ⟨Pi.single 1 1, ?_⟩
      rw [Matrix.mulVecLin_apply, tvGL_mulVec]
      simp
  rw [Matrix.rank, hrange]
  refine finrank_span_singleton ?_
  intro h
  have := congrFun h 0
  simp at this

theorem tvGL_sq : (((tvGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) *
    (((tvGL K : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) = 0 := by
  rw [tvGL_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply]

theorem case1_false {p : ℕ} [Fact p.Prime] {d : CoreData (ZMod p)} (h : CoreHyp d)
    {H : Subgroup (GL (Fin 3) (ZMod p))} (hHX : H ≤ d.X) (h1 : H = StatedSL 3 (ZMod p)) :
    False := by
  have hmem : tvGL (ZMod p) ∈ H := by
    rw [h1]
    exact Subgroup.subset_closure (tvGL_det)
  exact h.noTransv _ (hHX hmem) ⟨tvGL_rank, tvGL_sq⟩

end CFSG.RankThree.PartOne.N1322
