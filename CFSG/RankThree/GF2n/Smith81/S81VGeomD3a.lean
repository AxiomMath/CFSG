module

public import CFSG.RankThree.GF2n.Smith81.S81U6Basic

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

structure Frame (σ : F ≃+* F) (a b : Fin 3 → Fin 6 → F) : Prop where
  aa : ∀ i j, herm σ (a i) (a j) = 0
  bb : ∀ i j, herm σ (b i) (b j) = 0
  ab : ∀ i j, herm σ (a i) (b j) = if i = j then 1 else 0

variable {a b : Fin 3 → Fin 6 → F}

private theorem herm_sum_right_aux {ι : Type*} (s : Finset ι) (x : Fin 6 → F) (f : ι → Fin 6 → F) :
    herm σ x (∑ i ∈ s, f i) = ∑ i ∈ s, herm σ x (f i) := by
  exact map_sum (hermL σ x) f s

theorem linearIndependent_of_gram {k : ℕ} (v : Fin k → Fin 6 → F)
    (hdet : (Matrix.of fun i j => herm σ (v i) (v j)).det ≠ 0) : LinearIndependent F v := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmul : Matrix.mulVec (Matrix.of fun i j => herm σ (v i) (v j)) c = 0 := by
    funext j
    have h1 := congrArg (herm σ (v j)) hc
    rw [herm_zero_right, herm_sum_right_aux] at h1
    simp only [herm_smul_right] at h1
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply]
    calc ∑ i, herm σ (v j) (v i) * c i = ∑ i, c i * herm σ (v j) (v i) :=
          Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := h1
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hmul
  intro i
  simp [hc0]

theorem finrank_span_of_gram {k : ℕ} (v : Fin k → Fin 6 → F)
    (hdet : (Matrix.of fun i j => herm σ (v i) (v j)).det ≠ 0) :
    finrank F (Submodule.span F (Set.range v)) = k := by
  rw [finrank_span_eq_card (linearIndependent_of_gram v hdet), Fintype.card_fin]

end CFSG.RankThree.GF2n.Smith81.S81V
