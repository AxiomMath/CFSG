module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableSix

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.LieType.Universal.Spin

private theorem s15k_tms_apply (k : ℕ) (v : Fin k ⊕ Fin k ⊕ Fin 2 → ZMod 2) :
    quadMinus (k + 1) (ZMod 2) 1 1 v = ∑ i : Fin k, v (.inl i) * v (.inr (.inl i)) +
      v (.inr (.inr 0)) ^ 2 + 1 * v (.inr (.inr 0)) * v (.inr (.inr 1)) +
        1 * v (.inr (.inr 1)) ^ 2 :=
  quadMinus_apply (k + 1) (ZMod 2) 1 1 v

private theorem s15k_tms_polar (k : ℕ) (v w : Fin k ⊕ Fin k ⊕ Fin 2 → ZMod 2) :
    QuadraticMap.polar (quadMinus (k + 1) (ZMod 2) 1 1) v w =
      ∑ i : Fin k, (v (.inl i) * w (.inr (.inl i)) + w (.inl i) * v (.inr (.inl i))) +
        2 * (v (.inr (.inr 0)) * w (.inr (.inr 0))) +
        1 * (v (.inr (.inr 0)) * w (.inr (.inr 1)) + w (.inr (.inr 0)) * v (.inr (.inr 1))) +
          2 * 1 * (v (.inr (.inr 1)) * w (.inr (.inr 1))) :=
  polar_quadMinus (k + 1) (ZMod 2) 1 1 v w

private theorem s15k_tms_embed (m : ℕ) :
    ∃ (E : (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2) → (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2))
      (R : (Fin (m + 1) ⊕ Fin (m + 1) ⊕ Fin 2 → ZMod 2) → (Fin m ⊕ Fin m ⊕ Fin 2 → ZMod 2)),
      (∀ p, quadMinus (m + 1 + 1) (ZMod 2) 1 1 (E p) = quadMinus (m + 1) (ZMod 2) 1 1 p) ∧
      (∀ z p, QuadraticMap.polar (quadMinus (m + 1 + 1) (ZMod 2) 1 1) z (E p) =
        QuadraticMap.polar (quadMinus (m + 1) (ZMod 2) 1 1) (R z) p) ∧ ∀ p, R (E p) = p := by
  refine ⟨fun p => Sum.elim (fun i => Fin.lastCases 0 (fun j => p (Sum.inl j)) i)
      (Sum.elim (fun i => Fin.lastCases 0 (fun j => p (Sum.inr (Sum.inl j))) i)
        (fun j => p (Sum.inr (Sum.inr j)))),
    fun w => Sum.elim (fun j => w (Sum.inl j.castSucc))
      (Sum.elim (fun j => w (Sum.inr (Sum.inl j.castSucc))) (fun j => w (Sum.inr (Sum.inr j)))),
    ?_, ?_, ?_⟩
  · intro p
    rw [s15k_tms_apply, s15k_tms_apply, Fin.sum_univ_castSucc]
    simp
  · intro w p
    rw [s15k_tms_polar, s15k_tms_polar, Fin.sum_univ_castSucc]
    simp
  · intro p
    funext i
    rcases i with i | i | i <;> simp

private theorem s15k_tms_plane (m : ℕ) (z : Fin (m + 2) ⊕ Fin (m + 2) ⊕ Fin 2 → ZMod 2) :
    s15kPlane (quadMinus (m + 3) (ZMod 2) 1 1) z := by
  induction m with
  | zero => exact s15k_table_minus_three z
  | succ m ih =>
    obtain ⟨E, R, hE, hR, hRE⟩ := s15k_tms_embed (m + 2)
    exact s15k_table_plane_of_embed (quadMinus (m + 2 + 1) (ZMod 2) 1 1)
      (quadMinus (m + 2 + 1 + 1) (ZMod 2) 1 1) E R hE hR hRE z (ih (R z))

private theorem s15k_tms_pair (m : ℕ) (z : Fin (m + 3) ⊕ Fin (m + 3) ⊕ Fin 2 → ZMod 2) :
    s15kPlanePair (quadMinus (m + 4) (ZMod 2) 1 1) z := by
  induction m with
  | zero => exact s15k_table_minus_four z
  | succ m ih =>
    obtain ⟨E, R, hE, hR, hRE⟩ := s15k_tms_embed (m + 3)
    exact s15k_table_planePair_of_embed (quadMinus (m + 3 + 1) (ZMod 2) 1 1)
      (quadMinus (m + 3 + 1 + 1) (ZMod 2) 1 1) E R hE hR hRE z (ih (R z))

theorem s15k_table_minus_split {k : ℕ} (hk : 3 ≤ k)
    (z : Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2 → ZMod 2) :
    s15kPlane (quadMinus k (ZMod 2) 1 1) z ∧
      (4 ≤ k → s15kPlanePair (quadMinus k (ZMod 2) 1 1) z) := by
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 3 := ⟨k - 3, by omega⟩
  refine ⟨s15k_tms_plane m z, fun h4 => ?_⟩
  obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  exact s15k_tms_pair m' z

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
