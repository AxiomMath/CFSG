module

public import Certificates.Certificate17001


public section

namespace CFSG.Quasithin.JonesParshall

open Matrix

section Generic

variable {n : ℕ}

abbrev muF2 (n : ℕ) : SpecialLinearGroup (Fin n) (ZMod 2) →* AddMonoid.End (Fin n → ZMod 2) :=
  DistribMulAction.toAddMonoidEnd _ _

theorem wordEval_mem_closure {G : Type*} [Group G] {k : ℕ} (gens : Fin k → G)
    (w : List (Fin k)) : wordEval gens w ∈ Subgroup.closure (Set.range gens) := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih => exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨i, rfl⟩) ih

theorem wordEval_eq_one {gens : Fin 2 → SpecialLinearGroup (Fin n) (ZMod 2)} {w : List (Fin 2)}
    (h : wordEvalM (fun k => (gens k : Matrix (Fin n) (Fin n) (ZMod 2))) w = 1) :
    wordEval gens w = 1 := by
  apply Subtype.ext
  rw [coe_wordEval, h]
  rfl

theorem closure_range_eq_top {gens : Fin 2 → SpecialLinearGroup (Fin n) (ZMod 2)}
    {tw : Fin n → Fin n → List (Fin 2)}
    (htw : ∀ i j, i ≠ j →
      wordEvalM (fun k => (gens k : Matrix (Fin n) (Fin n) (ZMod 2))) (tw i j) =
        transvection i j 1) :
    Subgroup.closure (Set.range gens) = ⊤ := by
  refine closure_eq_top_of_transvection fun t => ?_
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) t.c with hc | hc
  · have : t.toSpecialLinearGroup = 1 := by
      apply Subtype.ext
      change t.toMatrix = 1
      rw [TransvectionStruct.toMatrix, hc, transvection_zero]
    rw [this]
    exact Subgroup.one_mem _
  · have : t.toSpecialLinearGroup = wordEval gens (tw t.i t.j) := by
      apply Subtype.ext
      rw [coe_wordEval, htw t.i t.j t.hij]
      change t.toMatrix = _
      rw [TransvectionStruct.toMatrix, hc]
    rw [this]
    exact wordEval_mem_closure gens _

theorem vals_eq {M : Type*} (f : Fin 2 → M) : f = ![f 0, f 1] := by
  funext i
  fin_cases i <;> rfl

theorem Z1A_le_B1A_of_rels {gens : Fin 2 → SpecialLinearGroup (Fin n) (ZMod 2)}
    {tw : Fin n → Fin n → List (Fin 2)}
    (htw : ∀ i j, i ≠ j →
      wordEvalM (fun k => (gens k : Matrix (Fin n) (Fin n) (ZMod 2))) (tw i j) =
        transvection i j 1)
    {rels : List (List (Fin 2))}
    (hrels : ∀ r ∈ rels, wordEvalM (fun k => (gens k : Matrix (Fin n) (Fin n) (ZMod 2))) r = 1)
    (hsol : ∀ v₁ v₂ : Fin n → ZMod 2,
      (∀ r ∈ rels, foxEvalM (fun k => (gens k : Matrix (Fin n) (Fin n) (ZMod 2))) ![v₁, v₂] r =
        0) →
      ∃ v, v₁ = (gens 0 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v ∧
        v₂ = (gens 1 : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v) :
    Z1A (muF2 n) ≤ B1A (muF2 n) := by
  intro f hf
  have hrel : ∀ r ∈ rels, foxEvalM (fun k => (gens k : Matrix (Fin n) (Fin n) (ZMod 2)))
      ![f (gens 0), f (gens 1)] r = 0 := fun r hr => by
    have h := (foxEval_SL gens (fun i => f (gens i)) r).symm.trans
      (Z1A_wordEval hf gens r).symm
    rw [wordEval_eq_one (hrels r hr), Z1A_one hf, ← vals_eq (fun i => f (gens i))] at *
    exact h
  obtain ⟨v, hv₁, hv₂⟩ := hsol _ _ hrel
  have hf' : f - coboundaryA (muF2 n) v ∈ Z1A (muF2 n) := sub_mem hf (B1A_le_Z1A _ ⟨v, rfl⟩)
  have h0 := eq_zero_of_vanish_closure hf' (closure_range_eq_top htw) (by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · change f (gens 0) - (gens 0 • v - v) = 0
      rw [hv₁, sub_eq_zero]
      rfl
    · change f (gens 1) - (gens 1 • v - v) = 0
      rw [hv₂, sub_eq_zero]
      rfl)
  have : f = coboundaryA (muF2 n) v := sub_eq_zero.mp h0
  rw [this]
  exact ⟨v, rfl⟩

end Generic

theorem gens3_coe : (fun k => (gens3 k : Matrix (Fin 3) (Fin 3) (ZMod 2))) = mats3 := by
  funext k
  fin_cases k <;> rfl

@[expose] def gens4 : Fin 2 → SpecialLinearGroup (Fin 4) (ZMod 2) :=
  ![⟨mats4 0, by
      rw [show mats4 0 = transvection 0 1 1 by decide]
      exact det_transvection_of_ne _ _ (by decide) _⟩,
    ⟨mats4 1, by
      rw [show mats4 1 = Equiv.Perm.permMatrix (ZMod 2) (finRotate 4).symm by decide,
        det_permutation]
      exact sign_cast_eq_one _⟩]

theorem gens4_coe : (fun k => (gens4 k : Matrix (Fin 4) (Fin 4) (ZMod 2))) = mats4 := by
  funext k
  fin_cases k <;> rfl

@[expose] def gens5 : Fin 2 → SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ![⟨mats5 0, by
      rw [show mats5 0 = transvection 0 1 1 by decide]
      exact det_transvection_of_ne _ _ (by decide) _⟩,
    ⟨mats5 1, by
      rw [show mats5 1 = Equiv.Perm.permMatrix (ZMod 2) (finRotate 5).symm by decide,
        det_permutation]
      exact sign_cast_eq_one _⟩]

theorem gens5_coe : (fun k => (gens5 k : Matrix (Fin 5) (Fin 5) (ZMod 2))) = mats5 := by
  funext k
  fin_cases k <;> rfl


theorem tw4_spec : ∀ i j : Fin 4, i ≠ j → wordEvalM mats4 (tw4 i j) = transvection i j 1 :=
  Certificates.certificate17001.1

theorem rels4_spec : ∀ r ∈ rels4, wordEvalM mats4 r = 1 :=
  Certificates.certificate17001.2.1

theorem sol4 : ∀ v₁ v₂ : Fin 4 → ZMod 2, (∀ r ∈ rels4, foxEvalM mats4 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats4 0 *ᵥ v - v ∧ v₂ = mats4 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.1

theorem Z1A_eq_B1A_four : Z1A (muF2 4) = B1A (muF2 4) := by
  refine le_antisymm ?_ (B1A_le_Z1A _)
  refine Z1A_le_B1A_of_rels (gens := gens4) (tw := tw4) (rels := rels4) ?_ ?_ ?_
  · rw [gens4_coe]
    exact tw4_spec
  · rw [gens4_coe]
    exact rels4_spec
  · rw [gens4_coe]
    exact sol4

theorem tw5_spec : ∀ i j : Fin 5, i ≠ j → wordEvalM mats5 (tw5 i j) = transvection i j 1 :=
  Certificates.certificate17001.2.2.2.1

theorem rels5_spec : ∀ r ∈ rels5, wordEvalM mats5 r = 1 :=
  Certificates.certificate17001.2.2.2.2.1

theorem sol5_0 : ∀ v₁ ∈ chunk5_0, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.1

theorem sol5_1 : ∀ v₁ ∈ chunk5_1, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.2.1

theorem sol5_2 : ∀ v₁ ∈ chunk5_2, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.2.2.1

theorem sol5_3 : ∀ v₁ ∈ chunk5_3, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.1

theorem sol5_4 : ∀ v₁ ∈ chunk5_4, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.1

theorem sol5_5 : ∀ v₁ ∈ chunk5_5, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.1

theorem sol5_6 : ∀ v₁ ∈ chunk5_6, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.1

theorem sol5_7 : ∀ v₁ ∈ chunk5_7, ∀ v₂ : Fin 5 → ZMod 2,
    (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem mem_chunk5 : ∀ v : Fin 5 → ZMod 2,
    v ∈ chunk5_0 ∨ v ∈ chunk5_1 ∨ v ∈ chunk5_2 ∨ v ∈ chunk5_3 ∨ v ∈ chunk5_4 ∨ v ∈ chunk5_5 ∨
      v ∈ chunk5_6 ∨ v ∈ chunk5_7 := by
  decide

theorem sol5
    : ∀ v₁ v₂ : Fin 5 → ZMod 2, (∀ r ∈ rels5, foxEvalM mats5 ![v₁, v₂] r = 0) →
    ∃ v, v₁ = mats5 0 *ᵥ v - v ∧ v₂ = mats5 1 *ᵥ v - v := by
  intro v₁ v₂ h
  rcases mem_chunk5 v₁ with h0 | h0 | h0 | h0 | h0 | h0 | h0 | h0
  · exact sol5_0 v₁ h0 v₂ h
  · exact sol5_1 v₁ h0 v₂ h
  · exact sol5_2 v₁ h0 v₂ h
  · exact sol5_3 v₁ h0 v₂ h
  · exact sol5_4 v₁ h0 v₂ h
  · exact sol5_5 v₁ h0 v₂ h
  · exact sol5_6 v₁ h0 v₂ h
  · exact sol5_7 v₁ h0 v₂ h

theorem Z1A_eq_B1A_five : Z1A (muF2 5) = B1A (muF2 5) := by
  refine le_antisymm ?_ (B1A_le_Z1A _)
  refine Z1A_le_B1A_of_rels (gens := gens5) (tw := tw5) (rels := rels5) ?_ ?_ ?_
  · rw [gens5_coe]
    exact tw5_spec
  · rw [gens5_coe]
    exact rels5_spec
  · rw [gens5_coe]
    exact sol5

theorem cocycle3_one : cocycle3 1 = 0 :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cocycle3_gen0 : ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    cocycle3 (gens3 0 * g) = cocycle3 (gens3 0) + gens3 0 • cocycle3 g :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cocycle3_gen1 : ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    cocycle3 (gens3 1 * g) = cocycle3 (gens3 1) + gens3 1 • cocycle3 g :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cocycle3_not : ¬ ∃ v : Fin 3 → ZMod 2,
    cocycle3 (gens3 0) = mats3 0 *ᵥ v - v ∧ cocycle3 (gens3 1) = mats3 1 *ᵥ v - v :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem sol3 : ∀ v₁ v₂ : Fin 3 → ZMod 2, (∀ r ∈ rels3, foxEvalM mats3 ![v₁, v₂] r = 0) →
    (∃ v, v₁ = mats3 0 *ᵥ v - v ∧ v₂ = mats3 1 *ᵥ v - v) ∨
      ∃ v, v₁ = mats3 0 *ᵥ v - v + cocycle3 (gens3 0) ∧
        v₂ = mats3 1 *ᵥ v - v + cocycle3 (gens3 1) :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem tw3_spec : ∀ i j : Fin 3, i ≠ j → wordEvalM mats3 (tw3 i j) = transvection i j 1 :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem rels3_spec : ∀ r ∈ rels3, wordEvalM mats3 r = 1 :=
  Certificates.certificate17001.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Quasithin.JonesParshall
