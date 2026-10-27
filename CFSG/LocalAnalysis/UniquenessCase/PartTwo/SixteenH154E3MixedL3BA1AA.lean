module

public import CFSG.Quasithin.Background.JonesParshallSLn

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin CFSG.Quasithin.JonesParshall

private theorem s16h_tw3_spec : ∀ i j : Fin 3, i ≠ j →
    wordEvalM mats3 (tw3 i j) = transvection i j 1 := by
  decide +kernel

private theorem s16h_rels3_spec : ∀ r ∈ rels3, wordEvalM mats3 r = 1 := by
  decide +kernel

private theorem s16h_cocycle3_one : cocycle3 1 = 0 := by
  decide +kernel

private theorem s16h_cocycle3_gen0 : ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    cocycle3 (gens3 0 * g) = cocycle3 (gens3 0) + gens3 0 • cocycle3 g := by
  decide +kernel

private theorem s16h_cocycle3_gen1 : ∀ g : SpecialLinearGroup (Fin 3) (ZMod 2),
    cocycle3 (gens3 1 * g) = cocycle3 (gens3 1) + gens3 1 • cocycle3 g := by
  decide +kernel

private theorem s16h_cocycle3_not : ¬ ∃ v : Fin 3 → ZMod 2,
    cocycle3 (gens3 0) = mats3 0 *ᵥ v - v ∧ cocycle3 (gens3 1) = mats3 1 *ᵥ v - v := by
  decide +kernel

private theorem s16h_sol3 : ∀ v₁ v₂ : Fin 3 → ZMod 2,
    (∀ r ∈ rels3, foxEvalM mats3 ![v₁, v₂] r = 0) →
    (∃ v, v₁ = mats3 0 *ᵥ v - v ∧ v₂ = mats3 1 *ᵥ v - v) ∨
      ∃ v, v₁ = mats3 0 *ᵥ v - v + cocycle3 (gens3 0) ∧
        v₂ = mats3 1 *ᵥ v - v + cocycle3 (gens3 1) := by
  decide +kernel

private theorem s16h_closure_gens3 : Subgroup.closure (Set.range gens3) = ⊤ :=
  closure_range_eq_top (tw := tw3) (by rw [gens3_coe]; exact s16h_tw3_spec)

private theorem s16h_cocycle3_mem : cocycle3 ∈ Z1A (muF2 3) := by
  refine mem_Z1A_of_gens s16h_closure_gens3 s16h_cocycle3_one ?_
  rintro _ ⟨i, rfl⟩ g
  fin_cases i
  · exact s16h_cocycle3_gen0 g
  · exact s16h_cocycle3_gen1 g

private theorem s16h_cocycle3_not_mem : cocycle3 ∉ B1A (muF2 3) := by
  rintro ⟨v, hv⟩
  apply s16h_cocycle3_not
  refine ⟨v, ?_, ?_⟩
  · rw [← hv]
    rfl
  · rw [← hv]
    rfl

theorem s16h_l3_nat_Z1A_card :
    Nat.card (Z1A (muF2 3)) = 2 * Nat.card (B1A (muF2 3)) := by
  let Φ : ZMod 2 × B1A (muF2 3) → Z1A (muF2 3) := fun p =>
    ⟨p.1.val • cocycle3 + p.2.1,
      add_mem (AddSubgroup.nsmul_mem _ s16h_cocycle3_mem _) (B1A_le_Z1A _ p.2.2)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨c, b⟩ ⟨c', b'⟩ h
      have h' : c.val • cocycle3 + b.1 = c'.val • cocycle3 + b'.1 := by
        simpa [Φ] using congrArg Subtype.val h
      have hc : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
      have key : c = c' := by
        rcases hc c with rfl | rfl <;> rcases hc c' with rfl | rfl
        · rfl
        · exfalso
          apply s16h_cocycle3_not_mem
          have : cocycle3 = b.1 - b'.1 := by
            simp only [ZMod.val_zero, zero_smul, zero_add, ZMod.val_one, one_smul] at h'
            rw [h']
            abel
          rw [this]
          exact sub_mem b.2 b'.2
        · exfalso
          apply s16h_cocycle3_not_mem
          have : cocycle3 = b'.1 - b.1 := by
            simp only [ZMod.val_zero, zero_smul, zero_add, ZMod.val_one, one_smul] at h'
            rw [← h']
            abel
          rw [this]
          exact sub_mem b'.2 b.2
        · rfl
      subst key
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h'))
    · rintro ⟨f, hf⟩
      have hrel := rels_constraint (gens := gens3) (rels := rels3)
        (by rw [gens3_coe]; exact s16h_rels3_spec) hf
      rw [gens3_coe] at hrel
      rcases s16h_sol3 _ _ hrel with ⟨v, hv₀, hv₁⟩ | ⟨v, hv₀, hv₁⟩
      · refine ⟨(0, ⟨coboundaryA (muF2 3) v, ⟨v, rfl⟩⟩), Subtype.ext ?_⟩
        simp only [Φ, ZMod.val_zero, zero_smul, zero_add]
        exact (eq_of_agree s16h_closure_gens3 hf (B1A_le_Z1A _ ⟨v, rfl⟩) hv₀ hv₁).symm
      · refine ⟨(1, ⟨coboundaryA (muF2 3) v, ⟨v, rfl⟩⟩), Subtype.ext ?_⟩
        simp only [Φ, ZMod.val_one, one_smul]
        refine (eq_of_agree s16h_closure_gens3 hf
          (add_mem s16h_cocycle3_mem (B1A_le_Z1A _ ⟨v, rfl⟩)) ?_ ?_).symm
        · rw [hv₀, Pi.add_apply, add_comm]
          rfl
        · rw [hv₁, Pi.add_apply, add_comm]
          rfl
  rw [← Nat.card_congr (Equiv.ofBijective Φ hΦ), Nat.card_prod, Nat.card_zmod]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
