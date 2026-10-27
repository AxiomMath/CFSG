module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e7Filter
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bLink

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3e7_idx : Option (Fin (Tag.rank Tag.E7)) → ℕ
  | none => 0
  | some j => j.val + 1

@[expose] def levTwoS3e7_maskOf (D : Finset (Option (Fin (Tag.rank Tag.E7)))) : ℕ :=
  ∑ x ∈ D, 2 ^ levTwoS3e7_idx x

@[expose] def levTwoS3e7_dOfMask (m : ℕ) : Finset (Option (Fin (Tag.rank Tag.E7))) :=
  (Finset.univ : Finset (Option (Fin (Tag.rank Tag.E7)))).filter
    (fun x => m.testBit (levTwoS3e7_idx x) = true)

@[expose] def levTwoS3e7_allNodes : List (Option (Fin (Tag.rank Tag.E7))) :=
  none :: (List.finRange (Tag.rank Tag.E7)).map (fun j => some j)

abbrev levTwoS3e7_fin2 (m : ℕ) (β : Fin (Tag.rank Tag.E7) → ℤ) : Prop :=
  ∃ e : Fin 2, ∃ s : Fin 2,
    (e.val = 0 ∨ m.testBit 0 = true) ∧
    (∀ j : Fin (Tag.rank Tag.E7), 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * β j +
      (e.val : ℤ) * levTwoS3e7_theta.getD j.val 0) ∧
    (∀ j : Fin (Tag.rank Tag.E7), (if s.val = 0 then (1 : ℤ) else -1) * β j +
      (e.val : ℤ) * levTwoS3e7_theta.getD j.val 0 ≠ 0 → m.testBit (j.val + 1) = true)

@[expose] def levTwoS3e7_fin2B (m : ℕ) (β : Fin (Tag.rank Tag.E7) → ℤ) : Bool :=
  decide (levTwoS3e7_fin2 m β)

theorem levTwoS3e7_allD_mem (D : Finset (Option (Fin (Tag.rank Tag.E7)))) :
    D ∈ (List.range 256).map levTwoS3e7_dOfMask := by
  have h : ∀ D : Finset (Option (Fin (Tag.rank Tag.E7))),
      D ∈ (List.range 256).map levTwoS3e7_dOfMask := by
    decide +kernel
  exact h D

theorem levTwoS3e7_maskOf_testBit_check :
    ((List.range 256).map levTwoS3e7_dOfMask).all (fun D =>
      levTwoS3e7_allNodes.all (fun x =>
        decide ((levTwoS3e7_maskOf D).testBit (levTwoS3e7_idx x) = true ↔ x ∈ D))) = true := by
  decide +kernel

theorem levTwoS3e7_maskOf_testBit (D : Finset (Option (Fin (Tag.rank Tag.E7))))
    (x : Option (Fin (Tag.rank Tag.E7))) :
    (levTwoS3e7_maskOf D).testBit (levTwoS3e7_idx x) = true ↔ x ∈ D := by
  obtain ⟨m, hm, hD⟩ := List.mem_map.mp (levTwoS3e7_allD_mem D)
  rw [← hD]
  have h1 := List.all_eq_true.mp levTwoS3e7_maskOf_testBit_check (levTwoS3e7_dOfMask m)
    (List.mem_map.mpr ⟨m, hm, rfl⟩)
  have h2 := List.all_eq_true.mp h1 x (by
    cases x with
    | none => simp [levTwoS3e7_allNodes]
    | some j => simp [levTwoS3e7_allNodes, List.mem_finRange])
  exact of_decide_eq_true h2

theorem levTwoS3e7_maskOf_testBit_none (D : Finset (Option (Fin (Tag.rank Tag.E7)))) :
    (levTwoS3e7_maskOf D).testBit 0 = true ↔ (none : Option (Fin (Tag.rank Tag.E7))) ∈ D := by
  simpa [levTwoS3e7_idx] using levTwoS3e7_maskOf_testBit D none

theorem levTwoS3e7_maskOf_testBit_some (D : Finset (Option (Fin (Tag.rank Tag.E7))))
    (j : Fin (Tag.rank Tag.E7)) :
    (levTwoS3e7_maskOf D).testBit (j.val + 1) = true ↔
      (some j : Option (Fin (Tag.rank Tag.E7))) ∈ D := by
  simpa [levTwoS3e7_idx] using levTwoS3e7_maskOf_testBit D (some j)

theorem levTwoS3e7_card_eq_pop_check :
    ((List.range 256).map levTwoS3e7_dOfMask).all (fun D =>
      decide (levTwoS3e7_maskPop (levTwoS3e7_maskOf D) = D.card)) = true := by
  decide +kernel

theorem levTwoS3e7_card_eq_pop (D : Finset (Option (Fin (Tag.rank Tag.E7)))) :
    levTwoS3e7_maskPop (levTwoS3e7_maskOf D) = D.card := by
  obtain ⟨m, hm, hD⟩ := List.mem_map.mp (levTwoS3e7_allD_mem D)
  rw [← hD]
  have h1 := List.all_eq_true.mp levTwoS3e7_card_eq_pop_check (levTwoS3e7_dOfMask m)
    (List.mem_map.mpr ⟨m, hm, rfl⟩)
  exact of_decide_eq_true h1

theorem levTwoS3e7_inPat_fin2B_check_lo :
    (List.range 128).all (fun m => levTwoS3e7_roots.all (fun β =>
      levTwoS3e7_inPat m β == levTwoS3e7_fin2B m (levTwoS3e7_vec (Tag.rank Tag.E7) β))) = true := by
  decide +kernel

theorem levTwoS3e7_inPat_fin2B_check_hi :
    (List.range 128).all (fun i => levTwoS3e7_roots.all (fun β =>
      levTwoS3e7_inPat (i + 128) β == levTwoS3e7_fin2B (i + 128)
        (levTwoS3e7_vec (Tag.rank Tag.E7) β))) = true := by
  decide +kernel

theorem levTwoS3e7_inPat_eq_fin2B {m : ℕ} (hm : m < 256) {β : List ℤ}
    (hβ : β ∈ levTwoS3e7_roots) :
    levTwoS3e7_inPat m β = levTwoS3e7_fin2B m (levTwoS3e7_vec (Tag.rank Tag.E7) β) := by
  rcases lt_or_ge m 128 with h | h
  · have h1 := List.all_eq_true.mp levTwoS3e7_inPat_fin2B_check_lo m (List.mem_range.mpr h)
    exact beq_iff_eq.mp (List.all_eq_true.mp h1 β hβ)
  · have h1 := List.all_eq_true.mp levTwoS3e7_inPat_fin2B_check_hi (m - 128)
      (List.mem_range.mpr (by omega))
    have h2 := List.all_eq_true.mp h1 β hβ
    have hm' : m - 128 + 128 = m := by omega
    simpa [hm'] using beq_iff_eq.mp h2

theorem levTwoS3e7_maskOf_lt :
    ∀ D : Finset (Option (Fin (Tag.rank Tag.E7))), levTwoS3e7_maskOf D < 256 := by
  decide +kernel

theorem levTwoS3e7_maskOf_lt_of_ne_univ :
    ∀ D : Finset (Option (Fin (Tag.rank Tag.E7))), D ≠ Finset.univ → levTwoS3e7_maskOf D < 255 := by
  decide +kernel

end CFSG.StandardType.LevTwo
