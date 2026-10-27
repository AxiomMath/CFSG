module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e6Filter
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bLink

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3e6_idx : Option (Fin (Tag.rank Tag.E6)) → ℕ
  | none => 0
  | some j => j.val + 1

@[expose] def levTwoS3e6_maskOf (D : Finset (Option (Fin (Tag.rank Tag.E6)))) : ℕ :=
  ∑ x ∈ D, 2 ^ levTwoS3e6_idx x

@[expose] def levTwoS3e6_dOfMask (m : ℕ) : Finset (Option (Fin (Tag.rank Tag.E6))) :=
  (Finset.univ : Finset (Option (Fin (Tag.rank Tag.E6)))).filter (fun x => m.testBit (levTwoS3e6_idx x) = true)

@[expose] def levTwoS3e6_allNodes : List (Option (Fin (Tag.rank Tag.E6))) :=
  none :: (List.finRange (Tag.rank Tag.E6)).map (fun j => some j)

abbrev levTwoS3e6_fin2 (m : ℕ) (β : Fin (Tag.rank Tag.E6) → ℤ) : Prop :=
  ∃ e : Fin 2, ∃ s : Fin 2,
    (e.val = 0 ∨ m.testBit 0 = true) ∧
    (∀ j : Fin (Tag.rank Tag.E6), 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * β j +
      (e.val : ℤ) * levTwoS3e6_theta.getD j.val 0) ∧
    (∀ j : Fin (Tag.rank Tag.E6), (if s.val = 0 then (1 : ℤ) else -1) * β j +
      (e.val : ℤ) * levTwoS3e6_theta.getD j.val 0 ≠ 0 → m.testBit (j.val + 1) = true)

@[expose] def levTwoS3e6_fin2B (m : ℕ) (β : Fin (Tag.rank Tag.E6) → ℤ) : Bool :=
  decide (levTwoS3e6_fin2 m β)

theorem levTwoS3e6_allD_mem (D : Finset (Option (Fin (Tag.rank Tag.E6)))) :
    D ∈ (List.range 128).map levTwoS3e6_dOfMask := by
  have h : ∀ D : Finset (Option (Fin (Tag.rank Tag.E6))), D ∈ (List.range 128).map levTwoS3e6_dOfMask := by
    decide +kernel
  exact h D

theorem levTwoS3e6_maskOf_testBit_check :
    ((List.range 128).map levTwoS3e6_dOfMask).all (fun D =>
      levTwoS3e6_allNodes.all (fun x =>
        decide ((levTwoS3e6_maskOf D).testBit (levTwoS3e6_idx x) = true ↔ x ∈ D))) = true := by
  decide +kernel

theorem levTwoS3e6_maskOf_testBit (D : Finset (Option (Fin (Tag.rank Tag.E6)))) (x : Option (Fin (Tag.rank Tag.E6))) :
    (levTwoS3e6_maskOf D).testBit (levTwoS3e6_idx x) = true ↔ x ∈ D := by
  obtain ⟨m, hm, hD⟩ := List.mem_map.mp (levTwoS3e6_allD_mem D)
  rw [← hD]
  have h1 := List.all_eq_true.mp levTwoS3e6_maskOf_testBit_check (levTwoS3e6_dOfMask m)
    (List.mem_map.mpr ⟨m, hm, rfl⟩)
  have h2 := List.all_eq_true.mp h1 x (by
    cases x with
    | none => simp [levTwoS3e6_allNodes]
    | some j => simp [levTwoS3e6_allNodes, List.mem_finRange])
  exact of_decide_eq_true h2

theorem levTwoS3e6_maskOf_testBit_none (D : Finset (Option (Fin (Tag.rank Tag.E6)))) :
    (levTwoS3e6_maskOf D).testBit 0 = true ↔ (none : Option (Fin (Tag.rank Tag.E6))) ∈ D := by
  simpa [levTwoS3e6_idx] using levTwoS3e6_maskOf_testBit D none

theorem levTwoS3e6_maskOf_testBit_some (D : Finset (Option (Fin (Tag.rank Tag.E6)))) (j : Fin (Tag.rank Tag.E6)) :
    (levTwoS3e6_maskOf D).testBit (j.val + 1) = true ↔ (some j : Option (Fin (Tag.rank Tag.E6))) ∈ D := by
  simpa [levTwoS3e6_idx] using levTwoS3e6_maskOf_testBit D (some j)

theorem levTwoS3e6_card_eq_pop_check :
    ((List.range 128).map levTwoS3e6_dOfMask).all (fun D =>
      decide (levTwoS3e6_maskPop (levTwoS3e6_maskOf D) = D.card)) = true := by
  decide +kernel

theorem levTwoS3e6_card_eq_pop (D : Finset (Option (Fin (Tag.rank Tag.E6)))) :
    levTwoS3e6_maskPop (levTwoS3e6_maskOf D) = D.card := by
  obtain ⟨m, hm, hD⟩ := List.mem_map.mp (levTwoS3e6_allD_mem D)
  rw [← hD]
  have h1 := List.all_eq_true.mp levTwoS3e6_card_eq_pop_check (levTwoS3e6_dOfMask m)
    (List.mem_map.mpr ⟨m, hm, rfl⟩)
  exact of_decide_eq_true h1

theorem levTwoS3e6_inPat_fin2B_check :
    (List.range 128).all (fun m => levTwoS3e6_roots.all (fun β =>
      levTwoS3e6_inPat m β == levTwoS3e6_fin2B m (levTwoS3e6_vec 6 β))) = true := by
  decide +kernel

theorem levTwoS3e6_inPat_eq_fin2B {m : ℕ} (hm : m < 128) {β : List ℤ}
    (hβ : β ∈ levTwoS3e6_roots) :
    levTwoS3e6_inPat m β = levTwoS3e6_fin2B m (levTwoS3e6_vec (Tag.rank Tag.E6) β) := by
  have h1 := List.all_eq_true.mp levTwoS3e6_inPat_fin2B_check m (List.mem_range.mpr hm)
  have h2 := List.all_eq_true.mp h1 β hβ
  exact beq_iff_eq.mp h2


theorem levTwoS3e6_maskOf_lt : ∀ D : Finset (Option (Fin (Tag.rank Tag.E6))), levTwoS3e6_maskOf D < 128 := by
  decide +kernel

theorem levTwoS3e6_maskOf_lt_of_ne_univ :
    ∀ D : Finset (Option (Fin (Tag.rank Tag.E6))), D ≠ Finset.univ → levTwoS3e6_maskOf D < 127 := by
  decide +kernel

end CFSG.StandardType.LevTwo
