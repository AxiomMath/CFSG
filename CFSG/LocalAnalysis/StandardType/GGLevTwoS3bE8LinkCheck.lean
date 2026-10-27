module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bMeasure
public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3bE8LinkCheckBool
public import CFSG.Mathlib.Decide.Bounded

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley
open scoped Matrix

@[expose] def levTwoS3b_e8_nodeIdx : Option (Fin (Tag.rank Tag.E8)) → ℕ
  | none => 0
  | some j => j.val + 1

@[expose] def levTwoS3b_e8_maskOf (D : Finset (Option (Fin (Tag.rank Tag.E8)))) : ℕ :=
  ∑ x ∈ D, 2 ^ levTwoS3b_e8_nodeIdx x

@[expose] def levTwoS3b_e8ThetaVec : Fin (Tag.rank Tag.E8) → ℤ := ![2, 3, 4, 6, 5, 4, 3, 2]

@[expose] def levTwoS3b_e8_block (k : ℕ) : Finset (Finset (Option (Fin (Tag.rank Tag.E8)))) :=
  Finset.univ.filter (fun D => levTwoS3b_e8_maskOf D / 64 = k)

@[expose] def levTwoS3b_e8_linkBlock (k : Fin 8) : Prop :=
    ∀ D ∈ levTwoS3b_e8_block k.val, D ≠ Finset.univ →
      ∀ l ∈ Tag.E8.artifactRoots,
      (∃ e : Fin 2, ∃ s : Fin 2,
        (e.val = 0 ∨ (none : Option (Fin (Tag.rank Tag.E8))) ∈ D) ∧
        (∀ j, 0 ≤ (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
          (e.val : ℤ) * levTwoS3b_e8ThetaVec j) ∧
        (∀ j, (if s.val = 0 then (1 : ℤ) else -1) * l.getD j.val 0 +
          (e.val : ℤ) * levTwoS3b_e8ThetaVec j ≠ 0 →
            (some j : Option (Fin (Tag.rank Tag.E8))) ∈ D)) ↔
      levTwoS3b_inPat (levTwoS3b_e8_maskOf D) l = true

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_linkBlock_0 : levTwoS3b_e8_linkBlock 0 := fun D hD =>
  levTwoS3bK_e8_block_sound levTwoS3b_e8_nodeIdx rfl (fun _ => rfl) levTwoS3b_e8ThetaVec
    (by decide) 0 levTwoS3bK_e8_chk_0 D (Finset.mem_filter.1 hD).2

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_linkBlock_1 : levTwoS3b_e8_linkBlock 1 := fun D hD =>
  levTwoS3bK_e8_block_sound levTwoS3b_e8_nodeIdx rfl (fun _ => rfl) levTwoS3b_e8ThetaVec
    (by decide) 1 levTwoS3bK_e8_chk_1 D (Finset.mem_filter.1 hD).2

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_linkBlock_2 : levTwoS3b_e8_linkBlock 2 := fun D hD =>
  levTwoS3bK_e8_block_sound levTwoS3b_e8_nodeIdx rfl (fun _ => rfl) levTwoS3b_e8ThetaVec
    (by decide) 2 levTwoS3bK_e8_chk_2 D (Finset.mem_filter.1 hD).2

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_linkBlock_3 : levTwoS3b_e8_linkBlock 3 := fun D hD =>
  levTwoS3bK_e8_block_sound levTwoS3b_e8_nodeIdx rfl (fun _ => rfl) levTwoS3b_e8ThetaVec
    (by decide) 3 levTwoS3bK_e8_chk_3 D (Finset.mem_filter.1 hD).2

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_linkBlock_4 : levTwoS3b_e8_linkBlock 4 := fun D hD =>
  levTwoS3bK_e8_block_sound levTwoS3b_e8_nodeIdx rfl (fun _ => rfl) levTwoS3b_e8ThetaVec
    (by decide) 4 levTwoS3bK_e8_chk_4 D (Finset.mem_filter.1 hD).2

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_linkBlock_5 : levTwoS3b_e8_linkBlock 5 := fun D hD =>
  levTwoS3bK_e8_block_sound levTwoS3b_e8_nodeIdx rfl (fun _ => rfl) levTwoS3b_e8ThetaVec
    (by decide) 5 levTwoS3bK_e8_chk_5 D (Finset.mem_filter.1 hD).2

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_linkBlock_6 : levTwoS3b_e8_linkBlock 6 := fun D hD =>
  levTwoS3bK_e8_block_sound levTwoS3b_e8_nodeIdx rfl (fun _ => rfl) levTwoS3b_e8ThetaVec
    (by decide) 6 levTwoS3bK_e8_chk_6 D (Finset.mem_filter.1 hD).2

open scoped CFSG.Decide.Bounded in
theorem levTwoS3b_e8_linkBlock_7 : levTwoS3b_e8_linkBlock 7 := fun D hD =>
  levTwoS3bK_e8_block_sound levTwoS3b_e8_nodeIdx rfl (fun _ => rfl) levTwoS3b_e8ThetaVec
    (by decide) 7 levTwoS3bK_e8_chk_7 D (Finset.mem_filter.1 hD).2

theorem levTwoS3b_e8_linkBlock_all : ∀ k : Fin 8, levTwoS3b_e8_linkBlock k := by
  intro k
  fin_cases k
  exact levTwoS3b_e8_linkBlock_0
  exact levTwoS3b_e8_linkBlock_1
  exact levTwoS3b_e8_linkBlock_2
  exact levTwoS3b_e8_linkBlock_3
  exact levTwoS3b_e8_linkBlock_4
  exact levTwoS3b_e8_linkBlock_5
  exact levTwoS3b_e8_linkBlock_6
  exact levTwoS3b_e8_linkBlock_7

end CFSG.StandardType.LevTwo
