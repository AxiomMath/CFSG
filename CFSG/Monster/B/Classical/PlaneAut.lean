module

public import CFSG.Monster.B.Classical.PlaneIncidence
import all CFSG.Fischer.F4
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Bool

public section

namespace CFSG.Monster.B.Classical.Plane

open CFSG.Fischer

@[expose] def IsFrame (f : Fin 21 × Fin 21 × Fin 21 × Fin 21) : Prop :=
  ¬Collinear3 f.1 f.2.1 f.2.2.1 ∧ ¬Collinear3 f.1 f.2.1 f.2.2.2 ∧
    ¬Collinear3 f.1 f.2.2.1 f.2.2.2 ∧ ¬Collinear3 f.2.1 f.2.2.1 f.2.2.2

@[expose] def frameB (f : Fin 21 × Fin 21 × Fin 21 × Fin 21) : Bool :=
  !colB f.1 f.2.1 f.2.2.1 && !colB f.1 f.2.1 f.2.2.2 && !colB f.1 f.2.2.1 f.2.2.2 &&
    !colB f.2.1 f.2.2.1 f.2.2.2

theorem frameB_iff (f : Fin 21 × Fin 21 × Fin 21 × Fin 21) : frameB f = true ↔ IsFrame f := by
  simp only [frameB, IsFrame, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, colB_iff,
    and_assoc]

instance : DecidablePred IsFrame := fun f => decidable_of_iff _ (frameB_iff f)

@[expose] def frameCount : ℕ :=
  ∑ a : Fin 21, ∑ b : Fin 21, ∑ c : Fin 21,
    if colB a b c then 0 else ∑ d : Fin 21, if colB a b d || colB a c d || colB b c d then 0 else 1

set_option maxHeartbeats 4000000 in
theorem frameCount_eq : frameCount = 60480 := by
  decide +kernel

theorem card_frames : (Finset.univ.filter IsFrame).card = 60480 := by
  rw [← frameCount_eq, Finset.card_filter, Fintype.sum_prod_type, frameCount]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases habc : colB a b c = true
  · rw [ite_eq_left habc]
    refine Finset.sum_eq_zero fun d _ => ite_eq_right fun h => ?_
    rw [← frameB_iff] at h
    simp [frameB, habc] at h
  · rw [ite_eq_right habc]
    refine Finset.sum_congr rfl fun d _ => ?_
    have : IsFrame (a, b, c, d) ↔ ¬(colB a b d || colB a c d || colB b c d) = true := by
      rw [← frameB_iff]
      simp only [Bool.not_eq_true] at habc
      simp [frameB, habc]
    by_cases h : (colB a b d || colB a c d || colB b c d) = true
    · rw [ite_eq_left h, ite_eq_right (by rwa [this, not_not])]
    · rw [ite_eq_right h, ite_eq_left (this.2 h)]

variable {σ : Equiv.Perm (Fin 21)}

theorem isFrame_map (hσ : σ ∈ lineAut) {a b c d : Fin 21} :
    IsFrame (σ a, σ b, σ c, σ d) ↔ IsFrame (a, b, c, d) := by
  simp only [IsFrame, collinear3_map_iff hσ]

theorem isFrame_base : IsFrame (5, 1, 0, 10) := by
  rw [← frameB_iff]
  decide +kernel

theorem apply_thirteen_of_fix (hσ : σ ∈ lineAut) (h5 : σ 5 = 5) (h1 : σ 1 = 1) (h0 : σ 0 = 0)
    (h10 : σ 10 = 10) : σ 13 = 13 ∨ σ 13 = 17 := by
  have hL0 : (projLine (join 5 1)).map σ.toEmbedding = projLine (join 5 1) :=
    map_projLine_join_of_fix hσ (by decide) h5 h1
  have hL9 : (projLine (join 0 10)).map σ.toEmbedding = projLine (join 0 10) :=
    map_projLine_join_of_fix hσ (by decide) h0 h10
  have h9 : σ (meet (join 5 1) (join 0 10)) = meet (join 5 1) (join 0 10) :=
    apply_meet_of_fix (by decide +kernel) hL0 hL9
  have hm : meet (join 5 1) (join 0 10) = 9 := by decide +kernel
  rw [hm] at h9
  have h13 : σ 13 ∈ projLine (join 5 1) := by
    rw [← hL0]
    exact Finset.mem_map_of_mem _ (by rw [mem_projLine]; decide +kernel)
  rw [mem_projLine] at h13
  have hne5 : σ 13 ≠ 5 := fun h => absurd (σ.injective (h.trans h5.symm)) (by decide)
  have hne1 : σ 13 ≠ 1 := fun h => absurd (σ.injective (h.trans h1.symm)) (by decide)
  have hne9 : σ 13 ≠ 9 := fun h => absurd (σ.injective (h.trans h9.symm)) (by decide)
  generalize σ 13 = x at h13 hne5 hne1 hne9
  revert x
  decide +kernel

theorem card_lineAut_le : Nat.card lineAut ≤ 120960 := by
  set f₀ : Fin 21 × Fin 21 × Fin 21 × Fin 21 := (5, 1, 0, 10)
  have hsmul : ∀ g : lineAut, g • f₀ = ((g : Equiv.Perm (Fin 21)) 5,
      (g : Equiv.Perm (Fin 21)) 1, (g : Equiv.Perm (Fin 21)) 0,
      (g : Equiv.Perm (Fin 21)) 10) := fun g => rfl
  have horb : Nat.card (MulAction.orbit lineAut f₀) ≤ 60480 := by
    rw [← card_frames, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, ?_⟩) ?_
    · obtain ⟨g, hg⟩ := x.2
      rw [← hg]
      change IsFrame (g • f₀)
      rw [hsmul]
      exact (isFrame_map g.2).2 isFrame_base
    · intro x y h
      have h' := congrArg Subtype.val h
      exact Subtype.ext h'
  have hstab : Nat.card (MulAction.stabilizer lineAut f₀) ≤ 2 := by
    have hfix : ∀ g : MulAction.stabilizer lineAut f₀,
        g.1.1 5 = 5 ∧ g.1.1 1 = 1 ∧ g.1.1 0 = 0 ∧ g.1.1 10 = 10 := by
      intro g
      have := (MulAction.mem_stabilizer_iff.1 g.2)
      rw [hsmul] at this
      simp only [f₀, Prod.mk.injEq] at this
      exact this
    let φ : MulAction.stabilizer lineAut f₀ → {x : Fin 21 // x = 13 ∨ x = 17} := fun g =>
      ⟨g.1.1 13, by
        obtain ⟨h5, h1, h0, h10⟩ := hfix g
        exact apply_thirteen_of_fix g.1.2 h5 h1 h0 h10⟩
    have hφ : Function.Injective φ := by
      intro g h hgh
      have h13 : g.1.1 13 = h.1.1 13 := congrArg Subtype.val hgh
      obtain ⟨g5, g1, g0, g10⟩ := hfix g
      obtain ⟨h5, h1, h0, h10⟩ := hfix h
      set a : Equiv.Perm (Fin 21) := g.1.1
      set b : Equiv.Perm (Fin 21) := h.1.1
      have hmem : b⁻¹ * a ∈ lineAut := mul_mem (inv_mem h.1.2) g.1.2
      have key : b⁻¹ * a = 1 := by
        refine eq_one_of_fix_five hmem ?_ ?_ ?_ ?_ ?_ <;>
          simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_eq_iff_eq]
        · rw [g5, h5]
        · rw [g1, h1]
        · rw [g0, h0]
        · rw [g10, h10]
        · exact h13
      have hab : a = b := by
        have := congrArg (b * ·) key
        simpa [mul_inv_cancel_left] using this
      exact Subtype.ext (Subtype.ext hab)
    have := Nat.card_le_card_of_injective φ hφ
    have h2 : Nat.card {x : Fin 21 // x = 13 ∨ x = 17} = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide
    omega
  have hcard := Subgroup.card_mul_index (MulAction.stabilizer lineAut f₀)
  rw [MulAction.index_stabilizer] at hcard
  rw [← hcard]
  calc Nat.card (MulAction.stabilizer lineAut f₀) * Nat.card (MulAction.orbit lineAut f₀)
      ≤ 2 * 60480 := Nat.mul_le_mul hstab horb
    _ = 120960 := by norm_num

end CFSG.Monster.B.Classical.Plane
