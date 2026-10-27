module

public import CFSG.LocalAnalysis.StandardType.GGTPDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTPTablePRow_A5 {n : ℕ} {X : LargeEvenLabel} (h3 : 3 ∣ 2 ^ n - 1)
    (hrow : GGTablePRow 3 ⟨.A, 5, n⟩ X) :
    X = ⟨.E6, 0, n⟩ ∨ X = ⟨.A, 6, n⟩ ∨ X = ⟨.C, 6, n⟩ ∨ X = ⟨.D, 6, n⟩ ∨ X = ⟨.twD, 7, n⟩ ∨
      (X.tag = .A ∧ (X.rank = 11 ∨ X.rank = 12) ∧ 2 * X.n = n ∧ 3 ∣ 2 ^ X.n + 1) := by
  unfold GGTablePRow at hrow
  simp at hrow
  rcases hrow with ⟨-, hX⟩ | ⟨hp, -⟩
  · rcases hX with h | h | h | h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · rw [h]; simp
    · right; right; right; right; right; exact h
  · have hp1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

theorem ggTPTablePRow_twA5 {n : ℕ} {X : LargeEvenLabel} (h3 : 3 ∣ 2 ^ n + 1)
    (hrow : GGTablePRow 3 ⟨.twA, 5, n⟩ X) :
    X = ⟨.twE6, 0, n⟩ ∨ X = ⟨.twA, 6, n⟩ ∨ X = ⟨.C, 6, n⟩ ∨ X = ⟨.D, 6, n⟩ ∨ X = ⟨.D, 7, n⟩ ∨
      (X.tag = .twE6 ∧ 3 * X.n = n) := by
  unfold GGTablePRow at hrow
  simp at hrow
  rcases hrow with ⟨hd, hX⟩ | ⟨-, hX⟩
  · have hp1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  · rcases hX with h | h | h | h | h | h | h | h
    · rw [h]; simp
    · rw [h]; simp
    · obtain ⟨-, h⟩ := h; rw [h]; simp
    · obtain ⟨-, h⟩ := h; rw [h]; simp
    · obtain ⟨he, -⟩ := h; exact absurd he (by decide)
    · obtain ⟨he, -⟩ := h; exact absurd he (by decide)
    · rw [h]; simp
    · right; right; right; right; right; exact h

theorem ggTPLabelIso_jLabel {lab₁ lab₂ : LargeEvenLabel} (h : GGLabelIso (ggTPJLabel lab₁) lab₂) :
    ggTPJLabel lab₁ = lab₂ := by
  unfold ggTPJLabel at *
  by_cases hE : lab₁.tag = LargeEvenLieTag.E6
  · rw [if_pos hE] at h ⊢
    unfold GGLabelIso at h
    rcases h with h | h | h | h | h | h | h | h
    · exact h
    · rcases h with ⟨ht, -⟩; simp at ht
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨-, h1⟩; simp at h1
  · rw [if_neg hE] at h ⊢
    unfold GGLabelIso at h
    rcases h with h | h | h | h | h | h | h | h
    · exact h
    · rcases h with ⟨ht, -⟩; simp at ht
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨h1, -⟩; simp at h1
    · rcases h with ⟨-, h1⟩; simp at h1

end CFSG.StandardType

end
