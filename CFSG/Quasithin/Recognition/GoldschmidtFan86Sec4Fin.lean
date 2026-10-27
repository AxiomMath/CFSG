module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Defs

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} (T : Track Γ G)

theorem Track.rev_line_vert (i : ℤ) : T.rev.line.vert i = T.line.vert (-i) := rfl

theorem Track.rev_subFixer (a b : ℤ) : T.rev.subFixer a b = T.subFixer (-b) (-a) := by
  ext g
  rw [T.rev.mem_subFixer, T.mem_subFixer]
  constructor
  · intro h i h1 h2
    have := h (-i) (by omega) (by omega)
    rwa [Track.rev_line_vert, neg_neg] at this
  · intro h i h1 h2
    rw [Track.rev_line_vert]
    exact h (-i) (by omega) (by omega)

theorem Track.rev_fixer : T.rev.fixer = T.fixer := by
  ext g
  rw [T.rev.mem_fixer, T.mem_fixer]
  constructor
  · intro h i
    have := h (-i)
    rwa [Track.rev_line_vert, neg_neg] at this
  · intro h i
    rw [Track.rev_line_vert]
    exact h (-i)

theorem Track.exists_moved (F : FanTree Γ G) {a₀ : ℤ} {g : G} (hg : g ∉ T.fixer) :
    ∃ k : ℤ, a₀ ≤ k ∧ g • T.line.vert k ≠ T.line.vert k := by
  by_contra hcon
  push Not at hcon
  exact hg ((T.mem_fixer).2 fun i => halfStab_fixes_all F.loc_finite T (a := a₀) (g := g) hcon i)

theorem Track.exists_bound_right (F : FanTree Γ G) (a₀ : ℤ) :
    ∃ B : ℤ, a₀ ≤ B ∧ ∀ b : ℤ, B ≤ b → T.subFixer a₀ b ≤ T.fixer := by
  classical
  have := F.loc_finite (T.line.vert a₀)
  let kf : ↥(MulAction.stabilizer G (T.line.vert a₀)) → ℤ := fun g =>
    if h : g.1 ∈ T.fixer then a₀
    else Classical.choose (T.exists_moved F (a₀ := a₀) h)
  obtain ⟨M, hM⟩ := Finite.exists_le kf
  refine ⟨max M a₀, le_max_right _ _, fun b hb g hg => ?_⟩
  by_contra hgT
  have hgs : g ∈ MulAction.stabilizer G (T.line.vert a₀) :=
    MulAction.mem_stabilizer_iff.2
      ((T.mem_subFixer).1 hg a₀ le_rfl (le_trans (le_max_right _ _) hb))
  have hk := Classical.choose_spec (T.exists_moved F (a₀ := a₀) hgT)
  have hkf : kf ⟨g, hgs⟩ = Classical.choose (T.exists_moved F (a₀ := a₀) hgT) := by
    simp [kf, hgT]
  have hle := hM ⟨g, hgs⟩
  rw [hkf] at hle
  exact hk.2 ((T.mem_subFixer).1 hg _ hk.1 (le_trans hle (le_trans (le_max_left _ _) hb)))

theorem Track.exists_bound_left (F : FanTree Γ G) (b₀ : ℤ) :
    ∃ A : ℤ, A ≤ b₀ ∧ ∀ a : ℤ, a ≤ A → T.subFixer a b₀ ≤ T.fixer := by
  obtain ⟨B, hB0, hB⟩ := T.rev.exists_bound_right F (-b₀)
  refine ⟨-B, by omega, fun a ha => ?_⟩
  have := hB (-a) (by omega)
  rwa [Track.rev_subFixer, Track.rev_fixer, neg_neg, neg_neg] at this

theorem Track.exists_pseg_max (F : FanTree Γ G) {a₀ b₀ : ℤ} (h : PSeg T a₀ b₀) :
    ∃ a b : ℤ, a ≤ a₀ ∧ b₀ ≤ b ∧ PSeg T a b ∧
      ∀ a' b' : ℤ, a' ≤ a → b ≤ b' → PSeg T a' b' → a' = a ∧ b' = b := by
  obtain ⟨B, hB0, hB⟩ := T.exists_bound_right F a₀
  obtain ⟨A, hA0, hA⟩ := T.exists_bound_left F b₀
  have hbd : ∀ a b : ℤ, a ≤ a₀ → b₀ ≤ b → PSeg T a b → A < a ∧ b < B := by
    intro a b ha hb hp
    constructor
    · by_contra hc
      push Not at hc
      exact hp.2 ((omega1_le _).trans
        ((T.subFixer_anti (a := a) (b := b₀) (a' := a) (b' := b) le_rfl hb).trans (hA a hc)))
    · by_contra hc
      push Not at hc
      exact hp.2 ((omega1_le _).trans
        ((T.subFixer_anti (a := a₀) (b := b) (a' := a) (b' := b) ha le_rfl).trans (hB b hc)))
  by_contra hcon
  push Not at hcon
  have chain : ∀ n : ℕ, ∃ a b : ℤ, a ≤ a₀ ∧ b₀ ≤ b ∧ PSeg T a b ∧ (b₀ - a₀) + n ≤ b - a := by
    intro n
    induction n with
    | zero => exact ⟨a₀, b₀, le_rfl, le_rfl, h, by omega⟩
    | succ n ih =>
      obtain ⟨a, b, ha, hb, hp, hlen⟩ := ih
      obtain ⟨a', b', ha', hb', hp', hne⟩ := hcon a b ha hb hp
      refine ⟨a', b', by omega, by omega, hp', ?_⟩
      by_cases h1 : a' = a
      · have := hne h1
        push_cast
        omega
      · push_cast
        omega
  obtain ⟨a, b, ha, hb, hp, hlen⟩ := chain ((B - A).toNat + 1)
  have := hbd a b ha hb hp
  have h0 := h.1
  omega

end CFSG.Quasithin.Fan86
