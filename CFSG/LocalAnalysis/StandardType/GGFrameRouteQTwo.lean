module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.Marking

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Open CFSG.Assembly

@[expose] def ggFrameQTwo_QTwoCompat (lab : LargeEvenLabel) : Prop :=
  lab.n = 1 ∨ (lab.tag = .A ∧ lab.rank = 1 ∧ lab.n = 2)

theorem ggFrameQTwo_exists_hasLabel {X : Type} [Group X] {P : LargeEvenLabel → Prop}
    (h : LargeEvenMarking X (fun lab _ _ _ _ _ => P lab)) :
    ∃ lab, LargeEvenInLambda2 lab ∧ P lab ∧ GGHasLabel lab (X ⧸ Subgroup.center X) := by
  obtain ⟨-, lab, hl, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, -, hP⟩ := largeEvenRawDatum_exists hraw
  exact ⟨lab, hl, hP, largeEvenRawDatum_mono (fun _ _ _ _ ⟨_, _, θ, _⟩ => ⟨θ⟩) hraw⟩

theorem ggFrameQTwo_qTwoCompat_of_iso {lab₁ lab₂ : LargeEvenLabel} (hn : lab₁.n = 1)
    (h : GGLabelIso lab₁ lab₂) : ggFrameQTwo_QTwoCompat lab₂ := by
  obtain ⟨t₁, r₁, n₁⟩ := lab₁
  obtain ⟨t₂, r₂, n₂⟩ := lab₂
  dsimp only at hn
  subst hn
  unfold GGLabelIso at h
  unfold ggFrameQTwo_QTwoCompat
  dsimp only
  rcases h with h | ⟨-, -, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨h, h'⟩
  all_goals simp only [LargeEvenLabel.mk.injEq] at h
  · exact Or.inl h.2.2.symm
  · exact Or.inl h.symm
  · exact Or.inl h.2.2
  · exact Or.inl h.2.2
  · exact Or.inl h.2.2
  · exact Or.inl h.2.2
  · exact Or.inr ⟨h.1, h.2.1, h.2.2⟩
  · simp only [LargeEvenLabel.mk.injEq] at h'
    omega

theorem ggFrameQTwo_qTwoLabel
    {X : Type} [Group X]
    (h₁ : LargeEvenMarking X (fun lab _ _ _ _ _ => lab.n < 2))
    (h₂ : LargeEvenMarking X (fun lab _ _ _ _ _ => ¬ ggFrameQTwo_QTwoCompat lab)) : False := by
  obtain ⟨lab₁, hl₁, hn, hH₁⟩ := ggFrameQTwo_exists_hasLabel h₁
  obtain ⟨lab₂, hl₂, hc, hH₂⟩ := ggFrameQTwo_exists_hasLabel h₂
  exact hc (ggFrameQTwo_qTwoCompat_of_iso (by have := hl₁.1; omega)
    (ggLabelRigidInput_holds lab₁ lab₂ _ hl₁ hl₂ hH₁ hH₂))

theorem ggFrameQTwo_eq_three_of_split {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hs : LargeEvenSplit p lab) (hc : ggFrameQTwo_QTwoCompat lab) : p = 3 := by
  have h1 : ¬ p ∣ 1 := fun h => hp.one_lt.ne' (Nat.dvd_one.1 h)
  have h3 : p ∣ 3 → p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
  rcases hc with hn | ⟨ht, -, hn⟩
  · rcases hs with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩ | ⟨-, h⟩
    · rw [hn] at h; exact absurd h h1
    · rw [hn] at h; exact h3 h
    · rw [hn] at h; exact absurd h h1
    · exact h
  · rcases hs with ⟨-, h⟩ | ⟨hu, -⟩ | ⟨htw, -⟩ | ⟨h, -⟩
    · rw [hn] at h; exact h3 h
    · rw [ht] at hu; exact absurd trivial hu
    · rw [ht] at htw; rcases htw with h | h <;> cases h
    · omega

theorem p_eq_three_of_qTwo
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    (hq : GGInnerDiagOnLabel GGLabQTwo p Bs L) : p = 3 := by
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  by_contra hne
  refine ggFrameQTwo_qTwoLabel (largeEvenMarking_mono (fun _ _ _ _ _ _ h => h.1) hq) ?_
  exact largeEvenMarking_mono
    (fun _ _ _ _ _ _ h hc => hne (ggFrameQTwo_eq_three_of_split hp h.1 hc))
    hC.1.2.2.2.2.2.2.2.1

end CFSG.StandardType.FrameRoute

end
