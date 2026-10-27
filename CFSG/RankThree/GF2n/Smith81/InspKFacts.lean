module

public import CFSG.Timmesfeld.RootOutcome

public section

namespace CFSG.RankThree.GF2n.Smith81.Insp

open CFSG CFSG.Blueprint CFSG.Open CFSG.Timmesfeld

@[expose] def TimmesfeldTag (t : StatedLieTag) (n f : ℕ) : Prop :=
  (t = .PSL ∧ 3 ≤ n) ∨ (t = .PSp ∧ 3 ≤ n) ∨ ((t = .POmegaPlus ∨ t = .POmegaMinus) ∧ 4 ≤ n) ∨
    (t = .G2 ∧ n = 0 ∧ 2 ≤ f) ∨
    (n = 0 ∧ (t = .trialityD4 ∨ t = .F4 ∨ t = .E6 ∨ t = .twistedE6 ∨ t = .E7 ∨ t = .E8))

@[expose] def RootOutcome (G : Type) [Group G] (D : Set G) : Prop :=
  ∃ (t : StatedLieTag) (n f : ℕ), 1 ≤ f ∧ TimmesfeldTag t n f ∧ LieModel G t n 2 f ∧
    ∀ d ∈ D, Nat.card (rootGroup D d) = 2 ^ f

@[expose] def K1NSLStatement : Prop :=
  ∀ (G : Type) [Group G] (D : Set G), Hyp G D → (∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) →
    ARS.NonSimplyLacedOutcome G → ARS.NSLData G (rootClass D) →
      RootOutcome G D ∨ LieModel G .PSU 3 3 1

theorem RootOutcomeSL.rootOutcome {G : Type} [Group G] {D : Set G} (h : RootOutcomeSL G D) :
    RootOutcome G D := by
  obtain ⟨f, hf, hE, hL⟩ := h
  rcases hL with ⟨n, hn, hL⟩ | ⟨n, hn, hL⟩ | hL | hL | hL
  · exact ⟨.PSL, n, f, hf, Or.inl ⟨rfl, hn⟩, hL, hE⟩
  · exact ⟨.POmegaPlus, n, f, hf, Or.inr (Or.inr (Or.inl ⟨Or.inl rfl, hn⟩)), hL, hE⟩
  · exact ⟨.E6, 0, f, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by simp⟩))), hL, hE⟩
  · exact ⟨.E7, 0, f, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by simp⟩))), hL, hE⟩
  · exact ⟨.E8, 0, f, hf, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, by simp⟩))), hL, hE⟩

theorem rootOutcome_of_K1NSL (hK : K1NSLStatement) {G : Type} [Group G] {D : Set G}
    (hH : Hyp G D) (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) :
    RootOutcome G D ∨ LieModel G .PSU 3 3 1 := by
  rcases Timmesfeld.rootOutcome hH hl with h | ⟨hns, hd⟩
  · exact Or.inl (RootOutcomeSL.rootOutcome h)
  · exact hK G D hH hl hns hd

end CFSG.RankThree.GF2n.Smith81.Insp
