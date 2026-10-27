module

public import CFSG.Quasithin.Recognition.Stroth.Str83Rq411O7
public import CFSG.Quasithin.Recognition.Stroth.Str83Rq411Even

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem IsMaxArc.commutator_eq_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1) (hO4 : t.GT = t.K) {ε : ℤ}
    {n b₀ b₁ : ℕ} (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀)
    (h₁ : t.IsFixRadius (ε + 1) b₁)
    (hle : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁)) :
    ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ = ⊥ := by
  by_contra hne
  obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := by
    obtain ⟨k, hk⟩ := Track.IsMaxArc.even t hfr h hrq
    exact ⟨k, by omega⟩
  rcases Nat.even_or_odd b₁ with hb₁ | hb₁
  · rcases Int.even_or_odd (ε + 1) with he | ho
    · exact hne (Track.IsFixRadius.commutator_eq_bot_of_even t hfr h₁ he hb₁)
    · obtain ⟨rfl, rfl⟩ :=
        Track.IsMaxArc.eq_two_of_even_of_commutator_ne_bot t hfr h h₁ hb₁ hle hne
      have hε : Even ε := by
        obtain ⟨k, hk⟩ := ho
        exact ⟨k, by omega⟩
      have e : ε + 1 + ((2 : ℕ) : ℤ) = ε + 3 := by push_cast; ring
      rw [e] at hle hne
      exact Track.IsMaxArc.false_of_eq_six t hfr hε h h₀ h₁ hle hne
  · obtain ⟨hm, hb0a, hb0b, hcase⟩ :=
      Track.IsMaxArc.of_odd_of_commutator_ne_bot t hfr h h₀ h₁ hb₁ hle hne
    rcases hcase with rfl | ⟨rfl, rfl⟩
    · obtain rfl : b₁ = 1 := by omega
      rcases (show b₀ = 1 ∨ b₀ = 2 by omega) with rfl | rfl
      · have h₂ : t.IsFixRadius (ε + 1 + 1) 1 := by
          have := Track.IsFixRadius.shift t h₀ 1
          rwa [show ε + 2 * 1 = ε + 1 + 1 by ring] at this
        apply hne
        have := Track.IsFixRadius.commutator_eq_bot_of_one t hfr hrq h₁ h₂
        simpa using this
      · apply hne
        have := Track.IsMaxArc.commutator_eq_bot_of_eq_four t hfr (by simpa using h) h₀ h₁
        rwa [show ε + 2 = ε + 1 + ((1 : ℕ) : ℤ) by push_cast; ring] at this
    · obtain rfl : b₁ = 3 := by omega
      have e : ε + 1 + ((3 : ℕ) : ℤ) = ε + 4 := by push_cast; ring
      rw [e] at hle hne
      exact hne (Track.IsMaxArc.commutator_eq_bot_of_eq_eight t hfr (by simpa using h) h₀ h₁ hle)

end Track

end CFSG.Quasithin.Stroth.Rq
