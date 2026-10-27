module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.Str83Rq410
import CFSG.Quasithin.Recognition.Stroth.Str83Rq411Main
import CFSG.Quasithin.Recognition.Stroth.Str83Rq412

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem IsMaxArc.even_or_of_commutator_eq_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1)
    (hO4 : t.GT = t.K) {ε : ℤ} {n b₀ b₁ : ℕ} (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀)
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hcomm : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ = ⊥) :
    Even (b₁ + 1) ∨ (Odd b₀ ∧ ⁅t.Zv ε, t.Zv (ε + b₀)⁆ = ⊥ ∧ t.IsMaxArc (ε + 1) n) := by
  rcases Nat.even_or_odd b₁ with hb₁even | hb₁odd
  · obtain ⟨m, rfl⟩ : ∃ m, n = 2 * m := by
      obtain ⟨k, hk⟩ := Track.IsMaxArc.even t hfr h hrq
      exact ⟨k, by omega⟩
    rcases Track.IsMaxArc.fixRadius_add_one t hfr h h₁ with hb1 | hb1
    · exact (Track.IsMaxArc.false_of_eq_two_mul_add_two t hfr h h₀ h₁ hb₁even hcomm
        (by omega)).elim
    · have h' : t.IsMaxArc (ε + 1) (2 * m) :=
        Track.IsMaxArc.add_one t hfr h h₁ hb₁even (by omega)
      have h₀' : t.IsFixRadius (ε + 1 + 1) b₀ := by
        have h := Track.IsFixRadius.shift t h₀ 1
        rwa [show ε + 2 * (1 : ℤ) = ε + 1 + 1 by ring] at h
      have hc2 : ⁅t.Zv (ε + 1 + 1), t.Zv (ε + 1 + 1 + b₀)⁆ = ⊥ := by
        rcases Track.IsMaxArc.commutator_le_inf_or_of_even t hfr hrq hO4 h' h₁ h₀' hb₁even with
          hle | ⟨hne, -, -⟩
        · exact Track.IsMaxArc.commutator_eq_bot t hfr hrq hO4 h' h₁ h₀' hle
        · exact (hne hcomm).elim
      rcases Nat.even_or_odd b₀ with hb₀even | hb₀odd
      · exfalso
        have hLv : t.Lv (ε + 1 + 1) ≤ centralizer (t.Zv (ε + 1 + 1) : Set G) :=
          Track.IsFixRadius.Lv_le_centralizer t hfr h₀' hb₀even (Or.inl hc2)
        have hEvenSub : Even (ε + 1 + 1 - ε) := by
          rw [show ε + 1 + 1 - ε = (2 : ℤ) by ring]
          exact ⟨1, by norm_num⟩
        have hLv0 : t.Lv ε ≤ centralizer (t.Zv ε : Set G) :=
          Track.Lv_le_centralizer_of_even_sub t hfr hEvenSub hLv
        have hZ : t.Zv (ε + 1) ≤ t.Zv ε :=
          (Track.IsFixRadius.Zv_le_and_lt t hfr h₀ h₁ hb₁even hcomm).1
        exact (Track.false_of_Zv_le_of_le_centralizer t hfr (u := ε + 1) (v := ε)
          (Or.inl (by ring)) hZ hLv0).elim
      · refine Or.inr ⟨hb₀odd, ?_, h'⟩
        have hmap := congrArg (Subgroup.map
          (MulAut.conj ((t.x₂ * t.x₁) ^ (-1 : ℤ))).toMonoidHom) hc2
        rw [Subgroup.map_commutator, Subgroup.map_bot] at hmap
        rw [map_qv_tau_pow, map_qv_tau_pow] at hmap
        rwa [show (ε + 1 + 1) + 2 * (-1 : ℤ) = ε by ring,
          show (ε + 1 + 1 + (b₀ : ℤ)) + 2 * (-1 : ℤ) = ε + b₀ by ring] at hmap
  · exact Or.inl hb₁odd.add_one

end Track

end CFSG.Quasithin.Stroth.Rq
