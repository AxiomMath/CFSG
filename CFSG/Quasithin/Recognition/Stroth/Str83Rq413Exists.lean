module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.Str83Rq410
import CFSG.Quasithin.Recognition.Stroth.Str83RqOdd
import CFSG.Quasithin.Recognition.Stroth.Str83Rq411Main
import CFSG.Quasithin.Recognition.Stroth.Str83Rq412Main

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem exists_isMaxArc_commutator_eq_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1)
    (hO4 : t.GT = t.K) :
    ∃ ε : ℤ, ∃ n b₀ b₁ : ℕ, t.IsMaxArc ε n ∧ t.IsFixRadius ε b₀ ∧ t.IsFixRadius (ε + 1) b₁ ∧
      Odd b₁ ∧ ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ = ⊥ := by
  obtain ⟨ε, n, h⟩ := Track.exists_isMaxArc t hfr hO4
  obtain ⟨b₀, h₀⟩ := Track.exists_isFixRadius t hfr hO4 ε
  obtain ⟨b₁, h₁⟩ := Track.exists_isFixRadius t hfr hO4 (ε + 1)
  obtain ⟨b', h'⟩ := Track.exists_isFixRadius t hfr hO4 (ε - 1)
  have hshift : ∀ {m : ℕ}, t.IsMaxArc (ε + 1) m → t.IsMaxArc (ε - 1) m := by
    intro m hm
    have hk := Track.IsMaxArc.shift t hm (-1)
    rwa [show (ε + 1) + 2 * (-1 : ℤ) = ε - 1 by ring] at hk
  have hle : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ ≤ t.Zv (ε + 1) ⊓ t.Zv (ε + 1 + b₁) := by
    rcases Nat.even_or_odd b₀ with hb₀ev | hb₀od
    · rcases Track.IsMaxArc.commutator_le_inf_or_of_even t hfr hrq hO4 h h₀ h₁ hb₀ev with
        hle | ⟨hne, hle, harc⟩
      · exact hle
      · exfalso
        have hle' : ⁅t.Zv ((ε - 1) + 1), t.Zv ((ε - 1) + 1 + b₀)⁆ ≤
            t.Zv ((ε - 1) + 1) ⊓ t.Zv ((ε - 1) + 1 + b₀) := by
          rwa [show (ε - 1) + 1 = ε by ring]
        have h₀' : t.IsFixRadius ((ε - 1) + 1) b₀ := by
          rwa [show (ε - 1) + 1 = ε by ring]
        have hbot := Track.IsMaxArc.commutator_eq_bot t hfr hrq hO4 (hshift harc) h' h₀' hle'
        rw [show (ε - 1) + 1 = ε by ring] at hbot
        exact hne hbot
    · exact Track.IsMaxArc.commutator_le_inf_of_odd t hfr hrq h h₀ h₁ hb₀od
  have hcomm : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ = ⊥ :=
    Track.IsMaxArc.commutator_eq_bot t hfr hrq hO4 h h₀ h₁ hle
  rcases Track.IsMaxArc.even_or_of_commutator_eq_bot t hfr hrq hO4 h h₀ h₁ hcomm with
    hb | ⟨hb₀od, hbot, harc⟩
  · exact ⟨ε, n, b₀, b₁, h, h₀, h₁,
      Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hb), hcomm⟩
  · refine ⟨ε - 1, n, b', b₀, hshift harc, h', ?_, hb₀od, ?_⟩
    · rwa [show (ε - 1) + 1 = ε by ring]
    · rwa [show (ε - 1) + 1 = ε by ring]

end Track

end CFSG.Quasithin.Stroth.Rq
