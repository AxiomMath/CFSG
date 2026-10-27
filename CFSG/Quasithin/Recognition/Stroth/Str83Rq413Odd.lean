module

public import CFSG.Quasithin.Recognition.Stroth.Str83RqArc
import CFSG.Quasithin.Recognition.Stroth.Str83Rq413Type
import CFSG.Quasithin.Recognition.Stroth.Str83Rq413Mid
import CFSG.Quasithin.Recognition.Stroth.Str83Rq413Four

public section

namespace CFSG.Quasithin.Stroth.Rq

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped commutatorElement
open CFSG.Quasithin.Stroth.G5 CFSG.GH74.Uniqueness.Bender CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

namespace Track

variable {L1 L2 S : Subgroup G} (t : Track L1 L2 S)

theorem IsMaxArc.false_of_odd_of_commutator_eq_bot
    {a f : ℕ} (hfr : Frame L1 L2 S a f) (hrq : f ≠ 2 * a + 1)
    {ε : ℤ} {n b₀ b₁ : ℕ} (h : t.IsMaxArc ε n) (h₀ : t.IsFixRadius ε b₀)
    (h₁ : t.IsFixRadius (ε + 1) b₁) (hb₁ : Odd b₁)
    (hcomm : ⁅t.Zv (ε + 1), t.Zv (ε + 1 + b₁)⁆ = ⊥) : False := by
  obtain ⟨hC, hZ⟩ := Track.IsFixRadius.Lv_le_centralizer_and_Zv_le t hfr h₁ hb₁ hcomm
  obtain ⟨hn, -, hZQ⟩ := Track.IsMaxArc.eq_of_Zv_le t hfr hrq h h₀ h₁ hb₁ hZ
  subst hn
  have hZQ' : t.Zv (ε + 1 + b₁) =
      omegaOneCenterOf (pCoreOf 2 (t.Gw ε (ε + 2 * (b₁ + 1)))) := by
    push_cast at hZQ ⊢
    exact hZQ
  obtain ⟨hε, hf, hcard⟩ := Track.IsMaxArc.even_and_eq t hfr hrq h h₁ hb₁ hC hZ hZQ'
  by_cases hH : t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁) ≤ t.Qv (ε + 2 + b₁)
  · exact Track.IsMaxArc.false_of_inf_Qv_le t hfr h h₁ hb₁ hε hf hZ hH
  · by_cases hX : ⁅t.Zv (ε + 2 + b₁) ⊓ t.Gv (ε + 1),
        t.Zv (ε + 1) ⊓ t.Qv (ε + 1 + b₁)⁆ = ⊥
    · exact Track.IsFixRadius.false_of_commutator_inf_eq_bot t hfr h₁ hb₁ hε hf hZ hH hX
    · have hb1 : b₁ = 1 := Track.IsMaxArc.eq_one_of_commutator_inf_ne_bot t hfr h h₁ hb₁ hX
      subst b₁
      have h4 : t.IsMaxArc ε 4 := h
      exact Track.IsMaxArc.false_of_four t hfr h4 hε hf hC hZ hcard

end Track

end CFSG.Quasithin.Stroth.Rq
