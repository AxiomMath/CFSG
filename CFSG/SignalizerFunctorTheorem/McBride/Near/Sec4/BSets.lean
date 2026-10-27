module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec4.BAux46

public section

open CFSG.Open CFSG.SignalizerFunctorTheorem.Nonsolvable
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

variable {H : Type*} [Group H] [Finite H]

theorem le_oStar_of_mem_bOne (hC : HypC H) {X : Subgroup H} (hX : X ∈ bOne (bSet H))
    (hperf : Group.IsPerfect X) : X ≤ oStar H := by
  obtain ⟨hXb, hmax⟩ := hX
  have hXo : oStar ↥X = ⊤ := (kOf_eq_self_iff_oStar_eq_top X).mp hXb
  exact BAux.le_oStar_of_deg_le hC hXo hperf (hmax _ BAux.oStar_mem_bSet)

theorem mul_solvableRadical_eq_oStar (hC : HypC H) {X : Subgroup H} (hX : X ∈ bTwo (bSet H)) :
    (X : Set H) * (CFSG.solvableRadical H : Set H) = (oStar H : Set H) := by
  obtain ⟨⟨hXb, hXmax⟩, hmax⟩ := hX
  have hKone : oStar H ∈ bOne (bSet H) :=
    ⟨BAux.oStar_mem_bSet, fun Y hY => BAux.deg_le_oStar_of_mem_bSet hC hY⟩
  exact (BAux.card_quot_le_oStar hC hXb (hXmax _ BAux.oStar_mem_bSet)).2 (hmax _ hKone)

theorem bStar_bSet_eq (hC : HypC H) : bStar (bSet H) = {oStar H} := by
  have hKone : oStar H ∈ bOne (bSet H) :=
    ⟨BAux.oStar_mem_bSet, fun Y hY => BAux.deg_le_oStar_of_mem_bSet hC hY⟩
  have hKtwo : oStar H ∈ bTwo (bSet H) := by
    refine ⟨hKone, fun Y hY => ?_⟩
    exact (BAux.card_quot_le_oStar hC hY.1 (hY.2 _ BAux.oStar_mem_bSet)).1
  have hle : ∀ X ∈ bTwo (bSet H), X ≤ oStar H := by
    intro X hX x hx
    have := mul_solvableRadical_eq_oStar hC hX
    have hx' : x ∈ (X : Set H) * (CFSG.solvableRadical H : Set H) :=
      ⟨x, hx, 1, one_mem _, mul_one x⟩
    rw [this] at hx'
    exact hx'
  ext X
  constructor
  · rintro ⟨hX2, hXmax⟩
    exact Subgroup.eq_of_le_of_card_ge (hle X hX2) (hXmax _ hKtwo)
  · intro hX
    rw [Set.mem_singleton_iff] at hX
    subst hX
    exact ⟨hKtwo, fun Y hY => Subgroup.card_le_of_le (hle Y hY)⟩

end CFSG.SignalizerFunctorTheorem.McBride.Near
