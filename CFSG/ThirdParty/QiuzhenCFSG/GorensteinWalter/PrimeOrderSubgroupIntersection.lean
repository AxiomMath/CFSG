module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-! # Intersections of prime-order subgroups -/

namespace CFSG.GorensteinWalter

universe u

/-- Two subgroups of the same prime order are equal when they share a
nonidentity element. -/
public theorem subgroup_eq_of_card_eq_prime_of_common_ne_one
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} (hp : p.Prime)
    (A B : Subgroup G)
    (hAcard : Nat.card A = p) (hBcard : Nat.card B = p)
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) (hxne : x ≠ 1) :
    A = B := by
  let I : Subgroup G := A ⊓ B
  have hIdiv : Nat.card I ∣ p := by
    rw [← hAcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hIneOne : Nat.card I ≠ 1 := by
    intro hcard
    have hIbot : I = ⊥ := (Subgroup.eq_bot_iff_card (H := I)).mpr hcard
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      rw [← hIbot]
      exact ⟨hxA, hxB⟩
    exact hxne (Subgroup.mem_bot.mp hxbot)
  have hIcard : Nat.card I = p :=
    ((Nat.dvd_prime hp).mp hIdiv).resolve_left hIneOne
  have hIA : I = A :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hIcard, hAcard])
  have hIB : I = B :=
    Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hIcard, hBcard])
  exact hIA.symm.trans hIB

end CFSG.GorensteinWalter
