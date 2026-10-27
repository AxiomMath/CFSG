module

public import CFSG.Permutation.FiveTransitive.MinimalOrbitStabilizer

public section

namespace CFSG

namespace FiveTransitive.MinimalOrbitBottomSemiregular

open MulAction

theorem semiregular_of_bottom
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (A : Subgroup G) (x : X)
    (hmin : ∀ y : X, y ∉ fixedPoints A X → Nat.card (orbit A x) ≤ Nat.card (orbit A y))
    (hbot : (stabilizer A x).map A.subtype = ⊥) :
    ∀ q : G, q ∈ A → q ≠ 1 → ∀ y : X, y ∉ fixedPoints A X → q • y ≠ y := by
  have hstab : stabilizer A x = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ A.subtype_injective).mp hbot
  intro q hq hne y hy hqy
  have hfixed : y ∈ fixedPoints (⊥ : Subgroup A) X := by
    intro r
    have hr : r.val = 1 := r.property
    change r.val • y = y
    rw [hr, one_smul]
  have he := MinimalOrbitStabilizer.stabilizer_eq_of_minimal_orbit A X x hmin
    (⊥ : Subgroup A) (by rw [hstab]) y hfixed hy
  have hmem : (⟨q, hq⟩ : A) ∈ stabilizer A y := hqy
  rw [he] at hmem
  exact hne (congrArg Subtype.val (Subgroup.mem_bot.mp hmem))

end FiveTransitive.MinimalOrbitBottomSemiregular

end CFSG
