module

public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Center

public section

namespace CFSG.StandardType.S2MathAs51600SmallBound

theorem card_quot_center_le_of_image_equiv {X R : Type} [Group X] [Group R] [Finite R]
    (pi : X →* R) (J : Subgroup X)
    (h : Nonempty ((J ⧸ Subgroup.center J) ≃*
      ((J.map pi) ⧸ Subgroup.center (J.map pi)))) :
    Nat.card (J ⧸ Subgroup.center J) ≤ Nat.card R := by
  obtain ⟨e⟩ := h
  calc Nat.card (J ⧸ Subgroup.center J)
      = Nat.card ((J.map pi) ⧸ Subgroup.center (J.map pi)) := Nat.card_congr e.toEquiv
    _ ≤ Nat.card (J.map pi) :=
        Nat.card_le_card_of_surjective _
          (QuotientGroup.mk'_surjective (Subgroup.center (J.map pi)))
    _ ≤ Nat.card R := Subgroup.card_le_card_group _

theorem card_bound_contradiction {X R : Type} [Group X] [Group R] [Finite R]
    (pi : X →* R) (J : Subgroup X)
    (h : Nonempty ((J ⧸ Subgroup.center J) ≃*
      ((J.map pi) ⧸ Subgroup.center (J.map pi))))
    (hbig : 174182400 ≤ Nat.card (J ⧸ Subgroup.center J))
    (hR : Nat.card R < 174182400) : False := by
  have hle := card_quot_center_le_of_image_equiv pi J h
  omega

end CFSG.StandardType.S2MathAs51600SmallBound
end
