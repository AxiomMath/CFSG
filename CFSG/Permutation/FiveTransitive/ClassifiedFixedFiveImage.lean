module

public import CFSG.Permutation.FiveTransitive.ClassifiedOddSemiregularFiveOrders
public import CFSG.Permutation.FiveTransitive.FixedNormalizerAction

public section

namespace CFSG

namespace FiveTransitive.ClassifiedFixedFiveImage

open MulAction FixedNormalizerAction

theorem degree_order_pairs
    {G X : Type} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G)
    (hlarge : 7 ≤ Nat.card (Fixed (X := X) Q))
    (hodd : Odd (Nat.card (Fixed (X := X) Q)))
    (h5 : IsMultiplyPretransitive (Image (X := X) Q) (Fixed (X := X) Q) 5)
    (hlocal : ∀ (b : Fin 5 ↪ Fixed (X := X) Q)
        (S : Sylow 2 (stabilizer (Image (X := X) Q) b)),
      let T := (S : Subgroup (stabilizer (Image (X := X) Q) b)).map
        (stabilizer (Image (X := X) Q) b).subtype
      T ≠ ⊥ ∧ Nat.card (fixedPoints T (Fixed (X := X) Q)) = 5 ∧
        ∀ t : Image (X := X) Q, t ∈ T → t ≠ 1 →
          ∀ z : Fixed (X := X) Q, z ∉ fixedPoints T (Fixed (X := X) Q) → t • z ≠ z)
    (hclass : Nat.card (Image (X := X) Q) = (Nat.card (Fixed (X := X) Q)).factorial ∨
      (7 ≤ Nat.card (Fixed (X := X) Q) ∧
        Nat.card (Image (X := X) Q) = (Nat.card (Fixed (X := X) Q)).factorial / 2) ∨
      (Nat.card (Fixed (X := X) Q) = 12 ∧ Nat.card (Image (X := X) Q) = 95040) ∨
      (Nat.card (Fixed (X := X) Q) = 24 ∧ Nat.card (Image (X := X) Q) = 244823040)) :
    (Nat.card (Fixed (X := X) Q) = 7 ∧ Nat.card (Image (X := X) Q) = 5040) ∨
      (Nat.card (Fixed (X := X) Q) = 9 ∧ Nat.card (Image (X := X) Q) = 181440) := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  obtain ⟨b⟩ : Nonempty (Fin 5 ↪ Fixed (X := X) Q) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_fin, ← Nat.card_eq_fintype_card, Nat.card_fin] using
        (show 5 ≤ Nat.card (Fixed (X := X) Q) by omega))
  let S : Sylow 2 (stabilizer (Image (X := X) Q) b) := Classical.choice inferInstance
  obtain ⟨hT, hfix, hfree⟩ := hlocal b S
  have hS : (S : Subgroup (stabilizer (Image (X := X) Q) b)) ≠ ⊥ := by
    intro h
    apply hT
    simp only [h, Subgroup.map_bot]
  have h := ClassifiedOddSemiregularFiveOrders.degree_order_pairs
    (Fixed (X := X) Q) (Image (X := X) Q) h5
    (by simpa only [Nat.card_eq_fintype_card] using hodd)
    (by simpa only [Nat.card_eq_fintype_card] using hlarge) b S hS hfix hfree
    (by simpa only [Nat.card_eq_fintype_card] using hclass)
  simpa only [Nat.card_eq_fintype_card] using h

end FiveTransitive.ClassifiedFixedFiveImage

end CFSG
