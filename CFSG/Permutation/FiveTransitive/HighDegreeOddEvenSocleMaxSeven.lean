module

public import CFSG.Permutation.FiveTransitive.HighDegreeOddEvenSocle
public import CFSG.Permutation.FiveTransitive.HighDegreeOddMaxSevenEntrance

public section

namespace CFSG

namespace FiveTransitive.HighDegreeOddEvenSocleMaxSeven

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem exists_entrance
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X))
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7) :
    ∃ H : Subgroup (Equiv.Perm X), H ≤ G ∧ IsSimpleGroup H ∧
      ¬ IsMulCommutative H ∧ FaithfulSMul H X ∧
      IsMultiplyPretransitive H X 5 ∧ ¬ alternatingGroup X ≤ H ∧
      (∀ h : H, Equiv.Perm.sign h.val = 1) ∧
      ∀ (a : Fin 5 ↪ X) (P : Sylow 2 (stabilizer H a)),
    ∃ (x : X) (Q : Subgroup H),
      x ∉ Set.range a ∧
      Q = (stabilizer (ambientSylow a P) x).map (ambientSylow a P).subtype ∧
      (∀ y : X, y ∉ Set.range a →
        Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y)) ∧
      Q < ambientSylow a P ∧ IsPGroup 2 Q ∧ Q ≠ ⊥ ∧
      Nat.card (fixedPoints Q X) = 7 ∧ Nat.card (Fixed (X := X) Q) = 7 ∧
      Nat.card (Fixed (X := X) Q) < Nat.card X ∧
      Nat.card (Fixed (X := X) Q) ≤ Fintype.card X / 2 ∧
      Image (X := X) Q = ⊤ ∧ Nat.card (Image (X := X) Q) = 5040 ∧
      (∃ T : Sylow 2 (fixingSubgroup H (insert x (Set.range a))),
        (T : Subgroup (fixingSubgroup H (insert x (Set.range a)))).map
          (fixingSubgroup H (insert x (Set.range a))).subtype = Q) ∧
      (∃ S : Sylow 2 (fixingSubgroup H (fixedPoints Q X)),
        (S : Subgroup (fixingSubgroup H (fixedPoints Q X))).map
          (fixingSubgroup H (fixedPoints Q X)).subtype = Q) ∧
      (∀ t : H, t ∈ Q → orderOf t = 2 → fixedBy X t = fixedPoints Q X) ∧
      (∃ t : H, t ∈ Q ∧ orderOf t = 2 ∧ fixedBy X t = fixedPoints Q X ∧
        (fixedBy X t).ncard = 7 ∧
        ∀ u : H, orderOf u = 2 → (fixedBy X u).ncard ≤ (fixedBy X t).ncard) ∧
      Fintype.card X % 4 = 3 ∧ 4 ∣ (Fintype.card X - 7) ∧
      ∀ q : H, q ∈ Q → q ≠ 1 → ∀ z : X, z ∉ fixedPoints Q X → q • z ≠ z := by
  obtain ⟨H, hHG, hsimple, hnoncomm, hfaithful, hH5, hHnotAlt, heven⟩ :=
    HighDegreeOddEvenSocle.exists_subgroup X G hcard h5 hnotAlt hodd
  let _ : IsSimpleGroup H := hsimple
  have hmaxH : ∀ t : H, orderOf t = 2 → (fixedBy X t).ncard ≤ 7 := by
    intro t ht
    exact hmax (Subgroup.inclusion hHG t)
      ((orderOf_injective (Subgroup.inclusion hHG) (Subgroup.inclusion_injective hHG) t).trans ht)
  refine ⟨H, hHG, hsimple, hnoncomm, hfaithful, hH5, hHnotAlt, heven, ?_⟩
  intro a P
  obtain ⟨x, Q, hx, hQ, hmin, hQA, hQp, hne, h7, h7', hlt, hhalf,
    htop, horder, hT, hS, hall, ⟨t, htQ, ht2, htfix, ht7, htmax⟩, hsemi⟩ :=
    HighDegreeOddMaxSevenEntrance.exists_entrance X H hcard hH5 hHnotAlt hodd hmaxH a P
  have hmod := SimpleActionEven.fixed_card_mod_four (X := X) hnoncomm t ht2
  rw [ht7] at hmod
  have hnmod : Fintype.card X % 4 = 3 := by omega
  have hdiv : 4 ∣ (Fintype.card X - 7) := Nat.dvd_of_mod_eq_zero (by omega)
  exact ⟨x, Q, hx, hQ, hmin, hQA, hQp, hne, h7, h7', hlt, hhalf,
    htop, horder, hT, hS, hall, ⟨t, htQ, ht2, htfix, ht7, htmax⟩, hnmod, hdiv, hsemi⟩

end FiveTransitive.HighDegreeOddEvenSocleMaxSeven

end CFSG
