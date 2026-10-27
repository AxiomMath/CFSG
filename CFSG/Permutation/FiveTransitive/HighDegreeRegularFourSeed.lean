module

public import CFSG.Permutation.FiveTransitive.MaxSevenRegularFourOrbit
public import CFSG.Permutation.FiveTransitive.CommutingFourSeed
public import CFSG.Permutation.FiveTransitive.HighDegreeCommutingInvolution

public section

namespace CFSG

namespace FiveTransitive.HighDegreeRegularFourSeed

open MulAction Research.HallOrbitTransitivity Research.HallRegularOrbits

variable {G X : Type} [Group G] [Finite G] [Fintype X] [MulAction G X]

theorem exists_fixing_regular_four
    (hcard : 28 ≤ Fintype.card X) (h5 : IsMultiplyPretransitive G X 5)
    (hmax : ∀ t : G, orderOf t = 2 → (fixedBy X t).ncard ≤ 7)
    (a b : G) (ha : orderOf a = 2) (hb : orderOf b = 2)
    (hab : Commute a b) (hne : a ≠ b) :
    ∃ (z : X) (u : G),
      (regularFourSet a b z).ncard = 4 ∧
      regularFourSet a b z ⊆ (exceptionalSet (X := X) a b)ᶜ ∧
      Even (Nat.card (fixingSubgroup G (regularFourSet a b z))) ∧
      u ∈ fixingSubgroup G (regularFourSet a b z) ∧
      orderOf u = 2 ∧
      (∀ y ∈ regularFourSet a b z, u • y = y) ∧
      Commute u a ∧ Commute u b := by
  obtain ⟨z, hzcard, hzout, hza, hzb⟩ :=
    MaxSevenRegularFourOrbit.exists_regular_four_set (by omega) hmax a b ha hb hab hne
  have ha2 : a * a = 1 := by simpa only [ha, pow_two] using (pow_orderOf_eq_one a)
  have hb2 : b * b = 1 := by simpa only [hb, pow_two] using (pow_orderOf_eq_one b)
  obtain ⟨K, hK, hmem⟩ := CommutingFourSeed.exists_pair_group a b ha2 hb2 hab.eq
  have hpreserves : ∀ k : G, k ∈ K → ∀ y ∈ regularFourSet a b z,
      k • y ∈ regularFourSet a b z := by
    intro k hk y hy
    rcases (hmem k).mp hk with rfl | rfl | rfl | rfl
    · simpa only [one_smul] using hy
    · exact hza y hy
    · exact hzb y hy
    · rw [mul_smul]; exact hza _ (hzb y hy)
  obtain ⟨u, hu, hu2, hufix, hucomm⟩ :=
    HighDegreeCommutingInvolution.exists_of_five_transitive G X hcard h5
      (regularFourSet a b z) hzcard K hK hpreserves
  have h4 : IsMultiplyPretransitive G X 4 := by
    let _ : IsMultiplyPretransitive G X 5 := h5
    exact isMultiplyPretransitive_of_le (G := G) (α := X) (n := 5) (by decide)
      (by simpa only [Nat.card_eq_fintype_card] using (show 5 ≤ Fintype.card X by omega))
  exact ⟨z, u, hzcard, hzout,
    FourTransitiveEvenStabilizer.even_card_fixingSubgroup G X (by omega) h4 _ hzcard,
    hu, hu2, hufix, hucomm a ((hmem a).mpr (Or.inr (Or.inl rfl))),
    hucomm b ((hmem b).mpr (Or.inr (Or.inr (Or.inl rfl))))⟩

end FiveTransitive.HighDegreeRegularFourSeed

end CFSG
