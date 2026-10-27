module

public import CFSG.Permutation.FiveTransitive.MaximalFixedSubgroupRealization
public import CFSG.Permutation.FiveTransitive.OddOriginalTupleEntrance
public import CFSG.Permutation.FiveTransitive.ChosenFixedFiveInducedTransitivity
public import CFSG.Permutation.FiveTransitive.MinimalOrbitFixedBounds

public section

namespace CFSG

namespace FiveTransitive.OddMaximalOrderDescent

open MulAction FixedNormalizerAction OyamaMinimalOrbitDescent

theorem local_structure
    (X : Type) [Fintype X] [DecidableEq X]
    (G : Subgroup (Equiv.Perm X)) (hcard : 28 ≤ Fintype.card X)
    (h5 : IsMultiplyPretransitive G X 5) (hnotAlt : ¬ alternatingGroup X ≤ G)
    (hodd : Odd (Fintype.card X))
    (U : Subgroup G) (hU : IsPGroup 2 U) (hne : U ≠ ⊥)
    (hfixU : 6 ≤ Nat.card (fixedPoints U X))
    (hmax : ∀ T : Subgroup G, IsPGroup 2 T → 6 ≤ Nat.card (fixedPoints T X) →
      Nat.card T ≤ Nat.card U) :
    7 ≤ Nat.card (Fixed (X := X) U) ∧ Odd (Nat.card (Fixed (X := X) U)) ∧
      Nat.card (Fixed (X := X) U) < Nat.card X ∧
      Nat.card (Fixed (X := X) U) ≤ Fintype.card X / 2 ∧
      IsMultiplyPretransitive (Image (X := X) U) (Fixed (X := X) U) 5 ∧
      (∀ (b : Fin 5 ↪ Fixed (X := X) U)
        (S : Sylow 2 (stabilizer (Image (X := X) U) b)),
      let T := (S : Subgroup (stabilizer (Image (X := X) U) b)).map
        (stabilizer (Image (X := X) U) b).subtype
      T ≠ ⊥ ∧ Nat.card (fixedPoints T (Fixed (X := X) U)) = 5 ∧
        ∀ t : Image (X := X) U, t ∈ T → t ≠ 1 →
          ∀ z : Fixed (X := X) U, z ∉ fixedPoints T (Fixed (X := X) U) → t • z ≠ z) := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, P, x, _, _, hx, _, hTx, hmin⟩ :=
    MaximalFixedSubgroupRealization.exists_minimal_orbit (k := 5) U hU hfixU hmax
  obtain ⟨_, hfixed⟩ := OddOriginalTupleEntrance.entrance X G hcard h5 hnotAlt hodd a P
  have hfixed' : fixedPoints (ambientSylow a P) X = Set.range a := hfixed
  have hfix : Nat.card (fixedPoints (ambientSylow a P) X) = 5 := by
    rw [hfixed', Nat.card_coe_set_eq, Set.ncard_range_of_injective a.injective, Nat.card_fin]
  have hx' : x ∉ fixedPoints (ambientSylow a P) X := by rwa [hfixed']
  have hmin' : ∀ y : X, y ∉ fixedPoints (ambientSylow a P) X →
      Nat.card (orbit (ambientSylow a P) x) ≤ Nat.card (orbit (ambientSylow a P) y) := by
    simpa only [hfixed'] using hmin
  have hd := ChosenFixedFiveInducedTransitivity.chosen_five h5 a P hfix x hx' hmin'
  dsimp only at hd
  rw [hTx] at hd
  obtain ⟨_, _, hseven, hoddU, htrans, hlocal, hcases⟩ := hd
  have hlt : Nat.card (Fixed (X := X) U) < Nat.card X := by
    rcases hcases with ⟨hbot, _⟩ | ⟨_, hlt⟩
    · exact False.elim (hne hbot)
    · exact hlt
  have hhalf : Nat.card (Fixed (X := X) U) ≤ Fintype.card X / 2 := by
    rw [fixed_eq]
    exact MinimalOrbitFixedBounds.fixed_card_le_half X G hcard h5 hnotAlt U hne
  exact ⟨hseven, hoddU, hlt, hhalf, htrans, hlocal⟩

end FiveTransitive.OddMaximalOrderDescent

end CFSG
