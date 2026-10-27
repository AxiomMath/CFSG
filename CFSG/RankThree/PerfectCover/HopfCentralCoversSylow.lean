module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PerfectCover

theorem sylow_two_card_le_of_surjective {A B : Type*} [Group A] [Group B]
    [Finite A] [Finite B] (f : A →* B) (hf : Function.Surjective f)
    (hA : ∀ S : Sylow 2 A, Nat.card S ≤ 2) :
    ∀ S : Sylow 2 B, Nat.card S ≤ 2 := by
  intro S
  obtain ⟨P, rfl⟩ := Sylow.mapSurjective_surjective hf 2 S
  have hcard : Nat.card (P.mapSurjective hf) ≤ Nat.card P := by
    change Nat.card ((P : Subgroup A).map f) ≤ Nat.card P
    exact Nat.le_of_dvd Nat.card_pos ((P : Subgroup A).card_map_dvd f)
  exact hcard.trans (hA P)

end CFSG.RankThree.PerfectCover
