module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.PerfectCover

theorem card_eq_two_mul_odd_of_sylow {A : Type*} [Group A] [Finite A]
    (hA : ∀ S : Sylow 2 A, Nat.card S = 2) :
    ∃ m : ℕ, Odd m ∧ Nat.card A = 2 * m := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow 2 A))
  have hc : Nat.Coprime 2 S.index := by
    simpa only [hA S] using S.card_coprime_index
  refine ⟨S.index, Nat.coprime_two_left.mp hc, ?_⟩
  simpa only [hA S] using (Subgroup.card_mul_index S.toSubgroup).symm

end CFSG.RankThree.PerfectCover
