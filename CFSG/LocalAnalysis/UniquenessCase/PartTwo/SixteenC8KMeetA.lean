module

public import TauCeti.RepresentationTheory.CharacterTable.Solvable
public import CFSG.Quasithin.Background.RonanE42ClosedA8
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped MatrixGroups

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem c8k_sl27_eq_top_of_not_solvable {H : Subgroup ↥(StatedSL 2 (ZMod 7))}
    (hns : ¬ Group.IsSolvable ↥H) : H = ⊤ := by
  haveI hperf : Group.IsPerfect (SL(2, ZMod 7)) :=
    ⟨Matrix.SL2.commutator_eq_top (F := ZMod 7) (a := 2) (by decide) (by decide)⟩
  haveI : Group.IsPerfect ↥(StatedSL 2 (ZMod 7)) :=
    Group.IsPerfect.ofSurjective
      (f := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod 7)).toMonoidHom)
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 (ZMod 7)).surjective
  have hcard : Nat.card ↥(StatedSL 2 (ZMod 7)) = 336 := by
    rw [CFSG.Open.StatedAPI.card_statedSL_two, Nat.card_zmod]
    norm_num
  have hdvd : Nat.card H ∣ 336 := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card H
  have hcases : ∀ n ∈ Nat.divisors 336, n ∣ 2 ^ 4 * 7 ∨ n ∣ 2 ^ 4 * 3 ∨ n ∣ 3 * 7 ∨
      n ∈ ({42, 84, 168, 336} : Finset ℕ) := by decide
  have hnmem : Nat.card H ∈ Nat.divisors 336 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  rcases hcases (Nat.card H) hnmem with h1 | h2 | h3 | h4
  · exact absurd (TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (p := 2) (q := 7)
      Nat.prime_two (by norm_num) (a := 4) (b := 1) (by simpa using h1)) hns
  · exact absurd (TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (p := 2) (q := 3)
      Nat.prime_two (by norm_num) (a := 4) (b := 1) (by simpa using h2)) hns
  · exact absurd (TauCeti.isSolvable_of_card_dvd_prime_pow_mul_prime_pow (p := 3) (q := 7)
      (by norm_num) (by norm_num) (a := 1) (b := 1) (by simpa using h3)) hns
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h4
    rcases h4 with h4 | h4 | h4 | h4
    · exact absurd (CFSG.GroupTheory.groups_order_below_sixty_solvable (G := ↥H)
        (by rw [h4]; norm_num)) hns
    · have hci := Subgroup.card_mul_index H
      rw [h4, hcard] at hci
      exact CFSG.Quasithin.RonanE42.Closed.eq_top_of_index_le_four (by omega)
    · have hci := Subgroup.card_mul_index H
      rw [h4, hcard] at hci
      exact CFSG.Quasithin.RonanE42.Closed.eq_top_of_index_le_four (by omega)
    · have hci := Subgroup.card_mul_index H
      rw [h4, hcard] at hci
      exact CFSG.Quasithin.RonanE42.Closed.eq_top_of_index_le_four (by omega)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
