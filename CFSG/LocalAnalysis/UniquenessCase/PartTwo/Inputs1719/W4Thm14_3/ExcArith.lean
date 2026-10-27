module

import CFSG.Quasithin.Recognition.St84.Gen.S1ThirteenDim
public import Mathlib.Data.Finset.Powerset

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3

theorem exc_arith {n d : ℕ} {J : Finset ℕ} (hn : 3 ≤ n) (hJ : J.Nonempty)
    (hJn : ∀ i ∈ J, i < n) (hshift : J.image (fun i => (i + d) % n) = J)
    (hdim : d * 2 ^ J.card = 2 * n + 4) :
    n = 6 ∧ d = 2 ∧ (J = {0, 2, 4} ∨ J = {1, 3, 5}) := by
  obtain ⟨hn6, hd2, hcard⟩ :=
    CFSG.Quasithin.St84.eq_three_mul_of_mul_two_pow_eq (m := n) (d := d) (r := 2)
      (by norm_num) (by omega) hJ hJn hshift (by simpa using hdim)
  have hn6' : n = 6 := by omega
  subst hn6'
  subst hd2
  have hsub : J ⊆ Finset.range 6 := fun i hi => Finset.mem_range.mpr (hJn i hi)
  have key : ∀ K ∈ (Finset.range 6).powerset, K.card = 3 →
      K.image (fun i => (i + 2) % 6) = K → K = {0, 2, 4} ∨ K = {1, 3, 5} := by
    decide
  exact ⟨rfl, rfl, key J (Finset.mem_powerset.mpr hsub) hcard hshift⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_3
