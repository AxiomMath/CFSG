module

import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Assembly.Defs
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.LocalAnalysis.ComponentClassification.OddCore

public noncomputable section

namespace CFSG.ShultStronglyClosedTI

open CFSG.Open

universe u

variable {F : Type u} [Group F] [Finite F]

omit [Finite F] in
theorem invertedHull_odd_subgroup_le_index_two (V : Subgroup F) [V.Normal]
    (hindex : V.index = 2) (W : Subgroup F) (hWodd : Odd (Nat.card W)) : W ≤ V := by
  let q := QuotientGroup.mk' V
  have hcard : Nat.card (F ⧸ V) = 2 := V.index_eq_card.symm.trans hindex
  have himageodd : Odd (Nat.card (W.map q)) := hWodd.of_dvd_nat (W.card_map_dvd q)
  have hdiv : Nat.card (W.map q) ∣ 2 := hcard ▸ (W.map q).card_subgroup_dvd_card
  have hone : Nat.card (W.map q) = 1 := himageodd.coprime_two_right.eq_one_of_dvd hdiv
  have hbot : W.map q = ⊥ := Subgroup.card_eq_one.mp hone
  intro w hw
  have hqw := Subgroup.mem_map_of_mem q hw
  rw [hbot] at hqw
  exact (QuotientGroup.eq_one_iff w).mp (Subgroup.mem_bot.mp hqw)

theorem invertedHull_odd_index_two_eq_oddCore (V : Subgroup F) [V.Normal]
    (hVodd : Odd (Nat.card V)) (hindex : V.index = 2) : V = oddCore F := by
  exact le_antisymm (CFSG.ComponentClassification.OddCore.maximal F V inferInstance hVodd)
    (invertedHull_odd_subgroup_le_index_two V hindex (oddCore F)
      (CFSG.ComponentClassification.OddCore.odd_card F))

theorem invertedHull_odd_index_two_solvable (V : Subgroup F) [V.Normal]
    (hVodd : Odd (Nat.card V)) (hindex : V.index = 2) : Group.IsSolvable F := by
  let : Group.IsSolvable V := CFSG.FeitThompson.isSolvable_of_odd_natCard V hVodd
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card (F ⧸ V) = 2 := V.index_eq_card.symm.trans hindex
  let : IsCyclic (F ⧸ V) := isCyclic_of_prime_card hcard
  let : Group.IsSolvable (F ⧸ V) := inferInstance
  exact Group.isSolvable_of_subgroup_quotient V

end CFSG.ShultStronglyClosedTI
