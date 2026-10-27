module

public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating10

public section

namespace CFSG.RankThree.PartTwo.Sec16.Step163Alt

open Equiv CFSG.RankThree.PartTwo.KFacts.KP2

@[expose] def conjBy (p : Fin 6 × Fin 8) (x : Perm (Fin 10)) : Perm (Fin 10) :=
  monoRep p.1 p.2 * x * (monoRep p.1 p.2)⁻¹

@[expose] def orbitTab (i j k : Fin 3) : Fin 4 → Fin 6 × Fin 8 :=
  if i ≠ 0 ∧ j ≠ 0 ∧ k ≠ 0 then ![(0, 0), (0, 3), (0, 5), (0, 6)]
  else if k = 0 then ![(0, 0), (4, 0), (5, 0), (0, 5)] else ![(0, 0), (4, 0), (5, 0), (0, 3)]

theorem orbitTab_even : ∀ (i j k : Fin 3) (m : Fin 4),
    evenTable (orbitTab i j k m).1 (orbitTab i j k m).2 = true := by
  decide

theorem orbitTab_mem (i j k : Fin 3) (m : Fin 4) :
    monoRep (orbitTab i j k m).1 (orbitTab i j k m).2 ∈ normAlt :=
  monoRep_mem_normAlt (orbitTab_even i j k m)

theorem orbitTab_distinct : ∀ i j k : Fin 3, eTwentySevenF i j k ≠ 1 →
    (¬ ∃ a : Fin 6, eTwentySevenF i j k = axisElt a) → ∀ m n : Fin 4, m ≠ n →
      conjBy (orbitTab i j k n) (eTwentySevenF i j k) ≠
          conjBy (orbitTab i j k m) (eTwentySevenF i j k) ∧
        conjBy (orbitTab i j k n) (eTwentySevenF i j k) ≠
          (conjBy (orbitTab i j k m) (eTwentySevenF i j k))⁻¹ := by
  decide +kernel

theorem axis_conj_distinct : ∀ (a : Fin 6) (m n : Fin 3), m ≠ n →
    wCycle ^ (n : ℕ) * axisElt a * (wCycle ^ (n : ℕ))⁻¹ ≠
        wCycle ^ (m : ℕ) * axisElt a * (wCycle ^ (m : ℕ))⁻¹ ∧
      wCycle ^ (n : ℕ) * axisElt a * (wCycle ^ (n : ℕ))⁻¹ ≠
        (wCycle ^ (m : ℕ) * axisElt a * (wCycle ^ (m : ℕ))⁻¹)⁻¹ := by
  decide +kernel

theorem not_mem_zpowers_of_ne {X : Type*} [Group X] {u v : X} (hu : u ^ 3 = 1) (hv1 : v ≠ 1)
    (hvu : v ≠ u) (hvu' : v ≠ u⁻¹) : v ∉ Subgroup.zpowers u := by
  intro hv
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
  have hk : u ^ k = u ^ (k % 3) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 3]
    rw [zpow_add, zpow_mul, show u ^ (3 : ℤ) = 1 by exact_mod_cast hu, one_zpow, one_mul]
  have h3 : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases h3 with h | h | h
  · exact hv1 (by rw [hk, h, zpow_zero])
  · exact hvu (by rw [hk, h, zpow_one])
  · refine hvu' ?_
    rw [hk, h]
    have : u ^ (2 : ℤ) * u = 1 := by
      rw [← zpow_add_one]
      exact_mod_cast hu
    exact eq_inv_of_mul_eq_one_left this

end CFSG.RankThree.PartTwo.Sec16.Step163Alt
