module

public import Mathlib.GroupTheory.Sylow
import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup
open scoped Pointwise

theorem card_sylow_seven {X : Type*} [Group X] [Finite X] {r : ℕ} (hcard : Nat.card X = 49 * r)
    (hr : ¬ 7 ∣ r) (Q : Sylow 7 X) : Nat.card (Q : Subgroup X) = 49 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [Sylow.card_eq_multiplicity, hcard]
  have hr0 : r ≠ 0 := by
    rintro rfl
    have := Nat.card_pos (α := X)
    simp at hcard
    omega
  rw [Nat.factorization_mul (by norm_num) hr0]
  have h1 : (49 : ℕ).factorization 7 = 2 := by
    rw [show (49 : ℕ) = 7 ^ 2 by norm_num, Nat.Prime.factorization_pow (by norm_num)]
    simp
  have h2 : r.factorization 7 = 0 := Nat.factorization_eq_zero_of_not_dvd hr
  simp [h1, h2]

theorem cyclic_sylow_seven {X : Type*} [Group X] [Finite X] {r : ℕ} (hcard : Nat.card X = 49 * r)
    (hr : ¬ 7 ∣ r) {x : X} (hx : orderOf x = 49) :
    ∀ R : Subgroup X, IsPGroup 7 R → IsCyclic ↥R ∧ Nat.card ↥R ≤ 49 := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro R hR
  have hZ : IsPGroup 7 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers, hx]
    norm_num
  obtain ⟨Q₀, hZQ₀⟩ := hZ.exists_le_sylow
  have hQ₀card := card_sylow_seven hcard hr Q₀
  have hZcard : Nat.card (Subgroup.zpowers x) = 49 := by rw [Nat.card_zpowers, hx]
  have hQ₀eq : (Q₀ : Subgroup X) = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge hZQ₀ (by rw [hQ₀card, hZcard])).symm
  have hQ₀cyc : IsCyclic ↥(Q₀ : Subgroup X) := by
    rw [hQ₀eq]
    infer_instance
  obtain ⟨Q, hRQ⟩ := hR.exists_le_sylow
  have hQcyc : IsCyclic ↥(Q : Subgroup X) :=
    ((Sylow.equiv Q₀ Q).isCyclic).1 hQ₀cyc
  have hQcard := card_sylow_seven hcard hr Q
  refine ⟨?_, ?_⟩
  · have e : ↥R ≃* ↥(R.subgroupOf (Q : Subgroup X)) := (Subgroup.subgroupOfEquivOfLe hRQ).symm
    have : IsCyclic ↥(R.subgroupOf (Q : Subgroup X)) := Subgroup.isCyclic _
    exact (e.isCyclic).2 this
  · calc Nat.card ↥R ≤ Nat.card ↥(Q : Subgroup X) := Subgroup.card_le_of_le hRQ
      _ = 49 := hQcard

end CFSG.RankThree.PartOne.TAIL
