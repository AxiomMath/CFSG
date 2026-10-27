module

public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

open scoped commutatorElement

namespace FiveTransitive.CyclicCentralCommutatorPair

theorem unique_square_one
    {H : Type*} [Group H] [Finite H] [IsCyclic H]
    (a b : H) (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hane : a ≠ 1) (hbne : b ≠ 1) :
    a = b := by
  classical
  let _ : Fintype H := Fintype.ofFinite _
  by_contra hab
  have hcard := IsCyclic.card_pow_eq_one_le (α := H) (n := 2) (by decide)
  have hsub : ({1, a, b} : Finset H) ⊆ Finset.univ.filter (fun g : H => g ^ 2 = 1) := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rcases hg with rfl | rfl | rfl <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and, one_pow, ha, hb]
  have hc := Finset.card_le_card hsub
  have hthree : ({1, a, b} : Finset H).card = 3 := by
    simp [hab, hane.symm, hbne.symm]
  omega

theorem commutator_square
    {G : Type*} [Group G] (x y : G) (hy : y ^ 2 = 1)
    (hcentral : Commute y ⁅x, y⁆) : ⁅x, y⁆ ^ 2 = 1 := by
  have hconj : y * ⁅x, y⁆ * y⁻¹ = ⁅x, y⁆ := by
    rw [hcentral.eq, mul_assoc, mul_inv_cancel, mul_one]
  calc
    ⁅x, y⁆ ^ 2 = ⁅x, y⁆ * ⁅x, y⁆ := pow_two _
    _ = ⁅x, y⁆ * (y * ⁅x, y⁆ * y⁻¹) := congrArg (fun t => ⁅x, y⁆ * t) hconj.symm
    _ = ⁅x, y * y⁆ := by
      rw [commutatorElement_mul_right_eq_mul_conj]
      simp only [mul_assoc]
    _ = 1 := by rw [← pow_two, hy, commutatorElement_one_right]

theorem pair_eq_and_commute
    {G : Type*} [Group G]
    (Q : Subgroup G) [Finite Q] [IsCyclic Q]
    (a : Q) (ha : a ^ 2 = 1) (hane : a ≠ 1)
    (x z y : G) (hy : y ^ 2 = 1)
    (hxcentral : ∀ q : Q, Commute x q.val)
    (hycentral : ∀ q : Q, Commute y q.val)
    (hxyQ : ⁅x, y⁆ ∈ Q) (hzyQ : ⁅z, y⁆ ∈ Q)
    (hxy : ¬ Commute x y) (hzy : ¬ Commute z y) :
    ⁅x, y⁆ = a.val ∧ ⁅z, y⁆ = a.val ∧ Commute (x * z) y := by
  have hne (g : G) (hg : ¬ Commute g y) : ⁅g, y⁆ ≠ 1 :=
    fun he => hg (commutatorElement_eq_one_iff_commute.mp he)
  have heq (g : G) (hgQ : ⁅g, y⁆ ∈ Q) (hg : ¬ Commute g y) : ⁅g, y⁆ = a.val := by
    let c : Q := ⟨⁅g, y⁆, hgQ⟩
    have hc2 : c ^ 2 = 1 := Subtype.ext
      (commutator_square g y hy (hycentral c))
    have hcne : c ≠ 1 := fun h => hne g hg (congrArg Subtype.val h)
    exact congrArg Subtype.val (unique_square_one c a hc2 ha hcne hane)
  have hx := heq x hxyQ hxy
  have hz := heq z hzyQ hzy
  refine ⟨hx, hz, commutatorElement_eq_one_iff_commute.mp ?_⟩
  rw [commutatorElement_mul_left_eq_conj_mul, hx, hz, (hxcentral a).eq]
  rw [mul_assoc a.val x x⁻¹, mul_inv_cancel, mul_one]
  exact congrArg Subtype.val (by simpa only [pow_two] using ha)

end FiveTransitive.CyclicCentralCommutatorPair

end CFSG
