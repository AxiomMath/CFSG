module

public import CFSG.Permutation.FiveTransitive.FreeActionTransporterCount
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitPermutation
public import CFSG.Permutation.FiveTransitive.CosetCountSaturation
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Linarith.Frontend
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG

namespace FiveTransitive.NormalizerCosetCount

open MulAction NormalizerOrbitPermutation
open scoped BigOperators

theorem fixed_sum
    {G Y : Type*} [Group G] [Finite Y] [MulAction G Y]
    (Q : Subgroup G) [Fintype Q]
    (hfree : ∀ (q : Q) (y : Y), q • y = y → q = 1)
    (x : Subgroup.normalizer (Q : Set G)) :
    (∑ q : Q, Nat.card (fixedBy Y (q.val * x.val))) =
      Nat.card Q * Nat.card (Function.fixedPoints (orbitPerm (Y := Y) Q x)) := by
  change (∑ q : Q, Nat.card {y : Y // (q.val * x.val) • y = y}) = _
  have hsum := FreeActionTransporterCount.sum_card_transporter hfree (fun y : Y => x.val • y)
  change (∑ q : Q, Nat.card {y : Y // q.val • (x.val • y) = y}) = _ at hsum
  have he : {y : Y // ∃ q : Q, q • (x.val • y) = y} ≃
      {y : Y // orbitPerm Q x (Quotient.mk'' y) = Quotient.mk'' y} :=
    Equiv.subtypeEquivRight fun y => by
      rw [fixed_iff_transporter]
      constructor <;> rintro ⟨q, hq⟩ <;> refine ⟨q, ?_⟩
      · change q.val • (x.val • y) = y at hq
        simpa only [mul_smul] using hq
      · change q.val • (x.val • y) = y
        simpa only [mul_smul] using hq
  calc
    _ = Nat.card {y : Y // ∃ q : Q, q • (x.val • y) = y} := by
      simpa only [mul_smul] using hsum
    _ = Nat.card {y : Y // orbitPerm Q x (Quotient.mk'' y) = Quotient.mk'' y} :=
      Nat.card_congr he
    _ = _ := FreeActionTransporterCount.card_orbit_preimage hfree
      (fun O => orbitPerm Q x O = O)

theorem orbit_bound
    {G Y : Type*} [Group G] [Finite Y] [MulAction G Y]
    (Q : Subgroup G) [Fintype Q]
    (hfree : ∀ (q : Q) (y : Y), q • y = y → q = 1)
    (x : Subgroup.normalizer (Q : Set G)) (b : ℕ)
    (hbound : ∀ q : Q, Nat.card (fixedBy Y (q.val * x.val)) ≤ b) :
    Nat.card (Function.fixedPoints (orbitPerm (Y := Y) Q x)) ≤ b := by
  have hs := Finset.sum_le_sum (fun (q : Q) (_ : q ∈ Finset.univ) => hbound q)
  rw [fixed_sum Q hfree x] at hs
  simp only [Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul,
    ← Nat.card_eq_fintype_card] at hs
  have hp : 0 < Nat.card Q := Nat.card_pos
  nlinarith

theorem saturated_fixed_count
    {G Y : Type*} [Group G] [Finite Y] [MulAction G Y]
    (Q : Subgroup G) [Fintype Q]
    (hfree : ∀ (q : Q) (y : Y), q • y = y → q = 1)
    (x : Subgroup.normalizer (Q : Set G)) (b : ℕ)
    (hbound : ∀ q : Q, Nat.card (fixedBy Y (q.val * x.val)) ≤ b)
    (horbits : Nat.card (Function.fixedPoints (orbitPerm (Y := Y) Q x)) = b) :
    ∀ q : Q, Nat.card (fixedBy Y (q.val * x.val)) = b := by
  apply CosetCountSaturation.eq_of_sum_eq _ b hbound
  rw [fixed_sum Q hfree x, horbits]

end FiveTransitive.NormalizerCosetCount

end CFSG
