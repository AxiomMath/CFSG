module

public import CFSG.Permutation.FiveTransitive.InvolutiveAutomorphismBound
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.NormNum.Pow

public section

namespace CFSG

namespace FiveTransitive.RegularOrbitAutomorphism

open MulAction

theorem fixed_card_eq
    (Q X : Type*) [Group Q] [Finite Q] [Finite X] [MulAction Q X]
    (f : Q →* Q) (a : X → X) (x : X)
    (hax : a x = x)
    (hcompat : ∀ q : Q, ∀ y : X, a (q • y) = f q • a y)
    (hfree : ∀ q : Q, q • x = x → q = 1) :
    Nat.card {q : Q // f q = q} =
      Nat.card {y : X // y ∈ orbit Q x ∧ a y = y} := by
  have hinj : Function.Injective (fun q : Q => q • x) := by
    intro q r h
    change q • x = r • x at h
    have heq : (r⁻¹ * q) • x = x := by
      rw [mul_smul, h, inv_smul_smul]
    have heqone := hfree (r⁻¹ * q) heq
    exact (inv_mul_eq_one.mp heqone).symm
  let e : {q : Q // f q = q} → {y : X // y ∈ orbit Q x ∧ a y = y} :=
    fun q => ⟨q.val • x, ⟨mem_orbit_iff.mpr ⟨q, rfl⟩, by
      rw [hcompat, hax, q.property]⟩⟩
  apply Nat.card_congr (Equiv.ofBijective e ?_)
  constructor
  · intro q r h
    exact Subtype.ext (hinj (congrArg Subtype.val h))
  · rintro ⟨y, hy, hay⟩
    obtain ⟨q, hq⟩ := mem_orbit_iff.mp hy
    have hfq : f q = q := hinj (by
      change f q • x = q • x
      calc
        f q • x = f q • a x := by rw [hax]
        _ = a (q • x) := (hcompat q x).symm
        _ = q • x := by rw [hq, hay])
    exact ⟨⟨q, hfq⟩, Subtype.ext hq⟩

theorem card_le_orbit_fixed_sq
    (Q X : Type*) [CommGroup Q] [Finite Q] [Finite X] [MulAction Q X]
    (f : Q →* Q) (hf : Function.Involutive f) (h2 : ∀ q : Q, q * q = 1)
    (a : X → X) (x : X) (hax : a x = x)
    (hcompat : ∀ q : Q, ∀ y : X, a (q • y) = f q • a y)
    (hfree : ∀ q : Q, q • x = x → q = 1) :
    Nat.card Q ≤ (Nat.card {y : X // y ∈ orbit Q x ∧ a y = y}) ^ 2 := by
  rw [← fixed_card_eq Q X f a x hax hcompat hfree]
  exact InvolutiveAutomorphismBound.card_le_fixed_sq Q f hf h2

end FiveTransitive.RegularOrbitAutomorphism

end CFSG
