module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationElevenBadFiber
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Equation (11): subtracting the in-`M` and bad fibres

This is the finite-set subtraction used after the total per-region count.
The total family is partitioned into members lying in `M`, bad members
outside `M`, and good members outside `M`.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- If a family has at least `a` members, at most `m` members lie in `M`,
and at most `b` of the remaining members are bad, then it has at least
`a - m - b` good members. -/
public theorem secondCase_linearEquation11_goodFiber_count
    {G : Type u} [Group G] [Finite G]
    (P X R M : Subgroup G) (Bad : Subgroup G → Prop)
    {a m b : ℕ}
    (hTotal : a ≤ Nat.card {Y : Subgroup G //
      (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
        Y ≤ R ∧ Y ≠ X})
    (hM : Nat.card {Y : Subgroup G //
      (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
        Y ≤ R ∧ Y ≠ X ∧ Y ≤ M} ≤ m)
    (hBad : Nat.card {Y : Subgroup G //
      (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
        Y ≤ R ∧ Y ≠ X ∧ ¬ Y ≤ M ∧ Bad Y} ≤ b) :
    a - m - b ≤ Nat.card {Y : Subgroup G //
      (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
        Y ≤ R ∧ Y ≠ X ∧ ¬ Y ≤ M ∧ ¬ Bad Y} := by
  classical
  let Total : Type u := {Y : Subgroup G //
    (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
      Y ≤ R ∧ Y ≠ X}
  let InM : Type u := {Y : Subgroup G //
    (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
      Y ≤ R ∧ Y ≠ X ∧ Y ≤ M}
  let BadOut : Type u := {Y : Subgroup G //
    (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
      Y ≤ R ∧ Y ≠ X ∧ ¬ Y ≤ M ∧ Bad Y}
  let Good : Type u := {Y : Subgroup G //
    (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧
      Y ≤ R ∧ Y ≠ X ∧ ¬ Y ≤ M ∧ ¬ Bad Y}
  let f : Total → InM ⊕ BadOut ⊕ Good := fun Y =>
    if hYM : Y.1 ≤ M then
      Sum.inl ⟨Y.1, Y.2.1, Y.2.2.1, Y.2.2.2, hYM⟩
    else if hYB : Bad Y.1 then
      Sum.inr (Sum.inl ⟨Y.1, Y.2.1, Y.2.2.1, Y.2.2.2, hYM, hYB⟩)
    else
      Sum.inr (Sum.inr ⟨Y.1, Y.2.1, Y.2.2.1, Y.2.2.2, hYM, hYB⟩)
  let recover : InM ⊕ BadOut ⊕ Good → Subgroup G
    | Sum.inl Y => Y.1
    | Sum.inr (Sum.inl Y) => Y.1
    | Sum.inr (Sum.inr Y) => Y.1
  have hrecover : ∀ Y : Total, recover (f Y) = Y.1 := by
    intro Y
    by_cases hYM : Y.1 ≤ M
    · simp [f, recover, hYM]
    · by_cases hYB : Bad Y.1 <;> simp [f, recover, hYM, hYB]
  have hfinj : Function.Injective f := by
    intro Y Z hYZ
    apply Subtype.ext
    calc
      Y.1 = recover (f Y) := (hrecover Y).symm
      _ = recover (f Z) := congrArg recover hYZ
      _ = Z.1 := hrecover Z
  have hpartition : Nat.card Total ≤
      Nat.card InM + Nat.card BadOut + Nat.card Good := by
    calc
      Nat.card Total ≤ Nat.card (InM ⊕ BadOut ⊕ Good) :=
        Nat.card_le_card_of_injective f hfinj
      _ = Nat.card InM + Nat.card BadOut + Nat.card Good := by
        simp [Nat.card_sum, Nat.add_assoc]
  have hTotal' : a ≤ Nat.card Total := by simpa [Total] using hTotal
  have hM' : Nat.card InM ≤ m := by simpa [InM] using hM
  have hBad' : Nat.card BadOut ≤ b := by simpa [BadOut] using hBad
  change a - m - b ≤ Nat.card Good
  omega

end CFSG.GorensteinWalter
