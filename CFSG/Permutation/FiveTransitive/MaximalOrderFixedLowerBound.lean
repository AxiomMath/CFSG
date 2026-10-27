module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.SetLike.Fintype

public section

namespace CFSG

namespace FiveTransitive.MaximalOrderFixedLowerBound

open MulAction

theorem exists_maximal
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (p m : ℕ) (R : Subgroup G) (hR : IsPGroup p R)
    (hRfix : m ≤ Nat.card (fixedPoints R X)) :
    ∃ U : Subgroup G, IsPGroup p U ∧ m ≤ Nat.card (fixedPoints U X) ∧
      Nat.card R ≤ Nat.card U ∧
      ∀ T : Subgroup G, IsPGroup p T → m ≤ Nat.card (fixedPoints T X) →
        Nat.card T ≤ Nat.card U := by
  classical
  let _ : Fintype (Subgroup G) := Fintype.ofFinite _
  let s := Finset.univ.filter (fun U : Subgroup G =>
    IsPGroup p U ∧ m ≤ Nat.card (fixedPoints U X))
  have hs : s.Nonempty := ⟨R, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hR, hRfix⟩⟩
  obtain ⟨U, hU, hmax⟩ := Finset.exists_max_image s (fun U : Subgroup G => Nat.card U) hs
  have hU' := (Finset.mem_filter.mp hU).2
  have hglobal : ∀ T : Subgroup G, IsPGroup p T → m ≤ Nat.card (fixedPoints T X) →
      Nat.card T ≤ Nat.card U := by
    intro T hT hfix
    exact hmax T (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hT, hfix⟩)
  exact ⟨U, hU'.1, hU'.2, hglobal R hR hRfix, hglobal⟩

end FiveTransitive.MaximalOrderFixedLowerBound

end CFSG
