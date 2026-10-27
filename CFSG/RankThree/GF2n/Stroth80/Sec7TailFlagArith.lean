module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Group
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup

theorem perfect_le_of_out_solvable {Y : Type} [Group Y] [Finite Y] {S E : Subgroup Y} [S.Normal]
    (hC : ∀ c : Y, (∀ s ∈ S, c * s = s * c) → c = 1)
    (hOut : ∀ P : Subgroup (MulAut ↥S), commutator ↥P = ⊤ →
      P ≤ (MulAut.conj : ↥S →* MulAut ↥S).range)
    (hE : commutator ↥E = ⊤) : E ≤ S := by
  set g : ↥E →* MulAut ↥S := (MulAut.conjNormal (H := S)).comp E.subtype
  have hperf : ⁅g.range, g.range⁆ = g.range := by
    have h1 := map_commutator_eq _ g
    rw [hE, ← MonoidHom.range_eq_map] at h1
    exact h1.symm
  have hP : commutator ↥(g.range) = ⊤ := by
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Subgroup.map_subtype_commutator, hperf, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  intro e he
  have hmem : MulAut.conjNormal (H := S) e ∈ g.range :=
    MonoidHom.mem_range.mpr ⟨⟨e, he⟩, rfl⟩
  obtain ⟨s, hs⟩ := MonoidHom.mem_range.mp (hOut _ hP hmem)
  have hk : ∀ x : ↥S, (s : Y) * (x : Y) * (s : Y)⁻¹ = e * (x : Y) * e⁻¹ := by
    intro x
    have h1 := congrArg (fun φ : MulAut ↥S => ((φ x : ↥S) : Y)) hs
    simpa [MulAut.conj_apply, MulAut.conjNormal_apply] using h1
  have hcx : ∀ x ∈ S, (s : Y)⁻¹ * e * x = x * ((s : Y)⁻¹ * e) := by
    intro x hx
    have hk' : (s : Y) * x * (s : Y)⁻¹ = e * x * e⁻¹ := hk ⟨x, hx⟩
    have h2 : e * x = (s : Y) * x * (s : Y)⁻¹ * e := by
      rw [hk']
      group
    rw [mul_assoc, h2]
    group
  have hse : (s : Y) = e := inv_mul_eq_one.mp (hC ((s : Y)⁻¹ * e) hcx)
  rw [← hse]
  exact s.2

end CFSG.RankThree.GF2n.Stroth80
