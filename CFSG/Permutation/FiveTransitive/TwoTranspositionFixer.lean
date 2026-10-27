module

public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

public section

namespace CFSG

namespace FiveTransitive.TwoTranspositionFixer

open MulAction

theorem exists_four_set
    (G X : Type*) [Group G] [Fintype X] [MulAction G X]
    (a : G) (ha2 : a ^ 2 = 1) (hmoved : 4 ≤ (fixedBy X a)ᶜ.ncard) :
    ∃ s : Set X, s.ncard = 4 ∧
      (∀ x ∈ s, a • x ≠ x) ∧
      a ∈ Subgroup.normalizer (fixingSubgroup G s : Set G) := by
  classical
  have haa (x : X) : a • (a • x) = x := by
    rw [← mul_smul, ← pow_two, ha2, one_smul]
  obtain ⟨x, hx⟩ := (Set.ncard_pos (Set.toFinite _)).mp (by omega : 0 < (fixedBy X a)ᶜ.ncard)
  have hxmove : a • x ≠ x := hx
  have hex : ∃ y ∈ (fixedBy X a)ᶜ, y ∉ ({x, a • x} : Set X) := by
    by_contra! hn
    have hle := Set.ncard_le_ncard (show (fixedBy X a)ᶜ ⊆ ({x, a • x} : Set X) from hn)
    have hp : ({x, a • x} : Set X).ncard = 2 := Set.ncard_pair hxmove.symm
    omega
  obtain ⟨y, hymove, hy⟩ := hex
  have hymove' : a • y ≠ y := hymove
  have hyx : y ≠ x := fun h => hy (by simp [h])
  have hyax : y ≠ a • x := fun h => hy (by simp [h])
  have hxay : x ≠ a • y := by
    intro h
    have he := congrArg (fun z : X => a • z) h
    rw [haa] at he
    exact hyax he.symm
  have haxay : a • x ≠ a • y := fun h => hyx (smul_left_cancel a h).symm
  let e : Fin 4 ↪ X := ⟨![x, a • x, y, a • y], by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      first | rfl | exact (hxmove h).elim | exact (hxmove h.symm).elim
            | exact (hymove' h).elim | exact (hymove' h.symm).elim
            | exact (hyx h).elim | exact (hyx h.symm).elim
            | exact (hyax h).elim | exact (hyax h.symm).elim
            | exact (hxay h).elim | exact (hxay h.symm).elim
            | exact (haxay h).elim | exact (haxay h.symm).elim⟩
  let s : Set X := Set.range e
  have hs : s.ncard = 4 := by
    simpa only [s, Nat.card_fin] using Set.ncard_range_of_injective e.injective
  have hmove : ∀ z ∈ s, a • z ≠ z := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hxmove
    · exact (haa x).trans_ne hxmove.symm
    · exact hymove'
    · exact (haa y).trans_ne hymove'.symm
  have hax : ∀ z ∈ s, a • z ∈ s := by
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact ⟨1, rfl⟩
    · exact ⟨0, (haa x).symm⟩
    · exact ⟨3, rfl⟩
    · exact ⟨2, (haa y).symm⟩
  have hainv : a⁻¹ = a := (eq_inv_iff_mul_eq_one.mpr (by simpa only [pow_two] using ha2)).symm
  refine ⟨s, hs, hmove, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    rw [mem_fixingSubgroup_iff] at hu ⊢
    intro z hz
    rw [mul_smul, mul_smul, hainv, hu _ (hax z hz), haa]
  · intro hu
    rw [mem_fixingSubgroup_iff] at hu ⊢
    intro z hz
    have h := hu (a • z) (hax z hz)
    simpa only [mul_smul, inv_smul_smul, smul_left_cancel_iff] using h

end FiveTransitive.TwoTranspositionFixer

end CFSG
