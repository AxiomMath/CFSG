module

public import CFSG.Quasithin.Background.A1cModuleDefs
public import Mathlib.GroupTheory.Index

public section

namespace CFSG.Quasithin

namespace XMod

variable {A : Type*} [Group A] {Q : Type*} [CommGroup Q] [MulDistribMulAction A Q]

theorem isInv_closure {S : Set Q} (h : ∀ (a : A), ∀ s ∈ S, a • s ∈ S) :
    IsInv A (Subgroup.closure S) := by
  intro a l hl
  induction hl using Subgroup.closure_induction with
  | mem x hx => exact Subgroup.subset_closure (h a x hx)
  | one => rw [smul_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [smul_mul']; exact mul_mem hx hy
  | inv x _ hx => rw [smul_inv']; exact inv_mem hx

end XMod

theorem exists_mem_hyperplane_of_invariant_set {G : Type*} [Group G] {V : Type*} [CommGroup V]
    [MulDistribMulAction G V] (hirr : XMod.IsIrr G (⊤ : Subgroup V)) {S : Set V}
    (hS : ∀ (g : G), ∀ s ∈ S, g • s ∈ S) (hS1 : S.Nontrivial) {W : Subgroup V}
    (hW : W.index = 2) : ∃ s ∈ S, s ∈ W := by
  by_contra hcon'
  have hcon : ∀ s ∈ S, s ∉ W := fun s hs h => hcon' ⟨s, hs, h⟩
  set D : Set V := {d | ∃ s ∈ S, ∃ s' ∈ S, d = s * s'⁻¹} with hD
  have hDW : D ≤ (W : Set V) := by
    rintro _ ⟨s, hs, s', hs', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mul_mem_iff_of_index_two hW, Subgroup.inv_mem_iff]
    exact iff_of_false (hcon s hs) (hcon s' hs')
  have hDinv : ∀ (g : G), ∀ d ∈ D, g • d ∈ D := by
    rintro g _ ⟨s, hs, s', hs', rfl⟩
    exact ⟨g • s, hS g s hs, g • s', hS g s' hs', by rw [smul_mul', smul_inv']⟩
  have hJinv : XMod.IsInv G (Subgroup.closure D) := XMod.isInv_closure hDinv
  have hJW : Subgroup.closure D ≤ W := (Subgroup.closure_le W).2 hDW
  obtain ⟨s, hs, s', hs', hne⟩ := hS1
  have hmem : s * s'⁻¹ ∈ Subgroup.closure D := Subgroup.subset_closure ⟨s, hs, s', hs', rfl⟩
  have hne1 : s * s'⁻¹ ≠ 1 := fun h => hne (mul_inv_eq_one.1 h)
  rcases hirr.2.2 _ hJinv bot_le le_top with h | h
  · exact hne1 (by simpa [h] using hmem)
  · rw [h] at hJW
    have : W = ⊤ := top_le_iff.1 hJW
    rw [this, Subgroup.index_top] at hW
    omega

end CFSG.Quasithin
