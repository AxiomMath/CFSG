module

public import CFSG.Permutation.FiveTransitive.FixedFiveInvolutionGeometry

public section

namespace CFSG

namespace FiveTransitive.StableInvolutionPairs

open MulAction FixedFiveInvolutionGeometry

theorem preserves_diff
    {G X : Type*} [Group G] [MulAction G X] (b : G) (hb : b * b = 1)
    (F U : Set X) (hF : ∀ x ∈ F, b • x ∈ F) (hU : ∀ x ∈ U, b • x ∈ U) :
    ∀ x ∈ F \ U, b • x ∈ F \ U := by
  intro x hx
  refine ⟨hF x hx.1, ?_⟩
  intro h
  have hh := hU (b • x) h
  rw [← mul_smul, hb, one_smul] at hh
  exact hx.2 hh

theorem swap_pair
    {G X : Type*} [Group G] [MulAction G X] (b : G) (hb : b * b = 1)
    (x y : X) (hstable : ∀ z ∈ ({x, y} : Set X), b • z ∈ ({x, y} : Set X))
    (hne : b • x ≠ x) : b • x = y ∧ b • y = x := by
  have hm := hstable x (by simp)
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
  have hxy : b • x = y := hm.resolve_left hne
  refine ⟨hxy, ?_⟩
  rw [← hxy, ← mul_smul, hb, one_smul]

theorem fixes_singleton_intersection
    {G X : Type*} [Group G] [MulAction G X] (a b c : G)
    (hac : a * c = c * a) (hbc : b * c = c * b) (u : X)
    (hinter : fixedBy X a ∩ fixedBy X b = {u}) : c • u = u := by
  have hu : u ∈ fixedBy X a ∩ fixedBy X b := by rw [hinter]; simp
  have hc : c • u ∈ fixedBy X a ∩ fixedBy X b :=
    ⟨mem_fixedBy_smul_of_commute a c hac hu.1, mem_fixedBy_smul_of_commute b c hbc hu.2⟩
  simpa only [hinter, Set.mem_singleton_iff] using hc

end FiveTransitive.StableInvolutionPairs

end CFSG
