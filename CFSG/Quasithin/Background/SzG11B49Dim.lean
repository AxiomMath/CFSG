module

public import CFSG.Quasithin.Background.SzG11B49Lin

public section

namespace CFSG.Quasithin.G11.SzG11S

open Module CFSG.GroupTheory.GLnTwoSplitting
open B49Aux

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

namespace B49Hyp

variable {B : LinearMap.BilinForm (ZMod 2) V} {H : Subgroup (GLV V)}
  {U : Submodule (ZMod 2) V} (hy : B49Hyp B H U)

include hy

theorem exists_common_zero [Finite V] (v v' : V) :
    ∃ z ∈ U, z ≠ 0 ∧ B v z = 0 ∧ B v' z = 0 := by
  by_contra hcon
  push Not at hcon
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  let f : U →ₗ[ZMod 2] (ZMod 2 × ZMod 2) :=
    ((B v).comp U.subtype).prod ((B v').comp U.subtype)
  have hinj : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun x hx => ?_
    by_contra hx0
    have h1 : B v (x : V) = 0 := congrArg Prod.fst hx
    have h2 : B v' (x : V) = 0 := congrArg Prod.snd hx
    have hx1 : (x : V) ≠ 0 := fun h => hx0 (Subtype.ext h)
    exact hcon x x.2 hx1 h1 h2
  have := LinearMap.finrank_le_finrank_of_injective hinj
  have h3 := hy.three
  simp [Module.finrank_prod] at this
  omega

theorem exists_sep2 [Finite V] {z z' w : V} (h : w ∉ Submodule.span (ZMod 2) {z, z'}) :
    ∃ x, B z x = 0 ∧ B z' x = 0 ∧ B w x = 1 := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  obtain ⟨χ, hχ, hχw⟩ := exists_dual_eq_one_of_notMem h
  have key : ∀ y, B ((B.toDual hy.nondegenerate).symm χ) y = χ y := fun y => by
    have := LinearMap.BilinForm.toDual_def hy.nondegenerate
      (m := (B.toDual hy.nondegenerate).symm χ) (n := y)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨(B.toDual hy.nondegenerate).symm χ, ?_, ?_, ?_⟩
  · rw [hy.symm, key]
    exact hχ z (Submodule.subset_span (by simp))
  · rw [hy.symm, key]
    exact hχ z' (Submodule.subset_span (by simp))
  · rw [hy.symm, key]
    exact hχw

theorem exists_two_zeros [Finite V] (v : V) :
    ∃ z₁ ∈ U, ∃ z₂ ∈ U, z₁ ≠ 0 ∧ z₂ ≠ 0 ∧ z₁ ≠ z₂ ∧ B v z₁ = 0 ∧ B v z₂ = 0 := by
  obtain ⟨z₁, hz₁, hz₁0, hv₁, -⟩ := hy.exists_common_zero v v
  obtain ⟨y, hy1⟩ := hy.exists_pair hz₁0
  obtain ⟨z₂, hz₂, hz₂0, hv₂, hy₂⟩ := hy.exists_common_zero v y
  refine ⟨z₁, hz₁, z₂, hz₂, hz₁0, hz₂0, ?_, hv₁, hv₂⟩
  rintro rfl
  rw [hy.symm, hy1] at hy₂
  exact one_ne_zero hy₂

theorem exists_two_forms [Finite V] {z : V} (hz0 : z ≠ 0) :
    ∃ v₁ v₂ : V, B v₁ z = 0 ∧ B v₂ z = 0 ∧ ∃ w₁ ∈ U, ∃ w₂ ∈ U,
      B v₁ w₁ = 1 ∧ B v₁ w₂ = 0 ∧ B v₂ w₁ = 0 ∧ B v₂ w₂ = 1 := by
  have hfin : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have h3 := hy.three
  obtain ⟨w₂, hw₂, hw₂'⟩ := exists_mem_notMem_of_finrank_lt (U := U)
    (S := Submodule.span (ZMod 2) {z}) (by rw [finrank_span_singleton hz0]; omega)
  obtain ⟨w₁, hw₁, hw₁'⟩ := exists_mem_notMem_of_finrank_lt (U := U)
    (S := Submodule.span (ZMod 2) {z, w₂}) ((finrank_span_pair_le z w₂).trans_lt (by omega))
  have hw₂'' : w₂ ∉ Submodule.span (ZMod 2) {z, w₁} := by
    intro hmem
    rw [span_pair_eq] at hmem
    rcases hmem with h | h | h | h
    · exact hw₂' (by rw [h]; exact Submodule.zero_mem _)
    · exact hw₂' (by rw [h]; exact Submodule.mem_span_singleton_self z)
    · exact hw₁' (by rw [← h]; exact Submodule.subset_span (by simp))
    · refine hw₁' (Submodule.mem_span_pair.2 ⟨1, 1, ?_⟩)
      rw [h]
      match_scalars <;> ring_nf
      reduce_mod_char
  obtain ⟨v₁, h1, h2, h3'⟩ := hy.exists_sep2 hw₁'
  obtain ⟨v₂, h4, h5, h6⟩ := hy.exists_sep2 hw₂''
  refine ⟨v₁, v₂, ?_, ?_, w₁, hw₁, w₂, hw₂, ?_, ?_, ?_, ?_⟩
  · rw [hy.symm]; exact h1
  · rw [hy.symm]; exact h4
  · rw [hy.symm]; exact h3'
  · rw [hy.symm]; exact h2
  · rw [hy.symm]; exact h5
  · rw [hy.symm]; exact h6

end B49Hyp

end CFSG.Quasithin.G11.SzG11S
