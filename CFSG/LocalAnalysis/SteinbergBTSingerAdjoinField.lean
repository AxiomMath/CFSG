module

public import Mathlib.RingTheory.LittleWedderburn
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific

public section

namespace CFSG.LocalAnalysis.SteinbergBT

variable {F W : Type*} [Field F] [AddCommGroup W] [Module F W]

theorem commute_of_mem_adjoin_singleton {T k : Module.End F W}
    (hk : k ∈ Algebra.adjoin F {T}) : Commute T k := by
  have hle : Algebra.adjoin F {T} ≤ Subalgebra.centralizer F {T} :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2
      ((Subalgebra.mem_centralizer_iff F).2 fun g hg => by rw [Set.mem_singleton_iff.1 hg]))
  exact (Subalgebra.mem_centralizer_iff F).1 (hle hk) T (Set.mem_singleton T)

theorem injective_of_mem_adjoin_singleton {T k : Module.End F W}
    (htrans : ∀ w w' : W, w ≠ 0 → w' ≠ 0 → ∃ j : ℕ, (T ^ j) w = w')
    (hk : k ∈ Algebra.adjoin F {T}) (hk0 : k ≠ 0) : Function.Injective k := by
  refine (injective_iff_map_eq_zero k).2 fun w hw => ?_
  by_contra hw0
  refine hk0 (LinearMap.ext fun w' => ?_)
  by_cases hw' : w' = 0
  · rw [hw', map_zero, LinearMap.zero_apply]
  · obtain ⟨j, rfl⟩ := htrans w w' hw0 hw'
    have hc : Commute (T ^ j) k := (commute_of_mem_adjoin_singleton hk).pow_left j
    rw [LinearMap.zero_apply, ← Module.End.mul_apply, ← hc.eq, Module.End.mul_apply, hw,
      map_zero]

theorem noZeroDivisors_adjoin_singleton {T : Module.End F W}
    (htrans : ∀ w w' : W, w ≠ 0 → w' ≠ 0 → ∃ j : ℕ, (T ^ j) w = w') :
    NoZeroDivisors (Algebra.adjoin F {T}) := by
  refine ⟨fun {a b} hab => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  right
  have hinj := injective_of_mem_adjoin_singleton htrans a.2 fun h => ha (Subtype.ext h)
  apply Subtype.ext
  refine LinearMap.ext fun w => hinj ?_
  have h : ((a * b : Algebra.adjoin F {T}) : Module.End F W) w = 0 := by
    rw [hab]
    rfl
  rw [Subalgebra.coe_mul, Module.End.mul_apply] at h
  rw [h, Subalgebra.coe_zero, LinearMap.zero_apply, map_zero]

theorem isField_adjoin_singleton [Finite W] [Nontrivial W] {T : Module.End F W}
    (htrans : ∀ w w' : W, w ≠ 0 → w' ≠ 0 → ∃ j : ℕ, (T ^ j) w = w') :
    IsField (Algebra.adjoin F {T}) := by
  have := noZeroDivisors_adjoin_singleton htrans
  have : IsDomain (Algebra.adjoin F {T}) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End F W) :=
    Finite.of_injective (fun f : Module.End F W => (f : W → W)) DFunLike.coe_injective
  exact Finite.isDomain_to_isField _

theorem bijective_apply_adjoin_singleton {T : Module.End F W}
    (htrans : ∀ w w' : W, w ≠ 0 → w' ≠ 0 → ∃ j : ℕ, (T ^ j) w = w') {w₀ : W} (hw₀ : w₀ ≠ 0) :
    Function.Bijective fun k : Algebra.adjoin F {T} => (k : Module.End F W) w₀ := by
  refine ⟨fun a b hab => ?_, fun w => ?_⟩
  · by_contra hne
    have hsub : (a : Module.End F W) - b ∈ Algebra.adjoin F {T} := sub_mem a.2 b.2
    have hne0 : (a : Module.End F W) - b ≠ 0 := sub_ne_zero.2 fun h => hne (Subtype.ext h)
    refine hw₀ (injective_of_mem_adjoin_singleton htrans hsub hne0 ?_)
    rw [LinearMap.sub_apply, map_zero]
    exact sub_eq_zero.2 hab
  · by_cases hw : w = 0
    · refine ⟨0, ?_⟩
      rw [hw]
      exact LinearMap.zero_apply w₀
    · obtain ⟨j, hj⟩ := htrans w₀ w hw₀ hw
      exact ⟨⟨T ^ j, pow_mem (Algebra.subset_adjoin (Set.mem_singleton T)) j⟩, hj⟩

theorem exists_pow_eq_of_mem_adjoin_singleton [Nontrivial W] {T k : Module.End F W}
    (htrans : ∀ w w' : W, w ≠ 0 → w' ≠ 0 → ∃ j : ℕ, (T ^ j) w = w')
    (hk : k ∈ Algebra.adjoin F {T}) (hk0 : k ≠ 0) : ∃ j : ℕ, T ^ j = k := by
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have hkw : k w₀ ≠ 0 := fun h =>
    hw₀ (injective_of_mem_adjoin_singleton htrans hk hk0 (h.trans (map_zero k).symm))
  obtain ⟨j, hj⟩ := htrans w₀ (k w₀) hw₀ hkw
  refine ⟨j, congrArg Subtype.val ((bijective_apply_adjoin_singleton htrans hw₀).1
    (a₁ := ⟨T ^ j, pow_mem (Algebra.subset_adjoin (Set.mem_singleton T)) j⟩) (a₂ := ⟨k, hk⟩) hj)⟩

end CFSG.LocalAnalysis.SteinbergBT
