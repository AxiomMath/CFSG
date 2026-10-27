module

public import CFSG.Quasithin.EmptyFaithful.S153NBb1

public section

namespace CFSG.Quasithin.S153N.Bb

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

section ActFacts

variable {V E : Subgroup G} [IsMulCommutative ↥V]
  (hN : Subgroup.normalizer (E : Set G) ≤ Subgroup.normalizer (V : Set G))

theorem actN_cube_apply (g : ↥(Subgroup.normalizer (E : Set G)))
    (h : (g : G) ^ 3 ∈ Subgroup.centralizer (V : Set G)) (u : Qt V E) :
    actN V E hN g (actN V E hN g (actN V E hN g u)) = u := by
  have h1 : actN V E hN (g ^ 3) = 1 := by
    refine actN_eq_one_of hN (g ^ 3) fun v hv => ?_
    have h2 : v * (g : G) ^ 3 = (g : G) ^ 3 * v := Subgroup.mem_centralizer_iff.mp h v hv
    have h3 : ((g ^ 3 : ↥(Subgroup.normalizer (E : Set G))) : G) = (g : G) ^ 3 := rfl
    rw [h3, ← h2]
    simp
  have h4 : actN V E hN g ^ 3 = 1 := by rw [← map_pow]; exact h1
  have := congrArg (fun φ : MulAut (Qt V E) => φ u) h4
  simpa [pow_succ, MulAut.mul_apply] using this

theorem actN_sq_apply (g : ↥(Subgroup.normalizer (E : Set G)))
    (h : ∀ v ∈ V, ((g : G) * g) * v * ((g : G) * g)⁻¹ * v⁻¹ ∈ E) (u : Qt V E) :
    actN V E hN g (actN V E hN g u) = u := by
  have h1 : actN V E hN (g * g) = 1 := actN_eq_one_of hN (g * g) h
  rw [map_mul] at h1
  have := congrArg (fun φ : MulAut (Qt V E) => φ u) h1
  simpa [MulAut.mul_apply] using this

theorem actN_comm_apply (g h : ↥(Subgroup.normalizer (E : Set G)))
    (hc : ∀ v ∈ V, ((g : G) * h * (g : G)⁻¹ * (h : G)⁻¹) * v *
      ((g : G) * h * (g : G)⁻¹ * (h : G)⁻¹)⁻¹ * v⁻¹ ∈ E) (u : Qt V E) :
    actN V E hN g (actN V E hN h u) = actN V E hN h (actN V E hN g u) := by
  have h1 : actN V E hN (g * h * g⁻¹ * h⁻¹) = 1 := actN_eq_one_of hN _ hc
  rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  have h2 : actN V E hN g * actN V E hN h = actN V E hN h * actN V E hN g := by
    have h3 : actN V E hN g * actN V E hN h * (actN V E hN g)⁻¹ = actN V E hN h :=
      mul_inv_eq_one.mp h1
    exact mul_inv_eq_iff_eq_mul.mp h3
  exact congrArg (fun φ : MulAut (Qt V E) => φ u) h2

theorem actN_rel_apply (a b : ↥(Subgroup.normalizer (E : Set G)))
    (hrel : ∀ v ∈ V, ((b : G) * a * (b : G)⁻¹ * a) * v * ((b : G) * a * (b : G)⁻¹ * a)⁻¹ * v⁻¹ ∈ E)
    (ha3 : ∀ u : Qt V E, actN V E hN a (actN V E hN a (actN V E hN a u)) = u) (u : Qt V E) :
    actN V E hN b (actN V E hN a u) = actN V E hN a (actN V E hN a (actN V E hN b u)) := by
  have h1 : actN V E hN (b * a * b⁻¹ * a) = 1 := actN_eq_one_of hN _ hrel
  rw [map_mul, map_mul, map_mul, map_inv] at h1
  have hpow : actN V E hN a * actN V E hN a * actN V E hN a = 1 := by
    ext x
    simpa [MulAut.mul_apply] using ha3 x
  have h2 : actN V E hN b * actN V E hN a = actN V E hN a * actN V E hN a * actN V E hN b := by
    have h3 : actN V E hN b * actN V E hN a * (actN V E hN b)⁻¹ = (actN V E hN a)⁻¹ :=
      eq_inv_of_mul_eq_one_left h1
    have h4 : (actN V E hN a)⁻¹ = actN V E hN a * actN V E hN a := (eq_inv_of_mul_eq_one_left hpow).symm
    rw [h4] at h3
    exact mul_inv_eq_iff_eq_mul.mp h3
  exact congrArg (fun φ : MulAut (Qt V E) => φ u) h2

end ActFacts
theorem comm_mem_of_centralizer {V E : Subgroup G} {x : G}
    (h : x ∈ Subgroup.centralizer (V : Set G)) : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ E := by
  intro v hv
  have h1 : v * x = x * v := Subgroup.mem_centralizer_iff.mp h v hv
  have : x * v * x⁻¹ * v⁻¹ = 1 := by
    rw [← h1]
    group
  rw [this]
  exact E.one_mem

end CFSG.Quasithin.S153N.Bb
