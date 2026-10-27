module

public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.Quasithin.G11.SzG11S.Two.Om4

open LinearMap (BilinForm)

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

theorem sq_add_of_two_eq_zero (h2 : (2 : K) = 0) (a b : K) : (a + b) ^ 2 = a ^ 2 + b ^ 2 := by
  linear_combination (a * b) * h2

theorem exists_riesz [FiniteDimensional K V] (β : BilinForm K V) (hβ : β.Nondegenerate)
    (f : Module.Dual K V) : ∃ w : V, ∀ v, β w v = f v :=
  ⟨(β.toDual hβ).symm f, fun v => LinearMap.BilinForm.apply_toDual_symm_apply f v⟩

theorem exists_adjoint [FiniteDimensional K V] (β : BilinForm K V) (hβ : β.Nondegenerate)
    (B' : BilinForm K V) : ∃ A : V →ₗ[K] V, ∀ u v, β (A v) u = B' u v := by
  refine ⟨(β.toDual hβ).symm.toLinearMap ∘ₗ B'.flip, fun u v => ?_⟩
  simp

theorem exists_twist (h2 : (2 : K) = 0) (h4 : ∀ κ : K, κ ^ 4 = κ) (β : BilinForm K V)
    (x : V →+ V) (hx : ∀ (κ : K) v, x (κ • v) = κ ^ 2 • x v) :
    ∃ B' : BilinForm K V, ∀ u v, B' u v = β (x u) (x v) ^ 2 := by
  refine ⟨LinearMap.mk₂ K (fun u v => β (x u) (x v) ^ 2) ?_ ?_ ?_ ?_, fun u v => rfl⟩
  · intro u u' v
    simp only [map_add, LinearMap.add_apply, sq_add_of_two_eq_zero h2]
  · intro κ u v
    simp only [hx, map_smul, LinearMap.smul_apply, smul_eq_mul]
    linear_combination (β (x u) (x v) ^ 2) * h4 κ
  · intro u v v'
    simp only [map_add, sq_add_of_two_eq_zero h2]
  · intro κ u v
    simp only [hx, map_smul, smul_eq_mul]
    linear_combination (β (x u) (x v) ^ 2) * h4 κ

theorem exists_scalar_of_invariant [FiniteDimensional K V]
    (h2 : (2 : K) = 0) (h4 : ∀ κ : K, κ ^ 4 = κ) (Q : V → K) (β : BilinForm K V)
    (hQ : ∀ u v, Q (u + v) = Q u + Q v + β u v)
    (hQs : ∀ (κ : K) v, Q (κ • v) = κ ^ 2 * Q v) (hβ : β.Nondegenerate)
    (x : V →+ V) (hx : ∀ (κ : K) v, x (κ • v) = κ ^ 2 • x v) (G : Set (V → V))
    (hGadd : ∀ g ∈ G, ∀ u v, g (u + v) = g u + g v)
    (hGsmul : ∀ g ∈ G, ∀ (κ : K) v, g (κ • v) = κ • g v)
    (hGsurj : ∀ g ∈ G, Function.Surjective g) (hGQ : ∀ g ∈ G, ∀ v, Q (g v) = Q v)
    (hGx : ∀ g ∈ G, ∃ g' ∈ G, ∀ v, x (g v) = g' (x v))
    (hSchur : ∀ A : V →+ V, (∀ g ∈ G, ∀ v, A (g v) = g (A v)) → ∃ κ : K, ∀ v, A v = κ • v)
    (hnot : ∀ w : V, ∃ v : V, ∀ κ : K, v ≠ κ • w) :
    ∃ μ : K, ∀ v, Q (x v) ^ 2 = μ * Q v := by
  have hβ_eq : ∀ u v, β u v = Q (u + v) + Q u + Q v := fun u v => by
    linear_combination (-1 : K) * hQ u v - (Q u + Q v) * h2
  have hβG : ∀ g ∈ G, ∀ u v, β (g u) (g v) = β u v := fun g hg u v => by
    rw [hβ_eq, ← hGadd g hg, hGQ g hg, hGQ g hg, hGQ g hg, ← hβ_eq]
  have hβsymm : ∀ u v, β u v = β v u := fun u v => by
    rw [hβ_eq, hβ_eq, add_comm u v]
    ring
  obtain ⟨β', hβ'⟩ := exists_twist h2 h4 β x hx
  have hQ' : ∀ u v, Q (x (u + v)) ^ 2 = Q (x u) ^ 2 + Q (x v) ^ 2 + β' u v := by
    intro u v
    rw [map_add, hQ, sq_add_of_two_eq_zero h2, sq_add_of_two_eq_zero h2, hβ']
  have hQ's : ∀ (κ : K) v, Q (x (κ • v)) ^ 2 = κ ^ 2 * Q (x v) ^ 2 := by
    intro κ v
    rw [hx, hQs]
    linear_combination (Q (x v) ^ 2 * (κ ^ 4 + κ)) * h4 κ
  have hQ'G : ∀ g ∈ G, ∀ v, Q (x (g v)) ^ 2 = Q (x v) ^ 2 := by
    intro g hg v
    obtain ⟨g', hg', hgg'⟩ := hGx g hg
    rw [hgg' v, hGQ g' hg']
  have hβ'G : ∀ g ∈ G, ∀ u v, β' (g u) (g v) = β' u v := by
    intro g hg u v
    obtain ⟨g', hg', hgg'⟩ := hGx g hg
    rw [hβ', hβ', hgg' u, hgg' v, hβG g' hg']
  obtain ⟨A, hA⟩ := exists_adjoint β hβ β'
  have hAG : ∀ g ∈ G, ∀ v, A (g v) = g (A v) := by
    intro g hg v
    have h0 : A (g v) - g (A v) = 0 := hβ.1 _ (fun u => by
      obtain ⟨u₀, rfl⟩ := hGsurj g hg u
      rw [map_sub, LinearMap.sub_apply, hA, hβ'G g hg, ← hA, hβG g hg, sub_self])
    exact sub_eq_zero.1 h0
  obtain ⟨μ, hμ⟩ := hSchur A.toAddMonoidHom (fun g hg v => hAG g hg v)
  have hμ' : ∀ v, A v = μ • v := hμ
  have hβ'μ : ∀ u v, β' u v = μ * β u v := by
    intro u v
    rw [← hA, hμ', map_smul, LinearMap.smul_apply, smul_eq_mul, hβsymm v u]
  obtain ⟨D, hDdef⟩ : ∃ D : V → K, ∀ v, D v = Q (x v) ^ 2 + μ * Q v := ⟨_, fun v => rfl⟩
  have hDadd : ∀ u v, D (u + v) = D u + D v := by
    intro u v
    rw [hDdef, hDdef, hDdef, hQ', hQ u v]
    linear_combination hβ'μ u v + (μ * β u v) * h2
  have hDsmul : ∀ (κ : K) v, D (κ • v) = κ ^ 2 * D v := by
    intro κ v
    rw [hDdef, hDdef, hQ's, hQs]
    ring
  have hDG : ∀ g ∈ G, ∀ v, D (g v) = D v := by
    intro g hg v
    rw [hDdef, hDdef, hQ'G g hg, hGQ g hg]
  let ℓ : Module.Dual K V :=
    { toFun := fun v => D v ^ 2
      map_add' := fun u v => by simp only [hDadd, sq_add_of_two_eq_zero h2]
      map_smul' := fun κ v => by
        simp only [hDsmul, smul_eq_mul, RingHom.id_apply]
        linear_combination (D v ^ 2) * h4 κ }
  have hℓ : ∀ v, ℓ v = D v ^ 2 := fun v => rfl
  obtain ⟨w, hw⟩ := exists_riesz β hβ ℓ
  have hgw : ∀ g ∈ G, g w = w := by
    intro g hg
    have h0 : g w - w = 0 := hβ.1 _ (fun u => by
      obtain ⟨u₀, rfl⟩ := hGsurj g hg u
      rw [map_sub, LinearMap.sub_apply, hβG g hg, hw, hw, hℓ, hℓ, hDG g hg, sub_self])
    exact sub_eq_zero.1 h0
  obtain ⟨κ₂, hκ₂⟩ := hSchur (LinearMap.smulRight ℓ w).toAddMonoidHom (fun g hg v => by
    show ℓ (g v) • w = g (ℓ v • w)
    rw [hℓ, hDG g hg, hGsmul g hg, hgw g hg, hℓ])
  have hℓ0 : ∀ v, D v ^ 2 = 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨v₀, hv₀⟩ := hcon
    have hw0 : w ≠ 0 := by
      intro hw0
      have := hw v₀
      rw [hw0, map_zero, LinearMap.zero_apply, hℓ] at this
      exact hv₀ this.symm
    have hκ : ∀ v, ℓ v • w = κ₂ • v := hκ₂
    by_cases hκ0 : κ₂ = 0
    · have := hκ v₀
      rw [hκ0, zero_smul, smul_eq_zero] at this
      rcases this with h | h
      · exact hv₀ (by rw [← hℓ]; exact h)
      · exact hw0 h
    · obtain ⟨v, hv⟩ := hnot w
      apply hv (κ₂⁻¹ * ℓ v)
      rw [mul_smul, hκ v, smul_smul, inv_mul_cancel₀ hκ0, one_smul]
  refine ⟨μ, fun v => ?_⟩
  have h0 : D v = 0 := (pow_eq_zero_iff two_ne_zero).1 (hℓ0 v)
  rw [hDdef] at h0
  linear_combination h0 - (μ * Q v) * h2

end CFSG.Quasithin.G11.SzG11S.Two.Om4
