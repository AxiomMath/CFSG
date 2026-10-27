module

public import CFSG.RankThree.GF2n.Smith81.S81VRankOne
public import CFSG.RankThree.GF2n.Smith81.S81VRootExp

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open Module

namespace RankOneData

variable {K : Type} [Field K] [Fintype K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  (D : RankOneData K V)

def S (v₀ : V) : Submodule K V := Submodule.span K (Set.range fun t : K => D.X t (D.s v₀))

private theorem X_eq_mul_ρ (t : K) : ∃ m₁ m₂ : D.N, D.X t = D.ρ m₁ * D.ρ m₂ := by
  obtain ⟨n', -, hρ⟩ := D.ρ_eq_ker_mul_X (t • D.n₁)
  have hτt : D.τ (t • D.n₁) = t := by rw [map_smul, D.τ_n₁, smul_eq_mul, mul_one]
  rw [hτt] at hρ
  refine ⟨n', t • D.n₁, ?_⟩
  calc D.X t = (D.ρ n' * D.ρ n') * D.X t := by rw [D.ρ_mul_self, one_mul]
    _ = D.ρ n' * (D.ρ n' * D.X t) := by rw [mul_assoc]
    _ = D.ρ n' * D.ρ (t • D.n₁) := by rw [hρ]

private theorem ρ_comm_X (n : D.N) (t : K) : D.ρ n * D.X t = D.X t * D.ρ n := by
  obtain ⟨m₁, m₂, h⟩ := D.X_eq_mul_ρ t
  calc D.ρ n * D.X t = D.ρ n * (D.ρ m₁ * D.ρ m₂) := by rw [h]
    _ = (D.ρ n * D.ρ m₁) * D.ρ m₂ := by rw [mul_assoc]
    _ = (D.ρ m₁ * D.ρ n) * D.ρ m₂ := by rw [D.ρ_comm n m₁]
    _ = D.ρ m₁ * (D.ρ n * D.ρ m₂) := by rw [mul_assoc]
    _ = D.ρ m₁ * (D.ρ m₂ * D.ρ n) := by rw [D.ρ_comm n m₂]
    _ = (D.ρ m₁ * D.ρ m₂) * D.ρ n := by rw [mul_assoc]
    _ = D.X t * D.ρ n := by rw [h]

theorem rho_eq_X_on_S [FiniteDimensional K V] (hfix : finrank K D.fix = 1) {v₀ : V}
    (hv₀ : v₀ ∈ D.fix) (hv0 : v₀ ≠ 0) {z : V} (hz : z ∈ D.S v₀) (n : D.N) :
    D.ρ n z = D.X (D.τ n) z := by
  obtain ⟨n', hτ', hρ⟩ := D.ρ_eq_ker_mul_X n
  have hfixS : ∀ w ∈ D.S v₀, D.ρ n' w = w := by
    intro w hw
    have hw' : w ∈ Submodule.span K (Set.range fun t : K => D.X t (D.s v₀)) := hw
    clear hw
    induction hw' using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      calc D.ρ n' (D.X t (D.s v₀)) = (D.ρ n' * D.X t) (D.s v₀) := by rw [LinearEquiv.mul_apply]
        _ = (D.X t * D.ρ n') (D.s v₀) := by rw [D.ρ_comm_X n' t]
        _ = D.X t (D.ρ n' (D.s v₀)) := by rw [LinearEquiv.mul_apply]
        _ = D.X t (D.s v₀) := by rw [D.ker_fixes_sv hfix hv₀ hv0 hτ']
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy]
    | smul a x _ hx => rw [map_smul, hx]
  calc D.ρ n z = (D.ρ n' * D.X (D.τ n)) z := by rw [hρ]
    _ = (D.X (D.τ n) * D.ρ n') z := by rw [D.ρ_comm_X n' (D.τ n)]
    _ = D.X (D.τ n) (D.ρ n' z) := by rw [LinearEquiv.mul_apply]
    _ = D.X (D.τ n) z := by rw [hfixS z hz]

theorem mem_fix_of_X_fixed [FiniteDimensional K V] (hfix : finrank K D.fix = 1) {v₀ : V}
    (hv₀ : v₀ ∈ D.fix) (hv0 : v₀ ≠ 0) {z : V} (hz : z ∈ D.S v₀) (hX : ∀ t : K, D.X t z = z) :
    z ∈ D.fix :=
  D.mem_fix.2 fun n => by rw [D.rho_eq_X_on_S hfix hv₀ hv0 hz n, hX]

theorem E_apply_mem_S {f : ℕ} {v₀ : V} {E : Finset (Fin f) → (V →ₗ[K] V)}
    (hEspan : ∀ B, E B ∈ Submodule.span K (Set.range fun t : K => (D.X t : V →ₗ[K] V)))
    (B : Finset (Fin f)) : E B (D.s v₀) ∈ D.S v₀ := by
  have key : ∀ y ∈ Submodule.span K (Set.range fun t : K => (D.X t : V →ₗ[K] V)),
      y (D.s v₀) ∈ D.S v₀ := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      refine Submodule.subset_span ⟨t, ?_⟩
      show D.X t (D.s v₀) = (D.X t : V →ₗ[K] V) (D.s v₀)
      rw [LinearEquiv.coe_coe]
    | zero => rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [LinearMap.add_apply]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx => rw [LinearMap.smul_apply]; exact Submodule.smul_mem _ a hx
  exact key _ (hEspan B)

theorem torus_conj_E {f : ℕ} (hf : Fintype.card K = 2 ^ f) {E : Finset (Fin f) → (V →ₗ[K] V)}
    (hE : ∀ t : K, (D.X t : V →ₗ[K] V) = ∑ B : Finset (Fin f), t ^ bitSum B • E B) (c : Kˣ)
    (B : Finset (Fin f)) (v : V) :
    D.a (D.d c) (E B v) = ((c : K) ^ (2 * bitSum B)) • E B (D.a (D.d c) v) := by
  have hcomm : ∀ (t : K) (w : V),
      D.a (D.d c) (D.X t w) = D.X ((c : K) ^ 2 * t) (D.a (D.d c) w) := by
    intro t w
    have h2 : D.a (D.d c) * D.X t = D.X ((c : K) ^ 2 * t) * D.a (D.d c) := by
      rw [← D.torus_conj_X c t, inv_mul_cancel_right]
    have h3 := congrArg (fun e : V ≃ₗ[K] V => e w) h2
    simpa only [LinearEquiv.mul_apply] using h3
  have hpow : ∀ (t : K) (B' : Finset (Fin f)),
      t ^ bitSum B' * (c : K) ^ (2 * bitSum B') = ((c : K) ^ 2 * t) ^ bitSum B' := by
    intro t B'
    rw [pow_mul, mul_pow, mul_comm]
  have hsum : ∀ t : K, ∑ B' : Finset (Fin f), t ^ bitSum B' •
      ((D.a (D.d c) : V →ₗ[K] V) * E B' -
        ((c : K) ^ (2 * bitSum B')) • (E B' * (D.a (D.d c) : V →ₗ[K] V))) = 0 := by
    intro t
    apply LinearMap.ext
    intro w
    have hXt : D.X t w = ∑ B' : Finset (Fin f), t ^ bitSum B' • E B' w := by
      simpa only [LinearEquiv.coe_coe, LinearMap.sum_apply, LinearMap.smul_apply] using
        LinearMap.congr_fun (hE t) w
    have hXct : D.X ((c : K) ^ 2 * t) (D.a (D.d c) w) =
        ∑ B' : Finset (Fin f), ((c : K) ^ 2 * t) ^ bitSum B' • E B' (D.a (D.d c) w) := by
      simpa only [LinearEquiv.coe_coe, LinearMap.sum_apply, LinearMap.smul_apply] using
        LinearMap.congr_fun (hE ((c : K) ^ 2 * t)) (D.a (D.d c) w)
    have e1 : ∑ B' : Finset (Fin f), t ^ bitSum B' • D.a (D.d c) (E B' w) =
        D.a (D.d c) (D.X t w) := by
      rw [hXt, map_sum]
      exact Finset.sum_congr rfl fun B' _ => (map_smul _ _ _).symm
    have e2 : ∑ B' : Finset (Fin f), ((c : K) ^ 2 * t) ^ bitSum B' • E B' (D.a (D.d c) w) =
        D.a (D.d c) (D.X t w) := by
      rw [← hXct, hcomm]
    have key : ∀ B' : Finset (Fin f),
        (t ^ bitSum B' • ((D.a (D.d c) : V →ₗ[K] V) * E B' -
          ((c : K) ^ (2 * bitSum B')) • (E B' * (D.a (D.d c) : V →ₗ[K] V)))) w =
          t ^ bitSum B' • D.a (D.d c) (E B' w) -
            ((c : K) ^ 2 * t) ^ bitSum B' • E B' (D.a (D.d c) w) := by
      intro B'
      simp only [LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply,
        LinearEquiv.coe_coe, smul_sub, smul_smul, hpow]
    simp only [LinearMap.sum_apply, key, LinearMap.zero_apply]
    rw [Finset.sum_sub_distrib, e1, e2, sub_self]
  have hF := rootExpansion_unique hf
    (fun B' => (D.a (D.d c) : V →ₗ[K] V) * E B' -
      ((c : K) ^ (2 * bitSum B')) • (E B' * (D.a (D.d c) : V →ₗ[K] V))) hsum B
  have h4 := LinearMap.congr_fun hF v
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearEquiv.coe_coe, LinearMap.zero_apply] at h4
  exact sub_eq_zero.1 h4

theorem torus_eigen_E {f : ℕ} (hf : Fintype.card K = 2 ^ f) {E : Finset (Fin f) → (V →ₗ[K] V)}
    (hE : ∀ t : K, (D.X t : V →ₗ[K] V) = ∑ B : Finset (Fin f), t ^ bitSum B • E B) {v₀ : V}
    {k : ℕ} (hk : ∀ c : Kˣ, D.a (D.d c) v₀ = (c : K) ^ k • v₀) (c : Kˣ) (B : Finset (Fin f)) :
    D.a (D.d c) (E B (D.s v₀)) =
      (((c : K) ^ (2 * bitSum B)) * ((c⁻¹ : Kˣ) : K) ^ k) • E B (D.s v₀) := by
  have hA : D.a (D.d c) * D.s = D.s * (D.a (D.d c))⁻¹ := by
    calc D.a (D.d c) * D.s = (D.s * D.s) * D.a (D.d c) * D.s := by rw [D.s_sq, one_mul]
      _ = D.s * (D.s * D.a (D.d c) * D.s) := by simp only [mul_assoc]
      _ = D.s * (D.a (D.d c))⁻¹ := by rw [D.s_d c]
  have hinv : (D.a (D.d c))⁻¹ = D.a (D.d (c⁻¹)) := by
    rw [map_inv D.d c, map_inv D.a (D.d c)]
  have h1 : D.a (D.d c) (D.s v₀) = ((c⁻¹ : Kˣ) : K) ^ k • D.s v₀ := by
    have h2 := congrArg (fun e : V ≃ₗ[K] V => e v₀) hA
    simp only [LinearEquiv.mul_apply] at h2
    rw [h2, hinv, hk (c⁻¹), map_smul]
  rw [D.torus_conj_E hf hE c B (D.s v₀), h1, map_smul, smul_smul]

end RankOneData

end CFSG.RankThree.GF2n.Smith81.S81V
