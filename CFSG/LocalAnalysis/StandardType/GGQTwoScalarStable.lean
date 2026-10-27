module

public import CFSG.LocalAnalysis.StandardType.GGQTwoS5Defs

public section

namespace CFSG.StandardType

open Module

private lemma ggQ2ss_scalar {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (a r t : ZMod p) (x y : V) :
    r • t • x + a • y = a • (r • x + y) + (r * (t - a)) • x := by
  rw [smul_add, smul_smul, smul_smul, add_assoc, add_comm (a • y), ← add_assoc,
    ← add_smul]
  rw [show r * t = a * r + r * (t - a) by ring]

private lemma ggQ2ss_mul_inv_apply {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (e₁ e₂ : V ≃ₗ[ZMod p] V) (x : V) :
    (e₁ * e₂)⁻¹ (e₁ (e₂ x)) = x := by
  rw [← LinearEquiv.mul_apply]
  simpa using (e₁ * e₂).symm_apply_apply x

private lemma ggQ2ss_simpleRefl_fix {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (xV : D.V)
    {j : D.ι} (hx : D.root j xV = 0) : D.simpleRefl j xV = xV := by
  simp only [GGQ2Lin.simpleRefl,
    Module.reflection_apply (x := D.coroot j) (f := D.root j) xV
      (D.root_coroot_self j), hx, zero_smul, sub_zero]

private lemma ggQ2ss_parab_fix {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (xV : D.V)
    (hxα : ∀ j : {k // k ≠ D.a}, D.root j xV = 0) :
    ∀ w ∈ D.parab {k | k ≠ D.a}, w xV = xV := by
  let H : Subgroup (D.V ≃ₗ[ZMod p] D.V) :=
    { carrier := {g | g xV = xV}
      one_mem' := by simp
      mul_mem' := by
        intro g h hg hh
        show (g * h) xV = xV
        rw [LinearEquiv.mul_apply, hh, hg]
      inv_mem' := by
        intro g hg
        have h : g⁻¹ (g xV) = xV := by simpa using g.symm_apply_apply xV
        rwa [hg] at h }
  have hsubset : D.simpleRefl '' {k | k ≠ D.a} ⊆ H := by
    rintro g ⟨j, hj, rfl⟩
    exact ggQ2ss_simpleRefl_fix D xV (hxα ⟨j, hj⟩)
  intro w hw
  exact (Subgroup.closure_le H).mpr hsubset hw

theorem ggQ2_scalarStable {p : ℕ} [Fact p.Prime] (D : GGQ2Lin p) (xV : D.V)
    (hxα : ∀ j : {k // k ≠ D.a}, D.root j xV = 0)
    (hV : Submodule.span (ZMod p)
      (insert xV (Set.range fun i : {k // k ≠ D.a} => D.coroot i)) = ⊤)
    {π : {k // k ≠ D.a} ≃ {k // k ≠ D.a}} {μ : {k // k ≠ D.a} → ZMod p}
    (hS : D.ScalarModW D.a π μ)
    {T : D.V →ₗ[ZMod p] D.V} {c : ZMod p} {w : D.V ≃ₗ[ZMod p] D.V}
    (hw : w ∈ D.parab {k | k ≠ D.a})
    (hT : ∀ i : {k // k ≠ D.a}, T (D.coroot i) = c • μ i • w (D.coroot (π i)))
    (hTx : T xV ∈ Submodule.span (ZMod p) {xV}) :
    ∃ w' ∈ D.parab {k | k ≠ D.a}, ∃ ε : ZMod p, ∀ v : D.V, ∃ s : ZMod p,
      w' (T v) = ε • v + s • xV := by
  obtain ⟨ε₀, -, w₁, hw₁, hμ⟩ := hS
  set w' : D.V ≃ₗ[ZMod p] D.V := (w * w₁)⁻¹ with hw'def
  have hw' : w' ∈ D.parab {k | k ≠ D.a} := by
    rw [hw'def]
    exact (D.parab {k | k ≠ D.a}).inv_mem ((D.parab {k | k ≠ D.a}).mul_mem hw hw₁)
  have hww₁ : ∀ x : D.V, w' (w (w₁ x)) = x := by
    intro x
    rw [hw'def]
    exact ggQ2ss_mul_inv_apply w w₁ x
  have hTeq : ∀ i : {k // k ≠ D.a},
      T (D.coroot i) = (c * ε₀) • w (w₁ (D.coroot i)) := by
    intro i
    calc T (D.coroot i) = c • μ i • w (D.coroot (π i)) := hT i
      _ = c • w (μ i • D.coroot (π i)) := by rw [map_smul]
      _ = c • w (ε₀ • w₁ (D.coroot i)) := by rw [hμ i]
      _ = (c * ε₀) • w (w₁ (D.coroot i)) := by rw [map_smul, smul_smul]
  have hcor : ∀ i : {k // k ≠ D.a}, w' (T (D.coroot i)) = (c * ε₀) • D.coroot i := by
    intro i
    rw [hTeq i]
    simp only [map_smul]
    rw [hww₁]
  have hspan : ∀ u ∈ Submodule.span (ZMod p)
      (Set.range fun i : {k // k ≠ D.a} => D.coroot i), w' (T u) = (c * ε₀) • u := by
    intro u hu
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hu
    · rintro x ⟨i, rfl⟩
      exact hcor i
    · simp
    · intro x y _ _ ihx ihy
      simp only [map_add, ihx, ihy, smul_add]
    · intro a x _ ih
      have hcoef : a * (c * ε₀) = (c * ε₀) * a := mul_comm _ _
      simp only [map_smul, ih, smul_smul]
      rw [hcoef]
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.mp hTx
  have hfix : w' xV = xV := ggQ2ss_parab_fix D xV hxα w' hw'
  have htx : w' (T xV) = t • xV := by
    rw [← ht, map_smul, hfix]
  have hv : ∀ v : D.V, ∃ r : ZMod p, ∃ u ∈ Submodule.span (ZMod p)
      (Set.range fun i : {k // k ≠ D.a} => D.coroot i), v = r • xV + u := by
    intro v
    have hmem : v ∈ Submodule.span (ZMod p)
        (insert xV (Set.range fun i : {k // k ≠ D.a} => D.coroot i)) := by
      rw [hV]
      trivial
    exact Submodule.mem_span_insert.mp hmem
  refine ⟨w', hw', c * ε₀, ?_⟩
  intro v
  obtain ⟨r, u, hu, rfl⟩ := hv v
  exact ⟨r * (t - c * ε₀), by
    simp only [map_add, map_smul, htx, hspan u hu]
    exact ggQ2ss_scalar (c * ε₀) r t xV u⟩

end CFSG.StandardType

end
