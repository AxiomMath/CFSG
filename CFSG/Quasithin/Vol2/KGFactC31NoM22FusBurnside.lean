module

public import Mathlib.GroupTheory.Sylow

public section

open scoped Pointwise

namespace CFSG.Quasithin.KGC31

variable {G : Type*} [Group G]

theorem burnside_fusion_subgroup [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (X : Subgroup G) (hX : ∀ x ∈ X, ∀ y ∈ (P : Subgroup G), x * y = y * x)
    (g : G) (hg : ∀ x ∈ X, ∀ y ∈ (P : Subgroup G), (g⁻¹ * x * g) * y = y * (g⁻¹ * x * g)) :
    ∃ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
      ∀ x ∈ X, g⁻¹ * x * g = n⁻¹ * x * n := by
  have h1 : (P : Subgroup G) ≤ Subgroup.centralizer (X : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hX x hx y hy
  have h2 : ((g • P : Sylow p G) : Subgroup G) ≤ Subgroup.centralizer (X : Set G) := by
    intro y hy
    rw [Sylow.coe_subgroup_smul] at hy
    obtain ⟨w, hw, rfl⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).1 hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    change x * (g * w * g⁻¹) = g * w * g⁻¹ * x
    calc x * (g * w * g⁻¹) = g * ((g⁻¹ * x * g) * w) * g⁻¹ := by group
      _ = g * (w * (g⁻¹ * x * g)) * g⁻¹ := by rw [hg x hx w hw]
      _ = g * w * g⁻¹ * x := by group
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq (Subgroup.centralizer (X : Set G))
    ((g • P : Sylow p G).subtype h2) (P.subtype h1)
  simp_rw [Sylow.smul_subtype, Subgroup.smul_def, smul_smul] at hh
  refine ⟨(h : G) * g, Sylow.smul_eq_iff_mem_normalizer.mp (Sylow.subtype_injective hh), ?_⟩
  intro x hx
  have hcomm : x * (h : G) = (h : G) * x := Subgroup.mem_centralizer_iff.1 h.2 x hx
  have hinv : (h : G)⁻¹ * x * (h : G) = x := by
    rw [mul_assoc, hcomm, inv_mul_cancel_left]
  calc g⁻¹ * x * g = g⁻¹ * ((h : G)⁻¹ * x * (h : G)) * g := by rw [hinv]
    _ = ((h : G) * g)⁻¹ * x * ((h : G) * g) := by group

theorem pow_centralizes_of_sylow [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x) {m : ℕ}
    (hm : ∀ u ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
      u ^ m ∈ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (X : Subgroup G) (hXP : X ≤ (P : Subgroup G)) (n : G)
    (hn : n ∈ Subgroup.normalizer (X : Set G)) :
    ∀ z ∈ X, n ^ m * z = z * n ^ m := by
  have hX : ∀ x ∈ X, ∀ y ∈ (P : Subgroup G), x * y = y * x := fun x hx y hy =>
    hP x (hXP hx) y hy
  have hnX : ∀ x ∈ X, n * x * n⁻¹ ∈ X := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hn x).1 hx
  obtain ⟨u, hu, hstep⟩ := burnside_fusion_subgroup P X hX n⁻¹ (by
    intro x hx y hy
    rw [inv_inv]
    exact hX _ (hnX x hx) y hy)
  have hstep' : ∀ x ∈ X, n * x * n⁻¹ = u⁻¹ * x * u := fun x hx => by
    have := hstep x hx
    rwa [inv_inv] at this
  have hpow : ∀ j : ℕ, ∀ x ∈ X, n ^ j * x * (n ^ j)⁻¹ = (u ^ j)⁻¹ * x * u ^ j := by
    intro j
    induction j with
    | zero => intro x _; simp
    | succ j ih =>
      intro x hx
      have hmem : n ^ j * x * (n ^ j)⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ hn j) x).1 hx
      calc n ^ (j + 1) * x * (n ^ (j + 1))⁻¹ = n * (n ^ j * x * (n ^ j)⁻¹) * n⁻¹ := by
            rw [pow_succ']; group
        _ = u⁻¹ * (n ^ j * x * (n ^ j)⁻¹) * u := hstep' _ hmem
        _ = u⁻¹ * ((u ^ j)⁻¹ * x * u ^ j) * u := by rw [ih x hx]
        _ = (u ^ (j + 1))⁻¹ * x * u ^ (j + 1) := by rw [pow_succ']; group
  intro z hz
  have hcent : z * u ^ m = u ^ m * z := Subgroup.mem_centralizer_iff.1 (hm u hu) z (hXP hz)
  have hconj : n ^ m * z * (n ^ m)⁻¹ = z := by
    rw [hpow m z hz, mul_assoc, hcent, inv_mul_cancel_left]
  calc n ^ m * z = (n ^ m * z * (n ^ m)⁻¹) * n ^ m := by group
    _ = z * n ^ m := by rw [hconj]

theorem pow_centralizes_pgroup [Finite G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    (hP : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x) {m : ℕ}
    (hm : ∀ u ∈ Subgroup.normalizer ((P : Subgroup G) : Set G),
      u ^ m ∈ Subgroup.centralizer ((P : Subgroup G) : Set G))
    (Q : Subgroup G) (hQ : IsPGroup p Q) (n : G) (hn : n ∈ Subgroup.normalizer (Q : Set G)) :
    ∀ z ∈ Q, n ^ m * z = z * n ^ m := by
  obtain ⟨R, hQR⟩ := hQ.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
  have hgR : ∀ z ∈ (R : Subgroup G), g * z * g⁻¹ ∈ (P : Subgroup G) := by
    intro z hz
    have hmem : MulAut.conj g z ∈ MulAut.conj g • (R : Subgroup G) :=
      Subgroup.smul_mem_pointwise_smul z _ _ hz
    rw [← Sylow.coe_subgroup_smul, hg] at hmem
    simpa [MulAut.conj_apply] using hmem
  set X : Subgroup G := Subgroup.map (MulAut.conj g).toMonoidHom Q with hXdef
  have hXP : X ≤ (P : Subgroup G) := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hw
    exact hgR z (hQR hz)
  have hnX : g * n * g⁻¹ ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro w
    have e1 : (MulAut.conj g).symm ((g * n * g⁻¹) * w * (g * n * g⁻¹)⁻¹) =
        n * ((MulAut.conj g).symm w) * n⁻¹ := by
      simp only [MulAut.conj_symm_apply]
      group
    rw [hXdef, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, e1]
    exact Subgroup.mem_normalizer_iff.1 hn _
  intro z hz
  have hzX : g * z * g⁻¹ ∈ X := Subgroup.mem_map.2 ⟨z, hz, rfl⟩
  have key := pow_centralizes_of_sylow P hP hm X hXP (g * n * g⁻¹) hnX (g * z * g⁻¹) hzX
  rw [conj_pow] at key
  have h2 : g * (n ^ m * z) * g⁻¹ = g * (z * n ^ m) * g⁻¹ := by
    calc g * (n ^ m * z) * g⁻¹ = g * n ^ m * g⁻¹ * (g * z * g⁻¹) := by group
      _ = (g * z * g⁻¹) * (g * n ^ m * g⁻¹) := key
      _ = g * (z * n ^ m) * g⁻¹ := by group
  have h3 := congrArg (fun t => g⁻¹ * t * g) h2
  simpa [mul_assoc] using h3

end CFSG.Quasithin.KGC31

end
