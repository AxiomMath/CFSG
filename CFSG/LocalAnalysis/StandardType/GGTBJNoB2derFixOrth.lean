module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRuleRank

public section

namespace CFSG.StandardType

open Module


private def l48dA_P {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Z : Module.End K V) : Module.End K V := Z ^ 2 + Z + 1

private lemma l48dA_decomp {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Z : Module.End K V) :
    l48dA_P Z + (Z - 1) * Z = 1 := by
  change (Z ^ 2 + Z + 1) + (Z - 1) * Z = 1
  have h : (Z ^ 2 + Z + 1) + (Z - 1) * Z = 2 * Z ^ 2 + 1 := by noncomm_ring
  rw [h, CFSG.StandardType.TwoThree.two_eq_zero_end, zero_mul, zero_add]

private lemma l48dA_P_mul_sub {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Z : Module.End K V) (hZ : Z ^ 3 = 1) :
    l48dA_P Z * (Z - 1) = 0 := by
  change (Z ^ 2 + Z + 1) * (Z - 1) = 0
  have h : (Z ^ 2 + Z + 1) * (Z - 1) = Z ^ 3 - 1 := by noncomm_ring
  rw [h, hZ, sub_self]

private lemma l48dA_Z_mul_P {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Z : Module.End K V) (hZ : Z ^ 3 = 1) :
    Z * l48dA_P Z = l48dA_P Z := by
  change Z * (Z ^ 2 + Z + 1) = Z ^ 2 + Z + 1
  have h : Z * (Z ^ 2 + Z + 1) = Z ^ 3 + Z ^ 2 + Z := by noncomm_ring
  rw [h, hZ]
  abel

private lemma l48dA_P_apply_of_fix {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    {Z : Module.End K V} {v : V} (hv : Z v = v) :
    l48dA_P Z v = v := by
  change ((Z ^ 2 + Z + 1 : Module.End K V)) v = v
  simp only [LinearMap.add_apply, Module.End.one_apply]
  have hZ2 : (Z ^ 2) v = v := by
    calc (Z ^ 2) v = Z (Z v) := by rw [pow_two, Module.End.mul_apply]
      _ = Z v := congrArg Z hv
      _ = v := hv
  rw [hZ2, hv]
  have hvv : v + v = 0 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    calc v + v = (1 : K) • v + (1 : K) • v := by simp only [one_smul]
      _ = ((1 : K) + (1 : K)) • v := (add_smul (1 : K) (1 : K) v).symm
      _ = (2 : K) • v := by rw [one_add_one_eq_two]
      _ = 0 := by rw [h2, zero_smul]
  rw [hvv, zero_add]

private lemma l48dA_mem_fix_iff {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (ρ : G →* (Module.End K V)ˣ) (z : G) (v : V) :
    v ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers z) ↔
      (ρ z : Module.End K V) v = v := by
  rw [SmallRule.mem_fixSpaceOf]
  constructor
  · intro h
    exact h z (Subgroup.mem_zpowers z)
  · intro h
    let S : Subgroup G :=
      { carrier := {u | (ρ u : Module.End K V) v = v}
        one_mem' := by
          change (ρ 1 : Module.End K V) v = v
          rw [map_one, Units.val_one, Module.End.one_apply]
        mul_mem' := by
          intro a b ha hb
          change (ρ (a * b) : Module.End K V) v = v
          rw [map_mul, Units.val_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := by
          intro a ha
          change (ρ a⁻¹ : Module.End K V) v = v
          calc (ρ a⁻¹ : Module.End K V) v
              = (ρ a⁻¹ : Module.End K V) ((ρ a : Module.End K V) v) := by rw [ha]
            _ = (ρ (a⁻¹ * a) : Module.End K V) v :=
                  (SmallRule.rho_mul_apply ρ a⁻¹ a v).symm
            _ = v := by rw [inv_mul_cancel, map_one, Units.val_one, Module.End.one_apply] }
    have hzS : z ∈ S := h
    exact Subgroup.zpowers_le.mpr hzS

theorem ggB2der_fix_orth_decomp {K : Type*} [Field K] [CharP K 2] [Finite K] {V : Type*}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {G : Type*} [Group G]
    (hK : Nat.card K = 2) (ρ : G →* (Module.End K V)ˣ)
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (hr : B.IsRefl)
    (hiso : ∀ g v w, B ((ρ g : Module.End K V) v) ((ρ g : Module.End K V) w) = B v w)
    {z : G} (hz : z ^ 3 = 1) :
    IsCompl (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z))
        (B.orthogonal (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z))) ∧
      (∀ g : G, g * z = z * g →
        ∀ v ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers z),
          (ρ g : Module.End K V) v ∈ SmallRule.fixSpaceOf ρ (Subgroup.zpowers z)) ∧
      (∀ g : G, g * z = z * g →
        ∀ v ∈ B.orthogonal (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z)),
          (ρ g : Module.End K V) v ∈ B.orthogonal (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z))) ∧
      (∀ v ∈ B.orthogonal (SmallRule.fixSpaceOf ρ (Subgroup.zpowers z)),
        (ρ z : Module.End K V) v = v → v = 0) := by
  classical
  set Z : Module.End K V := (ρ z : Module.End K V) with hZ
  set W0 : Submodule K V := SmallRule.fixSpaceOf ρ (Subgroup.zpowers z) with hW0
  have hZ3 : Z ^ 3 = 1 := by
    rw [hZ, ← Units.val_pow_eq_pow_val, ← map_pow, hz, map_one, Units.val_one]
  have hmem : ∀ v : V, v ∈ W0 ↔ Z v = v := by
    intro v
    rw [hW0, l48dA_mem_fix_iff ρ z v, hZ]
  have hZP : Z * l48dA_P Z = l48dA_P Z := l48dA_Z_mul_P Z hZ3
  have hPsub : l48dA_P Z * (Z - 1) = 0 := l48dA_P_mul_sub Z hZ3
  have hPmem : ∀ v : V, l48dA_P Z v ∈ W0 := by
    intro v
    rw [hmem (l48dA_P Z v)]
    rw [← Module.End.mul_apply, hZP]
  have hdisj_range : W0 ⊓ LinearMap.range (Z - 1) = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    rw [Submodule.mem_inf] at hv
    obtain ⟨hvW, u, hu⟩ := hv
    have h1 : l48dA_P Z v = v := l48dA_P_apply_of_fix ((hmem v).mp hvW)
    have h2 : l48dA_P Z v = 0 := by
      rw [← hu, ← Module.End.mul_apply, hPsub, LinearMap.zero_apply]
    rw [h1] at h2
    exact h2
  have hsup_range : W0 ⊔ LinearMap.range (Z - 1) = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h := congrArg (fun f : Module.End K V => f v) (l48dA_decomp Z)
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.one_apply] at h
    rw [← h]
    exact Submodule.add_mem_sup (hPmem v) ⟨Z v, rfl⟩
  have hcompl_range : IsCompl W0 (LinearMap.range (Z - 1)) := by
    rw [isCompl_iff]
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff_inf_le, hdisj_range]
    · rw [codisjoint_iff]
      exact hsup_range
  have hker_sub : LinearMap.ker (Z - 1) = W0 := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
    exact (hmem v).symm
  have hfr_range : finrank K (LinearMap.range (Z - 1)) = finrank K V - finrank K W0 := by
    have hrk := LinearMap.finrank_range_add_finrank_ker (Z - 1)
    rw [hker_sub] at hrk
    omega
  have hfr_orth : finrank K (B.orthogonal W0) = finrank K V - finrank K W0 :=
    LinearMap.BilinForm.finrank_orthogonal hB W0
  have horth_le : LinearMap.range (Z - 1) ≤ B.orthogonal W0 := by
    intro v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro w hw
    obtain ⟨u, rfl⟩ := hv
    have hwZ : Z w = w := (hmem w).mp hw
    have hisow : B w (Z u) = B w u := by
      calc B w (Z u) = B (Z w) (Z u) := by rw [hwZ]
        _ = B w u := by simpa only [hZ] using hiso z w u
    calc B w ((Z - 1) u) = B w (Z u - u) := by
            rw [LinearMap.sub_apply, Module.End.one_apply]
      _ = B w (Z u) - B w u := map_sub (B w) (Z u) u
      _ = 0 := by rw [hisow, sub_self]
  haveI : FiniteDimensional K (B.orthogonal W0) :=
    FiniteDimensional.finiteDimensional_submodule (B.orthogonal W0)
  have hrange_orth : LinearMap.range (Z - 1) = B.orthogonal W0 :=
    Submodule.eq_of_le_of_finrank_eq horth_le (hfr_range.trans hfr_orth.symm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hrange_orth]
    exact hcompl_range
  · intro g hgz v hv
    rw [hmem ((ρ g : Module.End K V) v)]
    have hvZ : Z v = v := (hmem v).mp hv
    have hzg : z * g = g * z := hgz.symm
    calc Z ((ρ g : Module.End K V) v)
        = (ρ (z * g) : Module.End K V) v := by
            simpa only [hZ] using (SmallRule.rho_mul_apply ρ z g v).symm
      _ = (ρ (g * z) : Module.End K V) v := by rw [hzg]
      _ = (ρ g : Module.End K V) (Z v) := by
            simpa only [hZ] using SmallRule.rho_mul_apply ρ g z v
      _ = (ρ g : Module.End K V) v := by rw [hvZ]
  · intro g hgz v hv
    rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
    intro w hw
    have hginv : g⁻¹ * z = z * g⁻¹ := by
      have h := congrArg (fun t => g⁻¹ * t * g⁻¹) hgz
      simpa [mul_assoc] using h.symm
    have hwZ : Z w = w := (hmem w).mp hw
    have hw' : (ρ g⁻¹ : Module.End K V) w ∈ W0 := by
      rw [hmem ((ρ g⁻¹ : Module.End K V) w)]
      calc Z ((ρ g⁻¹ : Module.End K V) w)
          = (ρ (z * g⁻¹) : Module.End K V) w := by
              simpa only [hZ] using (SmallRule.rho_mul_apply ρ z g⁻¹ w).symm
        _ = (ρ (g⁻¹ * z) : Module.End K V) w := by rw [hginv.symm]
        _ = (ρ g⁻¹ : Module.End K V) (Z w) := by
              simpa only [hZ] using SmallRule.rho_mul_apply ρ g⁻¹ z w
        _ = (ρ g⁻¹ : Module.End K V) w := by rw [hwZ]
    have hv' : (ρ g⁻¹ : Module.End K V) ((ρ g : Module.End K V) v) = v := by
      rw [← SmallRule.rho_mul_apply ρ g⁻¹ g v, inv_mul_cancel, map_one, Units.val_one,
        Module.End.one_apply]
    calc B w ((ρ g : Module.End K V) v)
        = B ((ρ g⁻¹ : Module.End K V) w)
            ((ρ g⁻¹ : Module.End K V) ((ρ g : Module.End K V) v)) :=
            (hiso g⁻¹ w ((ρ g : Module.End K V) v)).symm
      _ = B ((ρ g⁻¹ : Module.End K V) w) v := by rw [hv']
      _ = 0 := hv ((ρ g⁻¹ : Module.End K V) w) hw'
  · intro v hv hvZ
    have hvW : v ∈ W0 := (hmem v).mpr hvZ
    have hmem_inf : v ∈ W0 ⊓ LinearMap.range (Z - 1) := by
      refine ⟨hvW, ?_⟩
      rw [hrange_orth]
      exact hv
    rw [hdisj_range] at hmem_inf
    simpa using hmem_inf

end CFSG.StandardType

end
