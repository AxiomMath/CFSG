module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Action

public section

namespace CFSG.RankThree.GF2n.Tim79.QuadModel

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

private theorem exists_B_zero_B_ne {M₀ : QuadModel QF V K γ} {a b : M₀.E} (hb : b ≠ 0)
    (hab : ∀ c : K, c • b ≠ a) : ∃ f₀ : M₀.E, M₀.B f₀ b = 0 ∧ M₀.B f₀ a ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨c, hc⟩ := exists_smul_of_orthogonal hb (v := a) (fun h hh => by
    rw [B_comm a h, hcon h hh, neg_zero])
  exact hab c hc.symm

theorem exists_dual_pair (M₀ : QuadModel QF V K γ) {a b : M₀.E} (hb : b ≠ 0)
    (hab : ∀ c : K, c • b ≠ a) :
    ∃ f g : M₀.E, M₀.B f a = 1 ∧ M₀.B f b = 0 ∧ M₀.B g a = 0 ∧ M₀.B g b = 1 := by
  have ha : a ≠ 0 := fun h => hab 0 (by rw [h, zero_smul])
  have hba : ∀ c : K, c • a ≠ b := by
    intro c hc
    by_cases hc0 : c = 0
    · exact hb (by rw [← hc, hc0, zero_smul])
    · exact hab c⁻¹ (by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul])
  obtain ⟨f₀, hf₀b, hf₀a⟩ := exists_B_zero_B_ne hb hab
  obtain ⟨g₀, hg₀a, hg₀b⟩ := exists_B_zero_B_ne ha hba
  refine ⟨(M₀.B f₀ a)⁻¹ • f₀, (M₀.B g₀ b)⁻¹ • g₀, ?_, ?_, ?_, ?_⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀a]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hf₀b, mul_zero]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, hg₀a, mul_zero]
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hg₀b]

private theorem Qf_smul_add_smul_eq_zero {M₀ : QuadModel QF V K γ} {a b : M₀.E} (ha : M₀.Qf a = 0)
    (hb : M₀.Qf b = 0) (hω : M₀.B a b = 0) (x y : K) : M₀.Qf (x • a + y • b) = 0 := by
  simp [M₀.Qf_add, M₀.Qf_smul, ha, hb, hω, map_smul]

private theorem eq_smul_add_smul_of_perp [CharP K 2] {M₀ : QuadModel QF V K γ} {a b f g : M₀.E}
    (hfa : M₀.B f a = 1) (hfb : M₀.B f b = 0) (hga : M₀.B g a = 0) (hgb : M₀.B g b = 1)
    {w : M₀.E} (hw : ∀ u, M₀.B u a = 0 → M₀.B u b = 0 → M₀.B w u = 0) :
    w = M₀.B w f • a + M₀.B w g • b := by
  have hdec : ∀ x, M₀.B w x = M₀.B x a * M₀.B w f + M₀.B x b * M₀.B w g := by
    intro x
    have hu : M₀.B (x - M₀.B x a • f - M₀.B x b • g) a = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hfa, hga]
      ring
    have hu' : M₀.B (x - M₀.B x a • f - M₀.B x b • g) b = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
      rw [hfb, hgb]
      ring
    have key : M₀.B w x = M₀.B w (M₀.B x a • f + M₀.B x b • g) +
        M₀.B w (x - M₀.B x a • f - M₀.B x b • g) := by
      rw [← map_add]
      congr 1
      abel
    rw [key, hw _ hu hu', add_zero]
    simp only [map_add, map_smul, smul_eq_mul]
  have hv : ∀ x, M₀.B (w - (M₀.B w f • a + M₀.B w g • b)) x = 0 := by
    intro x
    have ha' : M₀.B a x = M₀.B x a := by rw [B_comm, CharTwo.neg_eq]
    have hb' : M₀.B b x = M₀.B x b := by rw [B_comm, CharTwo.neg_eq]
    simp only [map_sub, map_add, map_smul, LinearMap.sub_apply, LinearMap.add_apply,
      LinearMap.smul_apply, smul_eq_mul]
    rw [hdec x, ha', hb']
    ring
  exact sub_eq_zero.mp (M₀.nondeg _ hv)

theorem exists_scalar_of_fix_perp [CharP K 2] (M₀ : QuadModel QF V K γ) {a b : M₀.E}
    (ha : M₀.Qf a = 0) (hb : M₀.Qf b = 0) (hb0 : b ≠ 0) (hab : ∀ c : K, c • b ≠ a)
    {T : M₀.E →ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e) (hTa : T a = a) (hTb : T b = b)
    (hTU : ∀ e, M₀.B e a = 0 → M₀.B e b = 0 → T e = e) :
    ∃ c : K, ∀ e, T e = e + c • (M₀.B e b • a + M₀.B e a • b) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  by_cases hω : M₀.B a b = 0
  · obtain ⟨f, g, hfa, hfb, hga, hgb⟩ := exists_dual_pair M₀ hb0 hab
    have hdec : ∀ e, T e - e = M₀.B e a • (T f - f) + M₀.B e b • (T g - g) := by
      intro e
      have hu : M₀.B (e - M₀.B e a • f - M₀.B e b • g) a = 0 := by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [hfa, hga]
        ring
      have hu' : M₀.B (e - M₀.B e a • f - M₀.B e b • g) b = 0 := by
        simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [hfb, hgb]
        ring
      have h := hTU _ hu hu'
      simp only [map_sub, map_smul] at h
      linear_combination (norm := module) h
    have hperp_f : ∀ u, M₀.B u a = 0 → M₀.B u b = 0 → M₀.B (T f - f) u = 0 := by
      intro u hua hub
      have h := B_iso hT f u
      rw [hTU u hua hub] at h
      rw [map_sub, LinearMap.sub_apply, h, sub_self]
    have hperp_g : ∀ u, M₀.B u a = 0 → M₀.B u b = 0 → M₀.B (T g - g) u = 0 := by
      intro u hua hub
      have h := B_iso hT g u
      rw [hTU u hua hub] at h
      rw [map_sub, LinearMap.sub_apply, h, sub_self]
    obtain ⟨c₁, c₂, hwf⟩ : ∃ c₁ c₂ : K, T f - f = c₁ • a + c₂ • b :=
      ⟨_, _, eq_smul_add_smul_of_perp hfa hfb hga hgb hperp_f⟩
    obtain ⟨r₁, r₂, hwg⟩ : ∃ r₁ r₂ : K, T g - g = r₁ • a + r₂ • b :=
      ⟨_, _, eq_smul_add_smul_of_perp hfa hfb hga hgb hperp_g⟩
    have hQf_f : M₀.Qf (T f - f) = 0 := by
      rw [hwf]
      exact Qf_smul_add_smul_eq_zero ha hb hω _ _
    have hQf_g : M₀.Qf (T g - g) = 0 := by
      rw [hwg]
      exact Qf_smul_add_smul_eq_zero ha hb hω _ _
    have hBf : M₀.B f (T f - f) = 0 := by
      have h := hT f
      rw [show T f = f + (T f - f) by abel, M₀.Qf_add, hQf_f, add_zero] at h
      linear_combination h
    have hBg : M₀.B g (T g - g) = 0 := by
      have h := hT g
      rw [show T g = g + (T g - g) by abel, M₀.Qf_add, hQf_g, add_zero] at h
      linear_combination h
    have hc₁ : c₁ = 0 := by
      have h := hBf
      rw [hwf] at h
      simp only [map_add, map_smul, smul_eq_mul, hfa, hfb] at h
      linear_combination h
    have hr₂ : r₂ = 0 := by
      have h := hBg
      rw [hwg] at h
      simp only [map_add, map_smul, smul_eq_mul, hga, hgb] at h
      linear_combination h
    have hspan_sum : (T f - f) + (T g - g) = (c₁ + r₁) • a + (c₂ + r₂) • b := by
      rw [hwf, hwg]
      module
    have hQsum : M₀.Qf ((T f - f) + (T g - g)) = 0 := by
      rw [hspan_sum]
      exact Qf_smul_add_smul_eq_zero ha hb hω _ _
    have hlin : ∀ x y : K, M₀.B (f + g) (x • a + y • b) = x + y := by
      intro x y
      simp only [map_add, map_smul, LinearMap.add_apply, smul_eq_mul, hfa, hfb, hga, hgb]
      ring
    have h5 := hT (f + g)
    rw [map_add, show T f + T g = (f + g) + ((T f - f) + (T g - g)) by abel,
      M₀.Qf_add (f + g) ((T f - f) + (T g - g)), hQsum, add_zero, hspan_sum, hlin] at h5
    have hsum : c₁ + r₁ + (c₂ + r₂) = 0 := by
      linear_combination h5
    have hr₁ : r₁ = c₂ := by
      linear_combination hsum - hc₁ - hr₂ - c₂ * h2
    refine ⟨c₂, fun e => ?_⟩
    have key : T e - e = c₂ • (M₀.B e b • a + M₀.B e a • b) := by
      rw [hdec e, hwf, hwg, hc₁, hr₂, hr₁]
      module
    rw [← key]
    abel
  · refine ⟨0, fun e => ?_⟩
    have hba : M₀.B b a ≠ 0 := by
      rw [B_comm]
      exact neg_ne_zero.mpr hω
    have hα : M₀.B e b / M₀.B a b * M₀.B a b = M₀.B e b := div_mul_cancel₀ _ hω
    have hβ : M₀.B e a / M₀.B b a * M₀.B b a = M₀.B e a := div_mul_cancel₀ _ hba
    have hu : M₀.B (e - (M₀.B e b / M₀.B a b) • a - (M₀.B e a / M₀.B b a) • b) a = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        M₀.alt]
      linear_combination -hβ
    have hu' : M₀.B (e - (M₀.B e b / M₀.B a b) • a - (M₀.B e a / M₀.B b a) • b) b = 0 := by
      simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
        M₀.alt]
      linear_combination -hα
    have hfix := hTU _ hu hu'
    simp only [map_sub, map_smul, hTa, hTb] at hfix
    rw [zero_smul, add_zero]
    exact sub_left_inj.mp (sub_left_inj.mp hfix)

end CFSG.RankThree.GF2n.Tim79.QuadModel

namespace CFSG.RankThree.GF2n.Tim79.QuadModel

variable {G : Type} [Group G] {QF V : Subgroup G} {K : Type} [Field K] {γ : G → K}

theorem sq_eq_one_of_isotropic_range [CharP K 2] (M₀ : QuadModel QF V K γ)
    {T : M₀.E ≃ₗ[K] M₀.E} (hT : ∀ e, M₀.Qf (T e) = M₀.Qf e)
    (hiso : ∀ e e', M₀.B (T e - e) (T e' - e') = 0) (e : M₀.E) : T (T e) = e := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hTsymm : ∀ e, M₀.Qf (T.symm e) = M₀.Qf e := fun e => by
    have := hT (T.symm e)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have hB1 : ∀ e e', M₀.B (T e) (T e') = M₀.B e e' := fun e e' =>
    B_iso (T := (T : M₀.E →ₗ[K] M₀.E)) hT e e'
  have hB2 : ∀ e e', M₀.B (T.symm e) (T.symm e') = M₀.B e e' := fun e e' =>
    B_iso (T := (T.symm : M₀.E →ₗ[K] M₀.E)) hTsymm e e'
  have hadj : ∀ e e', M₀.B (T e) e' = M₀.B e (T.symm e') := fun e e' => by
    have := hB2 (T e) e'
    rw [LinearEquiv.symm_apply_apply] at this
    exact this.symm
  have hsym : ∀ e e', M₀.B (T e) e' = M₀.B e (T e') := fun e e' => by
    have h := hiso e e'
    simp only [map_sub, LinearMap.sub_apply] at h
    rw [hB1] at h
    linear_combination (-1 : K) * h + (M₀.B e e' - M₀.B e (T e')) * h2
  have heq : T e = T.symm e := by
    refine sub_eq_zero.mp (M₀.nondeg _ fun f => ?_)
    rw [B_comm (T e - T.symm e) f]
    have h1 := hsym f e
    have h3 := hadj f e
    rw [map_sub]
    have h4 : M₀.B f (T e) = M₀.B f (T.symm e) := by
      rw [← h1, h3]
    rw [h4, sub_self, neg_zero]
  rw [heq, LinearEquiv.apply_symm_apply]

end CFSG.RankThree.GF2n.Tim79.QuadModel

namespace CFSG.RankThree.GF2n.Stroth80

theorem range_sub_one_le_map_range {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {T : V →ₗ[K] V} {m : ℕ} (hm : Odd m) (hT : T ^ m = 1) :
    LinearMap.range (T - 1) ≤ (LinearMap.range (T - 1)).map (T - 1) := by
  rintro _ ⟨e, rfl⟩
  have he : e ∈ LinearMap.ker (T - 1) ⊔ LinearMap.range (T - 1) := by
    rw [ker_sup_range_eq_top_of_pow_eq_one hm hT]
    trivial
  obtain ⟨k, hk, r, hr, rfl⟩ := Submodule.mem_sup.mp he
  refine ⟨r, hr, ?_⟩
  rw [map_add, LinearMap.mem_ker.mp hk, zero_add]

theorem linearMap_pow_eq_one_of_equiv_pow_eq_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {T : V ≃ₗ[K] V} {r : ℕ} (h : T ^ r = 1) : (T : V →ₗ[K] V) ^ r = 1 := by
  ext e
  have h1 : (T ^ r) e = e := by rw [h]; rfl
  rw [LinearEquiv.coe_pow] at h1
  rw [Module.End.coe_pow]
  exact h1

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Stroth80

theorem altSelfadjCoreTwo {K : Type*} [Field K] (h2 : (2 : K) = 0)
    {a c e d g11 g12 g22 : K} (E1 : a * g11 + c * g12 = 0) (E2 : e * g12 + d * g22 = 0)
    (E4 : a * g12 + c * g22 = e * g11 + d * g12) (hD : g11 * g22 + g12 * g12 ≠ 0) :
    a + d = 0 := by
  have hm : (a + d) * (g11 * g22 + g12 * g12) = 0 := by
    linear_combination g22 * E1 + g11 * E2 - g12 * E4 + (g12 * (a * g12 - e * g11)) * h2
  rcases mul_eq_zero.mp hm with h | h
  · exact h
  · exact absurd h hD

theorem altSelfadjSqScalarOfFinrankLeOne {K P : Type*} [Field K] [AddCommGroup P]
    [Module K P] [FiniteDimensional K P] (hP : Module.finrank K P ≤ 1) (σ : P →ₗ[K] P) :
    ∃ c : K, ∀ x, σ (σ x) = c • x := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hP
  obtain ⟨κ, hκ⟩ := hv (σ v)
  refine ⟨κ * κ, fun x => ?_⟩
  obtain ⟨s, rfl⟩ := hv x
  simp only [map_smul, ← hκ]
  module

theorem altSelfadjSqScalarOfFinrankEqTwo {K P : Type*} [Field K] [AddCommGroup P]
    [Module K P] [FiniteDimensional K P] (h2 : (2 : K) = 0) (hP : Module.finrank K P = 2)
    (β : P →ₗ[K] P →ₗ[K] K) (hsymm : ∀ x y, β x y = β y x)
    (hnd : ∀ x, (∀ y, β x y = 0) → x = 0) (σ : P →ₗ[K] P)
    (hsa : ∀ x y, β (σ x) y = β x (σ y)) (hz : ∀ x, β (σ x) x = 0) :
    ∃ c : K, ∀ x, σ (σ x) = c • x := by
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin 2) K P) := ⟨Module.finBasisOfFinrankEq K P hP⟩
  have hdec : ∀ y : P, y = b.repr y 0 • b 0 + b.repr y 1 • b 1 := fun y => by
    have h := b.sum_repr y
    rw [Fin.sum_univ_two] at h
    exact h.symm
  have hfree : ∀ s t : K, s • b 0 + t • b 1 = 0 → s = 0 ∧ t = 0 := by
    intro s t h
    have h' := Fintype.linearIndependent_iff.mp b.linearIndependent ![s, t] (by
      rw [Fin.sum_univ_two]
      simpa using h)
    exact ⟨by simpa using h' 0, by simpa using h' 1⟩
  have hkey : ∀ u : P, β u (b 0) = 0 → β u (b 1) = 0 → u = 0 := by
    intro u h0 h1
    refine hnd u (fun y => ?_)
    rw [hdec y]
    simp only [map_add, map_smul, smul_eq_mul, h0, h1, mul_zero, add_zero]
  obtain ⟨a, c, hσ0⟩ : ∃ a c : K, σ (b 0) = a • b 0 + c • b 1 := ⟨_, _, hdec (σ (b 0))⟩
  obtain ⟨e, d, hσ1⟩ : ∃ e d : K, σ (b 1) = e • b 0 + d • b 1 := ⟨_, _, hdec (σ (b 1))⟩
  have E1 : a * β (b 0) (b 0) + c * β (b 0) (b 1) = 0 := by
    have h := hz (b 0)
    rw [hσ0] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    rw [hsymm (b 1) (b 0)] at h
    exact h
  have E2 : e * β (b 0) (b 1) + d * β (b 1) (b 1) = 0 := by
    have h := hz (b 1)
    rw [hσ1] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    exact h
  have E4 : a * β (b 0) (b 1) + c * β (b 1) (b 1)
      = e * β (b 0) (b 0) + d * β (b 0) (b 1) := by
    have h := hsa (b 0) (b 1)
    rw [hσ0, hσ1] at h
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
    exact h
  have hD : β (b 0) (b 0) * β (b 1) (b 1) + β (b 0) (b 1) * β (b 0) (b 1) ≠ 0 := by
    intro hD0
    have hv : β (b 1) (b 1) • b 0 + β (b 0) (b 1) • b 1 = 0 := by
      apply hkey
      · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [hsymm (b 1) (b 0)]
        linear_combination hD0
      · simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        linear_combination (β (b 0) (b 1) * β (b 1) (b 1)) * h2
    obtain ⟨hg22, hg12⟩ := hfree _ _ hv
    apply b.ne_zero 1
    apply hkey
    · rw [hsymm (b 1) (b 0)]
      exact hg12
    · exact hg22
  have hsum : a + d = 0 := altSelfadjCoreTwo h2 E1 E2 E4 hD
  have hd' : d = -a := by linear_combination hsum
  subst hd'
  have hσσ0 : σ (σ (b 0)) = (a * a + c * e) • b 0 := by
    simp only [map_add, map_smul, hσ0, hσ1]
    module
  have hσσ1 : σ (σ (b 1)) = (a * a + c * e) • b 1 := by
    simp only [map_add, map_smul, hσ0, hσ1]
    module
  refine ⟨a * a + c * e, fun x => ?_⟩
  obtain ⟨s, t, rfl⟩ : ∃ s t : K, x = s • b 0 + t • b 1 := ⟨_, _, hdec x⟩
  simp only [map_add, map_smul, hσσ0, hσσ1]
  module

theorem exists_sq_scalar_of_alt_selfadjoint {K P : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup P] [Module K P] [FiniteDimensional K P] (hP : Module.finrank K P ≤ 2)
    (β : P →ₗ[K] P →ₗ[K] K) (hsymm : ∀ x y, β x y = β y x)
    (hnd : ∀ x, (∀ y, β x y = 0) → x = 0) (σ : P →ₗ[K] P)
    (hsa : ∀ x y, β (σ x) y = β x (σ y)) (hz : ∀ x, β (σ x) x = 0) :
    ∃ μ : K, ∀ x, σ (σ x) = (μ * μ) • x := by
  have hsc : ∃ c : K, ∀ x, σ (σ x) = c • x := by
    rcases Nat.lt_or_ge (Module.finrank K P) 2 with h | h
    · exact altSelfadjSqScalarOfFinrankLeOne (by omega) σ
    · exact altSelfadjSqScalarOfFinrankEqTwo CharTwo.two_eq_zero (le_antisymm hP h)
        β hsymm hnd σ hsa hz
  obtain ⟨c, hc⟩ := hsc
  obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq (R := K) 2) c
  exact ⟨μ, fun x => by rw [hc x, hμ]⟩

end CFSG.RankThree.GF2n.Stroth80

namespace CFSG.RankThree.GF2n.Stroth80

open Polynomial

open scoped IsMulCommutative

theorem odd_order_frob_pow {C : Type*} [CommRing C] (h2 : (2 : C) = 0) (n : ℕ) (x y : C) :
    (x + y) ^ 2 ^ n = x ^ 2 ^ n + y ^ 2 ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ (2 : ℕ) k, pow_mul, ih, pow_mul, pow_mul, add_sq, mul_assoc, h2, zero_mul,
      add_zero]

theorem odd_order_split {C : Type*} [CommRing C] (h2 : (2 : C) = 0) {T u c d Φ Ψ : C}
    (hTu : T * u = 1) (hT2 : T * T + c * T + 1 = 0) (hΦ : Φ * Φ + c * Φ + 1 = 0)
    (hΨ : Φ * Ψ = 1) (hdc : d * c = 1) :
    d * (Φ + T) * (d * (Φ + T)) = d * (Φ + T) ∧
      Φ = (1 - d * (Φ + T)) * T + d * (Φ + T) * u ∧
      (1 - d * (Φ + T)) * Φ + d * (Φ + T) * Ψ = T := by
  have hs : T + u + c = 0 := by
    linear_combination u * hT2 - (T + c) * hTu
  have hΨeq : Φ + Ψ = c := by
    linear_combination Ψ * hΦ - (Φ + c) * hΨ - c * h2
  have hQ : (Φ + T) * (c - Φ - T) = 0 := by
    linear_combination (-1 : C) * hΦ + hT2 + (c * Φ - Φ * T - T * T) * h2
  have he : d * (Φ + T) * (d * (Φ + T)) = d * (Φ + T) := by
    linear_combination (-d ^ 2) * hQ + (d * (Φ + T)) * hdc
  have hsplit : Φ = (1 - d * (Φ + T)) * T + d * (Φ + T) * u := by
    linear_combination (d * (Φ + T)) * hs - (Φ + T) * hdc - (T + u * (d * (Φ + T))) * h2
  have h1 : (1 - d * (Φ + T)) * Φ = (1 - d * (Φ + T)) * T := by
    linear_combination (1 - d * (Φ + T)) * hsplit + (T - u) * he
  have h3 : d * (Φ + T) * Ψ = d * (Φ + T) * T := by
    linear_combination d * (Φ + T) * hΨeq - d * (Φ + T) * hsplit + d * (Φ + T) * hs
      + (T - u) * he - d * (Φ + T) * (T + u) * h2
  exact ⟨he, hsplit, by linear_combination h1 + h3⟩

theorem odd_order_core {C : Type*} [CommRing C] (h2 : (2 : C) = 0) (f : ℕ) {T u c d : C}
    (hTu : T * u = 1) (hT2 : T * T + c * T + 1 = 0) (hcq : c ^ 2 ^ f = c) (hdc : d * c = 1) :
    T ^ (2 ^ f * 2 ^ f) = T := by
  have hf : (2 : ℕ) ^ f ≠ 0 := pow_ne_zero f two_ne_zero
  have hΦ : T ^ 2 ^ f * T ^ 2 ^ f + c * T ^ 2 ^ f + 1 = 0 := by
    have h0 : (T * T + c * T + 1) ^ 2 ^ f = 0 := by
      rw [hT2]
      exact zero_pow hf
    rw [odd_order_frob_pow h2, odd_order_frob_pow h2, one_pow, mul_pow, mul_pow, hcq] at h0
    exact h0
  have hΨ : T ^ 2 ^ f * u ^ 2 ^ f = 1 := by
    rw [← mul_pow, hTu, one_pow]
  obtain ⟨he, hsplit, hfin⟩ := odd_order_split h2 hTu hT2 hΦ hΨ hdc
  have hid : (1 - d * (T ^ 2 ^ f + T)) * (1 - d * (T ^ 2 ^ f + T))
      = 1 - d * (T ^ 2 ^ f + T) := by
    linear_combination he
  have hpow1 : (1 - d * (T ^ 2 ^ f + T)) ^ 2 ^ f = 1 - d * (T ^ 2 ^ f + T) :=
    IsIdempotentElem.pow_eq hid hf
  have hpowe : (d * (T ^ 2 ^ f + T)) ^ 2 ^ f = d * (T ^ 2 ^ f + T) :=
    IsIdempotentElem.pow_eq he hf
  have h4 : (T ^ 2 ^ f) ^ 2 ^ f
      = ((1 - d * (T ^ 2 ^ f + T)) * T + d * (T ^ 2 ^ f + T) * u) ^ 2 ^ f :=
    congrArg (fun x => x ^ 2 ^ f) hsplit
  rw [pow_mul, h4, odd_order_frob_pow h2, mul_pow, mul_pow, hpow1, hpowe]
  exact hfin

theorem odd_order_pow_card_sq_sub_one {K A : Type*} [Field K] [Finite K] [CharP K 2] [Ring A]
    [Algebra K A] {T : A} {m : ℕ} (hm : Odd m) (hT : T ^ m = 1) {μ : K}
    (h : T * T + μ • T + 1 = 0) : T ^ (Nat.card K ^ 2 - 1) = 1 := by
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have h2A : (2 : A) = 0 := by
    have h2 : algebraMap K A 2 = 0 := by
      rw [h2K, map_zero]
    rwa [map_ofNat] at h2
  obtain ⟨f, hf⟩ : ∃ f : ℕ, Nat.card K = 2 ^ f := by
    haveI := Fintype.ofFinite K
    obtain ⟨n, -, hn⟩ := FiniteField.card K 2
    exact ⟨(n : ℕ), by rw [Nat.card_eq_fintype_card, hn]⟩
  have hm0 : 0 < m := by
    obtain ⟨k, hk⟩ := hm
    omega
  have hm1 : m - 1 + 1 = m := by omega
  have hTu : T * T ^ (m - 1) = 1 := by
    rw [← pow_succ', hm1, hT]
  obtain ⟨u, hu⟩ : ∃ u, T ^ (m - 1) = u := ⟨_, rfl⟩
  rw [hu] at hTu
  have key : T ^ Nat.card K ^ 2 = T := by
    by_cases hμ : μ = 0
    · subst hμ
      rw [zero_smul, add_zero] at h
      have h11 : (1 : A) + 1 = 0 := by
        rw [one_add_one_eq_two, h2A]
      have hTT : T * T = 1 := by
        calc T * T = T * T + 0 := (add_zero _).symm
          _ = T * T + (1 + 1) := by rw [h11]
          _ = T * T + 1 + 1 := (add_assoc _ _ _).symm
          _ = 1 := by rw [h, zero_add]
      have hT1 : T = 1 := by
        obtain ⟨k, hk⟩ := hm
        rw [hk, pow_succ, pow_mul, sq, hTT, one_pow, one_mul] at hT
        exact hT
      rw [hT1, one_pow]
    · have hμq : μ ^ Nat.card K = μ := by
        haveI := Fintype.ofFinite K
        rw [Nat.card_eq_fintype_card]
        exact FiniteField.pow_card μ
      have hμf : μ ^ 2 ^ f = μ := by
        rw [← hf]
        exact hμq
      have hT_mem : T ∈ Algebra.adjoin K ({T} : Set A) :=
        Algebra.subset_adjoin (Set.mem_singleton T)
      have hu_mem : u ∈ Algebra.adjoin K ({T} : Set A) := by
        rw [← hu]
        exact pow_mem hT_mem _
      have hS2 : (2 : Algebra.adjoin K ({T} : Set A)) = 0 := Subtype.ext h2A
      have hcore := odd_order_core (C := ↥(Algebra.adjoin K ({T} : Set A))) hS2 f
        (T := ⟨T, hT_mem⟩) (u := ⟨u, hu_mem⟩)
        (c := algebraMap K (Algebra.adjoin K ({T} : Set A)) μ)
        (d := algebraMap K (Algebra.adjoin K ({T} : Set A)) μ⁻¹)
        (Subtype.ext (by simpa using hTu))
        (Subtype.ext (by simpa [Algebra.smul_def] using h))
        (by rw [← map_pow, hμf])
        (by rw [← map_mul, inv_mul_cancel₀ hμ, map_one])
      have hA : T ^ (2 ^ f * 2 ^ f) = T := by
        have hval := congrArg Subtype.val hcore
        simpa using hval
      rw [hf, sq]
      exact hA
  have hNpos : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
  obtain ⟨M, hM⟩ : ∃ M, Nat.card K ^ 2 = M + 1 := ⟨Nat.card K ^ 2 - 1, by omega⟩
  have hTM : T ^ M * T = T := by
    rw [← pow_succ, ← hM]
    exact key
  rw [hM, Nat.add_sub_cancel]
  calc T ^ M = T ^ M * (T * u) := by rw [hTu, mul_one]
    _ = T ^ M * T * u := (mul_assoc _ _ _).symm
    _ = 1 := by rw [hTM, hTu]

theorem eq_zero_of_sq_eq_zero_of_pow_eq_one {K V : Type*} [Field K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {T : V →ₗ[K] V} {m : ℕ} (hm : Odd m) (hT : T ^ m = 1)
    {μ : K} (h : (T * T + μ • T + 1) * (T * T + μ • T + 1) = 0) : T * T + μ • T + 1 = 0 := by
  obtain ⟨g, hg_def⟩ : ∃ g : K[X], g = X ^ 2 + C μ * X + 1 := ⟨_, rfl⟩
  have hg : aeval T g = T * T + μ • T + 1 := by
    rw [hg_def]
    simp [Algebra.smul_def, sq]
  have hgg : aeval T (g * g) = 0 := by
    rw [map_mul, hg]
    exact h
  have hdvd : minpoly K T ∣ g * g := minpoly.dvd K T hgg
  have hXm : aeval T (X ^ m - 1 : K[X]) = 0 := by
    simp [hT]
  have hdvdX : minpoly K T ∣ (X ^ m - 1 : K[X]) := minpoly.dvd K T hXm
  have hm0 : (m : K) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff K 2] at h0
    obtain ⟨k, hk⟩ := hm
    omega
  have hsqf : Squarefree (minpoly K T) :=
    Squarefree.squarefree_of_dvd hdvdX (X_pow_sub_one_separable_iff.mpr hm0).squarefree
  have hdvdg : minpoly K T ∣ g :=
    (Squarefree.dvd_pow_iff_dvd hsqf two_ne_zero).mp (by rw [sq]; exact hdvd)
  obtain ⟨r, hr⟩ := hdvdg
  rw [← hg, hr, map_mul, minpoly.aeval, zero_mul]

theorem pow_card_sq_sub_one_eq_one {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] {T : V →ₗ[K] V} {m : ℕ} (hm : Odd m) (hT : T ^ m = 1)
    {μ : K} (h : T * T + μ • T + 1 = 0) : T ^ (Nat.card K ^ 2 - 1) = 1 :=
  odd_order_pow_card_sq_sub_one hm hT h

end CFSG.RankThree.GF2n.Stroth80
