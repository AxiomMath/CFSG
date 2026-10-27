module

public import CFSG.ClassicalGroups.Orthogonal.Matrix
public import CFSG.ClassicalGroups.Orthogonal.Models

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement
open scoped Matrix

section Derived

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

private theorem exists_perp_polar_one (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {x : V} (hx : x ∈ P.perp) (hx0 : x ≠ 0) : ∃ y ∈ P.perp, polar Q x y = 1 := by
  obtain ⟨y₀, hy₀, hne⟩ := (HypPair.polarNondegOn_perp hQ P).exists_polar_ne_zero hx hx0
  exact ⟨(polar Q x y₀)⁻¹ • y₀, P.perp.smul_mem _ hy₀, by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hne]⟩

private theorem eichler_mem_derived (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    {u x : V} (hpu : ∀ y ∈ P.perp, polar Q u y = 0) (hx : x ∈ P.perp) (hQx : Q x ≠ 0) :
    eichler Q u x ∈
      ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  have hx0 : x ≠ 0 := fun h => hQx (by rw [h, QuadraticMap.map_zero])
  obtain ⟨y₁, hy₁, hxy₁⟩ := exists_perp_polar_one hQ P hx hx0
  obtain ⟨y, hyP, hxy⟩ : ∃ y ∈ P.perp, polar Q x y = -Q x :=
    ⟨(-Q x) • y₁, P.perp.smul_mem _ hy₁, by rw [polar_smul_right_eq, hxy₁, mul_one]⟩
  have hxu : polar Q x u = 0 := by rw [polar_comm]; exact hpu x hx
  have hgu : reflect Q x u = u := reflect_apply_of_polar_eq_zero hxu
  have hr : reflect Q x y - y = x := by
    rw [reflect_apply hQx, hxy, neg_div, div_self hQx, neg_one_smul]
    abel
  have hc := commutatorElement_eichler (reflect_mem_orthogonalGroup Q x) hgu (hpu y hyP)
  rw [hr] at hc
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (reflect_mem_orthogonalGroup Q x)
    (eichler_mem_orthogonalGroup Q u y)

private theorem exists_eq_add_of_eichler {φ : V →ₗ[K] V} {u x y : V} (hu : Q u = 0)
    (hux : polar Q u x = 0) (huy : polar Q u y = 0) (hxy : polar Q x y = 1)
    (hE : ∀ v, φ (eichler Q u x v) = eichler Q u x (φ v)) :
    ∃ α β : K, φ u = α • u + β • x := by
  have hyu : polar Q y u = 0 := by rw [polar_comm]; exact huy
  have hyx : polar Q y x = 1 := by rw [polar_comm]; exact hxy
  have hEy : eichler Q u x y = y - u := by
    rw [eichler_apply hu hux, hyu, hyx]
    simp
  have h := hE y
  rw [hEy, map_sub, eichler_apply hu hux (φ y)] at h
  refine ⟨polar Q (φ y) x + Q x * polar Q (φ y) u, -polar Q (φ y) u, ?_⟩
  linear_combination (norm := module) (-1 : K) • h

private theorem smul_of_two_decomp {z u w x₁ x₂ : V} (hind : LinearIndependent K ![x₁, x₂])
    (huw : polar Q u w = 1) (hw₁ : polar Q x₁ w = 0) (hw₂ : polar Q x₂ w = 0)
    {α₁ β₁ α₂ β₂ : K} (h₁ : z = α₁ • u + β₁ • x₁) (h₂ : z = α₂ • u + β₂ • x₂) :
    ∃ a : K, z = a • u := by
  have hα : α₁ = α₂ := by
    have e := congrArg (fun t => polar Q t w) (h₁.symm.trans h₂)
    simpa [polar_add_left, polar_smul_left_eq, smul_eq_mul, huw, hw₁, hw₂] using e
  rw [← hα] at h₂
  have hlin : β₁ • x₁ + (-β₂) • x₂ = 0 := by
    have h12 := h₁.symm.trans h₂
    linear_combination (norm := module) h12
  have hβ : β₁ = 0 := (LinearIndependent.pair_iff.mp hind β₁ (-β₂) hlin).1
  exact ⟨α₁, by rw [h₁, hβ, zero_smul, add_zero]⟩

private theorem phi_formula_e {φ : V →ₗ[K] V} {a b : K} (P : HypPair Q)
    (hφe : φ P.e = a • P.e) (hφf : φ P.f = b • P.f) {x : V} (hx : x ∈ P.perp)
    (hE : ∀ v, φ (eichler Q P.e x v) = eichler Q P.e x (φ v)) :
    φ x = b • x + (Q x * (a - b)) • P.e := by
  have hEf : eichler Q P.e x P.f = P.f + x - Q x • P.e := by
    rw [eichler_apply P.Q_e (HypPair.mem_perp.mp hx).1 P.f, P.polar_fe,
      (HypPair.mem_perp.mp hx).2]
    module
  have h := hE P.f
  rw [hEf, hφf, map_smul, hEf] at h
  simp only [map_sub, map_add, map_smul, hφe, hφf] at h
  linear_combination (norm := module) h

private theorem phi_formula_f {φ : V →ₗ[K] V} {a b : K} (P : HypPair Q)
    (hφe : φ P.e = a • P.e) (hφf : φ P.f = b • P.f) {x : V} (hx : x ∈ P.perp)
    (hE : ∀ v, φ (eichler Q P.f x v) = eichler Q P.f x (φ v)) :
    φ x = a • x + (Q x * (b - a)) • P.f := by
  have hEe : eichler Q P.f x P.e = P.e + x - Q x • P.f := by
    rw [eichler_apply P.Q_f (HypPair.mem_perp.mp hx).2 P.e, P.polar_ef,
      (HypPair.mem_perp.mp hx).1]
    module
  have h := hE P.e
  rw [hEe, hφe, map_smul, hEe] at h
  simp only [map_sub, map_add, map_smul, hφe, hφf] at h
  linear_combination (norm := module) h

end Derived

theorem eq_smul_of_commute_derivedOrthogonal {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (P : HypPair Q)
    (hspan : P.perp ≤ Submodule.span K {x | x ∈ P.perp ∧ Q x ≠ 0})
    {x₁ x₂ : V} (hx₁ : x₁ ∈ P.perp) (hx₂ : x₂ ∈ P.perp) (hQx₁ : Q x₁ ≠ 0) (hQx₂ : Q x₂ ≠ 0)
    (hind : LinearIndependent K ![x₁, x₂]) (φ : V →ₗ[K] V)
    (hφ : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆,
      ∀ v, φ (g v) = g (φ v)) :
    ∃ c : K, ∀ v, φ v = c • v := by
  have hpe : ∀ y ∈ P.perp, polar Q P.e y = 0 := fun y hy => (HypPair.mem_perp.mp hy).1
  have hpf : ∀ y ∈ P.perp, polar Q P.f y = 0 := fun y hy => (HypPair.mem_perp.mp hy).2
  have hEe : ∀ x ∈ P.perp, Q x ≠ 0 → ∀ v, φ (eichler Q P.e x v) = eichler Q P.e x (φ v) :=
    fun x hx hQx v => hφ _ (eichler_mem_derived hQ P hpe hx hQx) v
  have hEf : ∀ x ∈ P.perp, Q x ≠ 0 → ∀ v, φ (eichler Q P.f x v) = eichler Q P.f x (φ v) :=
    fun x hx hQx v => hφ _ (eichler_mem_derived hQ P hpf hx hQx) v
  have hx₁0 : x₁ ≠ 0 := fun h => hQx₁ (by rw [h, QuadraticMap.map_zero])
  have hx₂0 : x₂ ≠ 0 := fun h => hQx₂ (by rw [h, QuadraticMap.map_zero])
  obtain ⟨y₁, hy₁, hxy₁⟩ := exists_perp_polar_one hQ P hx₁ hx₁0
  obtain ⟨y₂, hy₂, hxy₂⟩ := exists_perp_polar_one hQ P hx₂ hx₂0
  have hx₁e : polar Q P.e x₁ = 0 := (HypPair.mem_perp.mp hx₁).1
  have hx₂e : polar Q P.e x₂ = 0 := (HypPair.mem_perp.mp hx₂).1
  have hx₁f : polar Q P.f x₁ = 0 := (HypPair.mem_perp.mp hx₁).2
  have hx₂f : polar Q P.f x₂ = 0 := (HypPair.mem_perp.mp hx₂).2
  have hfx₁ : polar Q x₁ P.f = 0 := by rw [polar_comm]; exact hx₁f
  have hfx₂ : polar Q x₂ P.f = 0 := by rw [polar_comm]; exact hx₂f
  have hex₁ : polar Q x₁ P.e = 0 := by rw [polar_comm]; exact hx₁e
  have hex₂ : polar Q x₂ P.e = 0 := by rw [polar_comm]; exact hx₂e
  obtain ⟨a, hφe⟩ : ∃ a : K, φ P.e = a • P.e := by
    obtain ⟨α₁, β₁, h₁⟩ :=
      exists_eq_add_of_eichler P.Q_e hx₁e (hpe y₁ hy₁) hxy₁ (hEe x₁ hx₁ hQx₁)
    obtain ⟨α₂, β₂, h₂⟩ :=
      exists_eq_add_of_eichler P.Q_e hx₂e (hpe y₂ hy₂) hxy₂ (hEe x₂ hx₂ hQx₂)
    exact smul_of_two_decomp hind P.polar_ef hfx₁ hfx₂ h₁ h₂
  obtain ⟨b, hφf⟩ : ∃ b : K, φ P.f = b • P.f := by
    obtain ⟨α₁, β₁, h₁⟩ :=
      exists_eq_add_of_eichler P.Q_f hx₁f (hpf y₁ hy₁) hxy₁ (hEf x₁ hx₁ hQx₁)
    obtain ⟨α₂, β₂, h₂⟩ :=
      exists_eq_add_of_eichler P.Q_f hx₂f (hpf y₂ hy₂) hxy₂ (hEf x₂ hx₂ hQx₂)
    exact smul_of_two_decomp hind P.polar_fe hex₁ hex₂ h₁ h₂
  have hba : b = a := by
    have hf1 := phi_formula_e P hφe hφf hx₁ (hEe x₁ hx₁ hQx₁)
    have hf2 := phi_formula_f P hφe hφf hx₁ (hEf x₁ hx₁ hQx₁)
    have h1 : polar Q P.e (φ x₁) = 0 := by
      rw [hf1, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hx₁e, P.polar_ee]
      ring
    have h2 : polar Q P.e (φ x₁) = Q x₁ * (b - a) := by
      rw [hf2, polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hx₁e, P.polar_ef]
      ring
    have h3 : Q x₁ * (b - a) = 0 := by rw [← h2]; exact h1
    exact sub_eq_zero.mp ((mul_eq_zero.mp h3).resolve_left hQx₁)
  have haniso : ∀ x ∈ P.perp, Q x ≠ 0 → φ x = a • x := by
    intro x hx hQx
    rw [phi_formula_e P hφe hφf hx (hEe x hx hQx), hba, sub_self, mul_zero, zero_smul, add_zero]
  have hperp : ∀ w ∈ P.perp, φ w = a • w := by
    have hEq : Set.EqOn ⇑φ ⇑(a • (LinearMap.id : V →ₗ[K] V)) {x | x ∈ P.perp ∧ Q x ≠ 0} := by
      rintro x ⟨hx, hQx⟩
      rw [LinearMap.smul_apply, LinearMap.id_apply]
      exact haniso x hx hQx
    intro w hw
    simpa using LinearMap.eqOn_span' hEq (hspan hw)
  refine ⟨a, fun v => ?_⟩
  have hv := P.eq_add_proj v
  have hproj : φ (P.proj v) = a • P.proj v := hperp _ (P.proj_mem_perp v)
  have hφf' : φ P.f = a • P.f := by rw [hφf, hba]
  calc φ v = φ (polar Q v P.f • P.e + polar Q v P.e • P.f + P.proj v) := congrArg φ hv
    _ = a • v := by
      rw [map_add, map_add, map_smul, map_smul, hφe, hφf', hproj]
      conv_rhs => rw [hv]
      module

theorem stroth_2_4_omegaMinus (K : Type) [Field K] [Finite K] {m : ℕ} (hm : 2 ≤ m) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (f : (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) →ₗ[K] (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K))
    (hf : ∀ A ∈ StatedOmega (StatedQuadMinus m K b c),
      ∀ v, f ((A : Matrix _ _ K) *ᵥ v) = (A : Matrix _ _ K) *ᵥ f v) :
    ∃ c : K, ∀ v, f v = c • v := by
  have hQ : (polarBilin (quadMinus m K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite m K hirr
  have hcoe : ⇑(quadMinus m K b c) = StatedQuadMinus m K b c := coe_quadMinus m K b c
  have key := statedOmega_eq_comap hcoe
  have hφ : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus m K b c)⁆, ∀ v, f (g v) = g (f v) := by
    intro g hg v
    obtain ⟨A, hAg⟩ : ∃ A : GL (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K,
        toLinEquiv _ K A = g :=
      ⟨(toLinEquiv _ K).symm g, (toLinEquiv _ K).apply_symm_apply g⟩
    have hA : A ∈ StatedOmega (StatedQuadMinus m K b c) := by
      rw [key, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, hAg]
      exact hg
    have hgA : ∀ w, g w = (A : Matrix _ _ K) *ᵥ w := fun w => by
      rw [← hAg, toLinEquiv_apply]
    rw [hgA v, hf A hA v, hgA (f v)]
  obtain ⟨i0⟩ : Nonempty (Fin (m - 1)) := ⟨⟨0, by omega⟩⟩
  obtain ⟨P, hPdef⟩ : ∃ P : HypPair (quadMinus m K b c), P = minusPair K b c i0 := ⟨_, rfl⟩
  have hPe : P.e = Pi.single (Sum.inl i0) 1 := by rw [hPdef, minusPair_e]
  have hPf : P.f = Pi.single (Sum.inr (Sum.inl i0)) 1 := by rw [hPdef, minusPair_f]
  have hmem : ∀ w, w ∈ P.perp ↔ w (Sum.inr (Sum.inl i0)) = 0 ∧ w (Sum.inl i0) = 0 := by
    intro w
    rw [HypPair.mem_perp, hPe, hPf, polar_single_inl_quadMinus, polar_single_inr_quadMinus]
  set x₁ : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 0)) 1 with hx₁
  set x₂ : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K := Pi.single (Sum.inr (Sum.inr 1)) 1 with hx₂
  have hc0 : c ≠ 0 := by simpa using hirr 0
  have hQx₁ : quadMinus m K b c x₁ = 1 := by
    rw [hx₁, quadMinus_apply]
    simp [Pi.single_apply]
  have hQx₂ : quadMinus m K b c x₂ = c := by
    rw [hx₂, quadMinus_apply]
    simp [Pi.single_apply]
  have hx₁P : x₁ ∈ P.perp := by
    rw [hmem, hx₁]
    simp [Pi.single_apply]
  have hx₂P : x₂ ∈ P.perp := by
    rw [hmem, hx₂]
    simp [Pi.single_apply]
  have hS₁ : x₁ ∈ {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} :=
    ⟨hx₁P, by rw [hQx₁]; exact one_ne_zero⟩
  have hS₂ : x₂ ∈ {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} :=
    ⟨hx₂P, by rw [hQx₂]; exact hc0⟩
  have hind : LinearIndependent K ![x₁, x₂] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h0 := congrFun hst (Sum.inr (Sum.inr 0))
    have h1 := congrFun hst (Sum.inr (Sum.inr 1))
    simp [hx₁, hx₂, Pi.single_apply] at h0 h1
    exact ⟨h0, h1⟩
  have hspan_of : ∀ v : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K, v ∈ P.perp →
      quadMinus m K b c v = 0 → polar (quadMinus m K b c) v x₁ = 0 →
        v ∈ Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} := by
    intro v hv hQv hvx
    have hsum : v + x₁ ∈ {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} := by
      refine ⟨P.perp.add_mem hv hx₁P, ?_⟩
      rw [QuadraticMap.map_add (quadMinus m K b c) v x₁, hQv, hQx₁, hvx]
      norm_num
    have h : v + x₁ - x₁ ∈ Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} :=
      Submodule.sub_mem _ (Submodule.subset_span hsum) (Submodule.subset_span hS₁)
    simpa using h
  have hinr : ∀ j : Fin 2, (Pi.single (Sum.inr (Sum.inr j)) (1 : K) :
      Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
        Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} :=
    Fin.forall_fin_two.mpr ⟨Submodule.subset_span hS₁, Submodule.subset_span hS₂⟩
  have hbasis : ∀ k : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2, k ≠ Sum.inl i0 →
      k ≠ Sum.inr (Sum.inl i0) →
      (Pi.single k (1 : K) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈
        Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} := by
    intro k hk1 hk2
    rcases k with i | i | j
    · have hi : i ≠ i0 := fun h => hk1 (congrArg Sum.inl h)
      have hmemi : (Pi.single (Sum.inl i) (1 : K) :
          Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈ P.perp :=
        (hmem _).mpr ⟨by simp [Pi.single_apply], by simp [Pi.single_apply, Ne.symm hi]⟩
      have hpol : polar (quadMinus m K b c) (Pi.single (Sum.inl i) (1 : K)) x₁ = 0 := by
        rw [polar_single_inl_quadMinus, hx₁]
        simp [Pi.single_apply]
      exact hspan_of _ hmemi (quadMinus_single_inl i) hpol
    · have hi : i ≠ i0 := fun h => hk2 (congrArg Sum.inr (congrArg Sum.inl h))
      have hmemi : (Pi.single (Sum.inr (Sum.inl i)) (1 : K) :
          Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) ∈ P.perp :=
        (hmem _).mpr ⟨by simp [Pi.single_apply, Ne.symm hi], by simp [Pi.single_apply]⟩
      have hpol : polar (quadMinus m K b c) (Pi.single (Sum.inr (Sum.inl i)) (1 : K)) x₁ = 0 := by
        rw [polar_single_inr_quadMinus, hx₁]
        simp [Pi.single_apply]
      exact hspan_of _ hmemi (quadMinus_single_inr i) hpol
    · exact hinr j
  have hspan : P.perp ≤ Submodule.span K {x | x ∈ P.perp ∧ quadMinus m K b c x ≠ 0} := by
    intro w hw
    have hw' := (hmem w).mp hw
    have hdec : w = ∑ k, Pi.single k (w k) := by
      funext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [hdec]
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk0 : k = Sum.inl i0 ∨ k = Sum.inr (Sum.inl i0)
    · have hwk : w k = 0 := by
        rcases hk0 with rfl | rfl
        · exact hw'.2
        · exact hw'.1
      rw [hwk]
      simp
    · have hsc : (Pi.single k (w k) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) =
          w k • (Pi.single k (1 : K) : Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → K) := by
        funext j
        simp [Pi.single_apply]
      rw [hsc]
      exact Submodule.smul_mem _ _
        (hbasis k (fun h => hk0 (Or.inl h)) (fun h => hk0 (Or.inr h)))
  have hQx₁' : quadMinus m K b c x₁ ≠ 0 := by rw [hQx₁]; exact one_ne_zero
  have hQx₂' : quadMinus m K b c x₂ ≠ 0 := by rw [hQx₂]; exact hc0
  exact eq_smul_of_commute_derivedOrthogonal hQ P hspan hx₁P hx₂P hQx₁' hQx₂' hind f hφ

end CFSG.RankThree.GF2n.Stroth80
