module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameInd
public import CFSG.GroupTheory.ABGLocalTools.SL2FieldAutSemilinear

public section

open Polynomial Module
open scoped Matrix

namespace CFSG.StandardType

namespace WitSpBlk

@[expose] def BlockNormal (K : Type) [Field K] (D : Type) [AddCommGroup D] [Module K D]
    (c : D →ₗ[K] D) : Prop :=
  ∀ β₀ β₁ : LinearMap.BilinForm K D, β₀.IsAlt → β₁.IsAlt → β₀.Nondegenerate →
    β₁.Nondegenerate → (∀ u v, β₀ (c u) (c v) = β₀ u v) → (∀ u v, β₁ (c u) (c v) = β₁ u v) →
    ∃ μ : D ≃ₗ[K] D, (∀ u, μ (c u) = c (μ u)) ∧ ∀ u v, β₁ (μ u) (μ v) = β₀ u v

section Twist

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

theorem twist_aeval {γ : LinearMap.BilinForm K L} {ζ θ : L}
    (h : ∀ x y, γ (ζ * x) y = γ x (θ * y)) (P : K[X]) (x y : L) :
    γ (aeval ζ P * x) y = γ x (aeval θ P * y) := by
  induction P using Polynomial.induction_on generalizing x y with
  | C a =>
    simp only [aeval_C]
    rw [← Algebra.smul_def, ← Algebra.smul_def, LinearMap.map_smul₂, map_smul]
  | add P Q hP hQ =>
    rw [map_add, map_add, add_mul, add_mul, map_add, LinearMap.add_apply, hP, hQ, map_add]
  | monomial m a ih =>
    have e1 : aeval ζ (C a * X ^ (m + 1)) * x = aeval ζ (C a * X ^ m) * (ζ * x) := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X, mul_assoc]
    have e2 : aeval θ (C a * X ^ (m + 1)) * y = θ * (aeval θ (C a * X ^ m) * y) := by
      rw [pow_succ, ← mul_assoc, map_mul, aeval_X]
      ring
    rw [e1, ih, h, e2]

end Twist

section SelfDual

variable {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

theorem pow_pred_mul_pred {M : Type*} [Monoid M] {ζ : M} (hp : 2 ≤ p) (hζ : ζ ^ p = 1) :
    ζ ^ ((p - 1) * (p - 1)) = ζ := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 2 := ⟨p - 2, by omega⟩
  have e : (q + 2 - 1) * (q + 2 - 1) = (q + 2) * q + 1 := by
    rw [show q + 2 - 1 = q + 1 by omega]
    ring
  rw [e, pow_succ, pow_mul, hζ, one_pow, one_mul]

theorem blockNormal_selfDual (hp : p.Prime) (hp2 : p ≠ 2) (hpK : (p : K) ≠ 0)
    (hgd : g ∣ cyclotomic p K) (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g = 0) :
    BlockNormal K (AdjoinRoot g) (LinearMap.mulLeft K (AdjoinRoot.root g)) := by
  intro β₀ β₁ halt₀ halt₁ hnd₀ hnd₁ hinv₀ hinv₁
  classical
  have : Module.Finite K (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible g).ne_zero).finite
  have : Finite (AdjoinRoot g) := Module.finite_of_finite K
  set ζ := AdjoinRoot.root g with hζdef
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζζ : ζ * ζ ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hζp]
  set σ : AdjoinRoot g →ₐ[K] AdjoinRoot g :=
    AdjoinRoot.liftAlgHom g (Algebra.ofId K _) (ζ ^ (p - 1)) (by
      rw [← hσ, aeval_def]
      rfl) with hσdef
  have hσζ : σ ζ = ζ ^ (p - 1) := AdjoinRoot.liftAlgHom_root _ _ _ _
  have hσσ' : σ.comp σ = AlgHom.id K _ := AdjoinRoot.algHom_ext (by
    rw [AlgHom.comp_apply, hσζ, map_pow, hσζ, ← pow_mul, AlgHom.id_apply,
      pow_pred_mul_pred hp.two_le hζp])
  have hσσ : ∀ x, σ (σ x) = x := fun x => AlgHom.congr_fun hσσ' x
  set σe : AdjoinRoot g ≃+* AdjoinRoot g := (AlgEquiv.ofAlgHom σ σ hσσ' hσσ').toRingEquiv
    with hσe
  have hσe : ∀ x, σe x = σ x := fun x => rfl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have horder : orderOf σe = 2 := by
    refine orderOf_eq_prime (RingEquiv.ext fun x => ?_) fun h1 => ?_
    · rw [pow_two, RingAut.mul_apply, hσe, hσe, hσσ]
      rfl
    · have h2 : σe ζ = ζ := by rw [h1]; rfl
      rw [hσe, hσζ] at h2
      have h3 : ζ ^ (p - 2) = 1 := by
        have h4 : ζ ^ (p - 2) * ζ = 1 * ζ := by
          rw [one_mul, ← pow_succ, show p - 2 + 1 = p - 1 by have := hp.two_le; omega, h2]
        exact mul_right_cancel₀ (hζ.ne_zero hp.ne_zero) h4
      have h5 := (hζ.pow_eq_one_iff_dvd _).mp h3
      have h6 : 0 < p - 2 := by
        have := hp.two_le
        omega
      have := Nat.le_of_dvd h6 h5
      omega
  have hadj : ∀ β : LinearMap.BilinForm K (AdjoinRoot g),
      (∀ u v, β (LinearMap.mulLeft K ζ u) (LinearMap.mulLeft K ζ v) = β u v) →
        ∀ a x y, β (a * x) y = β x (σ a * y) := by
    intro β hβ a x y
    have htw : ∀ x y, β (ζ * x) y = β x (ζ ^ (p - 1) * y) := fun x y => by
      have := hβ x (ζ ^ (p - 1) * y)
      rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply, ← mul_assoc, hζζ, one_mul] at this
      exact this
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective a
    rw [← AdjoinRoot.aeval_eq, twist_aeval htw, ← hσζ, Polynomial.aeval_algHom_apply]
  have hadj₀ := hadj β₀ hinv₀
  have hadj₁ := hadj β₁ hinv₁
  set A := β₁.symmCompOfNondegenerate β₀ hnd₀ with hA
  have hAl : ∀ w v, β₀ (A w) v = β₁ w v := fun w v =>
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply β₁ hnd₀ v w
  have hAmul : ∀ a w, A (a * w) = a * A w := by
    intro a w
    refine sub_eq_zero.mp (hnd₀.1 _ fun v => ?_)
    rw [LinearMap.map_sub₂, hAl, hadj₁, ← hAl, hadj₀, sub_self]
  set a₀ := A 1 with ha₀
  have hAa : ∀ w, A w = a₀ * w := fun w => by
    have h := hAmul w 1
    rw [mul_one] at h
    rw [h]
    exact mul_comm _ _
  have hσa : σ a₀ = a₀ := by
    have h1 : ∀ u v, β₀ (a₀ * u) v = β₀ (σ a₀ * u) v := by
      intro u v
      rw [← hAa, hAl, ← halt₁.neg_eq, ← hAl, hAa, ← halt₀.neg_eq, neg_neg, hadj₀, hσσ]
    have h2 := hnd₀.1 (a₀ * 1 - σ a₀ * 1) fun v => by rw [LinearMap.map_sub₂, h1, sub_self]
    rw [mul_one, mul_one, sub_eq_zero] at h2
    exact h2.symm
  have ha₀0 : a₀ ≠ 0 := by
    intro h0
    have h1 := hnd₁.1 1 fun v => by rw [← hAl, hAa, h0, zero_mul, LinearMap.map_zero₂]
    exact one_ne_zero h1
  obtain ⟨μ, hμ⟩ := CFSG.ABGLocalTools.exists_prod_pow_eq σe (c := a₀⁻¹)
    (by rw [hσe, map_inv₀, hσa])
  rw [horder, Finset.prod_range_succ, Finset.prod_range_one, pow_zero, pow_one] at hμ
  change μ * σ μ = a₀⁻¹ at hμ
  have hμ0 : μ ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hμ
    exact inv_ne_zero ha₀0 hμ.symm
  refine ⟨LinearEquiv.ofLinearMap (LinearMap.mulLeft K μ) (LinearMap.mulLeft K μ⁻¹)
    (LinearMap.ext fun x => ?_) (LinearMap.ext fun x => ?_), fun u => ?_, fun u v => ?_⟩
  · simp [← mul_assoc, mul_inv_cancel₀ hμ0]
  · simp [← mul_assoc, inv_mul_cancel₀ hμ0]
  · simp only [LinearEquiv.coe_ofLinearMap, LinearMap.mulLeft_apply]
    ring
  · simp only [LinearEquiv.coe_ofLinearMap, LinearMap.mulLeft_apply]
    calc β₁ (μ * u) (μ * v) = β₀ (a₀ * (μ * u)) (μ * v) := by rw [← hAl, hAa]
      _ = β₀ (a₀ * (μ * u)) (σ (σ μ) * v) := by rw [hσσ]
      _ = β₀ (σ μ * (a₀ * (μ * u))) v := (hadj₀ (σ μ) _ _).symm
      _ = β₀ ((μ * σ μ * a₀) * u) v := by
        rw [show σ μ * (a₀ * (μ * u)) = (μ * σ μ * a₀) * u by ring]
      _ = β₀ u v := by rw [hμ, inv_mul_cancel₀ ha₀0, one_mul]

end SelfDual

section Paired

variable {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)] {p : ℕ}

theorem blockNormal_paired (hp : p.Prime) (hpK : (p : K) ≠ 0) (hgd : g ∣ cyclotomic p K)
    (hσ : aeval (AdjoinRoot.root g ^ (p - 1)) g ≠ 0) :
    BlockNormal K (AdjoinRoot g × AdjoinRoot g)
      ((LinearMap.mulLeft K (AdjoinRoot.root g)).prodMap
        (LinearMap.mulLeft K (AdjoinRoot.root g ^ (p - 1)))) := by
  intro β₀ β₁ halt₀ halt₁ hnd₀ hnd₁ hinv₀ hinv₁
  classical
  have : Module.Finite K (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis (Fact.out : Irreducible g).ne_zero).finite
  set ζ := AdjoinRoot.root g with hζdef
  set θ := ζ ^ (p - 1) with hθ
  have hζ := NSFrame.root_isPrimitiveRoot (g := g) hp hpK hgd
  have hζθ : ζ * θ = 1 := by
    rw [hθ, ← pow_succ', Nat.sub_add_cancel hp.one_lt.le, hζ.pow_eq_one]
  have hθζ : θ * ζ = 1 := by rw [mul_comm, hζθ]
  have hgζ : aeval ζ g = 0 := by rw [hζdef, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  set c := (LinearMap.mulLeft K ζ).prodMap (LinearMap.mulLeft K θ) with hc
  have hcapp : ∀ x y : AdjoinRoot g, c (x, y) = (ζ * x, θ * y) := fun x y => rfl
  have hstruct : ∀ β : LinearMap.BilinForm K (AdjoinRoot g × AdjoinRoot g), β.IsAlt →
      (∀ u v, β (c u) (c v) = β u v) →
      (∀ a x y, β (a * x, 0) (0, y) = β (x, 0) (0, a * y)) ∧
        ∀ x₁ x₂ y₁ y₂, β (x₁, x₂) (y₁, y₂) = β (x₁, 0) (0, y₂) - β (y₁, 0) (0, x₂) := by
    intro β hβ hinv
    set γ₁₁ := β.compl₁₂ (LinearMap.inl K (AdjoinRoot g) (AdjoinRoot g))
      (LinearMap.inl K (AdjoinRoot g) (AdjoinRoot g)) with hγ₁₁
    set γ₂₂ := β.compl₁₂ (LinearMap.inr K (AdjoinRoot g) (AdjoinRoot g))
      (LinearMap.inr K (AdjoinRoot g) (AdjoinRoot g)) with hγ₂₂
    set π := β.compl₁₂ (LinearMap.inl K (AdjoinRoot g) (AdjoinRoot g))
      (LinearMap.inr K (AdjoinRoot g) (AdjoinRoot g)) with hπ
    have e11 : ∀ x y, γ₁₁ x y = β (x, 0) (y, 0) := fun x y => rfl
    have e22 : ∀ x y, γ₂₂ x y = β (0, x) (0, y) := fun x y => rfl
    have e12 : ∀ x y, π x y = β (x, 0) (0, y) := fun x y => rfl
    have h11 : ∀ x y, β (x, 0) (y, 0) = 0 := by
      have htw : ∀ x y, γ₁₁ (ζ * x) y = γ₁₁ x (θ * y) := fun x y => by
        have := hinv (x, 0) (θ * y, 0)
        rw [hcapp, hcapp, mul_zero, ← mul_assoc, hζθ, one_mul] at this
        rw [e11, e11, this]
      intro x y
      have h1 := twist_aeval htw g x ((aeval θ g)⁻¹ * y)
      rw [hgζ, zero_mul, mul_inv_cancel_left₀ hσ, LinearMap.map_zero₂] at h1
      rw [← e11, ← h1]
    have h22 : ∀ x y, β (0, x) (0, y) = 0 := by
      have htw : ∀ x y, γ₂₂ (θ * x) y = γ₂₂ x (ζ * y) := fun x y => by
        have := hinv (0, x) (0, ζ * y)
        rw [hcapp, hcapp, mul_zero, ← mul_assoc, hθζ, one_mul] at this
        rw [e22, e22, this]
      intro x y
      have h1 := twist_aeval htw g ((aeval θ g)⁻¹ * x) y
      rw [hgζ, zero_mul, mul_inv_cancel_left₀ hσ, map_zero] at h1
      rw [← e22, h1]
    refine ⟨fun a x y => ?_, fun x₁ x₂ y₁ y₂ => ?_⟩
    · have htw : ∀ x y, π (ζ * x) y = π x (ζ * y) := fun x y => by
        have := hinv (x, 0) (0, ζ * y)
        simp only [hcapp, mul_zero, ← mul_assoc, hθζ, one_mul] at this
        rw [e12, e12, this]
      obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective a
      rw [← e12, ← e12, ← AdjoinRoot.aeval_eq]
      exact twist_aeval htw P x y
    · have e : ∀ x₁ x₂ : AdjoinRoot g, ((x₁, x₂) : AdjoinRoot g × AdjoinRoot g) =
          (x₁, 0) + (0, x₂) := fun x₁ x₂ => by simp
      rw [e x₁ x₂, e y₁ y₂, LinearMap.map_add₂, map_add, map_add, h11, h22,
        ← hβ.neg_eq (y₁, 0) (0, x₂)]
      ring
  obtain ⟨h12₀, hdec₀⟩ := hstruct β₀ halt₀ hinv₀
  obtain ⟨h12₁, hdec₁⟩ := hstruct β₁ halt₁ hinv₁
  set π₀ := β₀.compl₁₂ (LinearMap.inl K (AdjoinRoot g) (AdjoinRoot g))
    (LinearMap.inr K (AdjoinRoot g) (AdjoinRoot g)) with hπ₀
  set π₁ := β₁.compl₁₂ (LinearMap.inl K (AdjoinRoot g) (AdjoinRoot g))
    (LinearMap.inr K (AdjoinRoot g) (AdjoinRoot g)) with hπ₁
  have e₀ : ∀ x y, π₀ x y = β₀ (x, 0) (0, y) := fun x y => rfl
  have e₁ : ∀ x y, π₁ x y = β₁ (x, 0) (0, y) := fun x y => rfl
  have hπnd : π₀.Nondegenerate := by
    refine ⟨fun x hx => ?_, fun y hy => ?_⟩
    · have h1 := hnd₀.1 (x, 0) fun v => by
        obtain ⟨v₁, v₂⟩ := v
        rw [hdec₀, ← e₀, hx, ← e₀, map_zero, sub_zero]
      exact congrArg Prod.fst h1
    · have h1 := hnd₀.2 (0, y) fun v => by
        obtain ⟨v₁, v₂⟩ := v
        rw [hdec₀, ← e₀, hy, ← e₀, LinearMap.map_zero₂, sub_zero]
      exact congrArg Prod.snd h1
  set A := LinearMap.BilinForm.symmCompOfNondegenerate π₁ π₀ hπnd with hA
  have hAl : ∀ w v, π₀ (A w) v = π₁ w v := fun w v =>
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply π₁ hπnd v w
  have hAmul : ∀ a w, A (a * w) = a * A w := by
    intro a w
    refine sub_eq_zero.mp (hπnd.1 _ fun v => ?_)
    rw [LinearMap.map_sub₂, hAl, e₁, h12₁, ← e₁, ← hAl, e₀, e₀, h12₀, sub_self]
  set a₀ := A 1 with ha₀
  have hAa : ∀ w, A w = a₀ * w := fun w => by
    have h := hAmul w 1
    rw [mul_one] at h
    rw [h]
    exact mul_comm _ _
  have ha₀0 : a₀ ≠ 0 := by
    intro h0
    have h1 := hnd₁.1 (1, 0) fun v => by
      obtain ⟨v₁, v₂⟩ := v
      rw [hdec₁, ← e₁, ← hAl, hAa, h0, zero_mul, LinearMap.map_zero₂, ← e₁, map_zero,
        sub_zero]
    exact one_ne_zero (congrArg Prod.fst h1)
  refine ⟨LinearEquiv.ofLinearMap ((LinearMap.mulLeft K a₀⁻¹).prodMap LinearMap.id)
    ((LinearMap.mulLeft K a₀).prodMap LinearMap.id) (LinearMap.ext fun x => ?_)
    (LinearMap.ext fun x => ?_), fun u => ?_, fun u v => ?_⟩
  · obtain ⟨x₁, x₂⟩ := x
    simp [← mul_assoc, inv_mul_cancel₀ ha₀0]
  · obtain ⟨x₁, x₂⟩ := x
    simp [← mul_assoc, mul_inv_cancel₀ ha₀0]
  · obtain ⟨u₁, u₂⟩ := u
    refine Prod.ext ?_ rfl
    simp only [LinearEquiv.coe_ofLinearMap, LinearMap.prodMap_apply, LinearMap.mulLeft_apply,
      hcapp]
    ring
  · obtain ⟨u₁, u₂⟩ := u
    obtain ⟨v₁, v₂⟩ := v
    simp only [LinearEquiv.coe_ofLinearMap, LinearMap.prodMap_apply, LinearMap.mulLeft_apply,
      LinearMap.id_apply]
    rw [hdec₁, hdec₀, ← e₁, ← e₁, ← hAl, ← hAl, hAa, hAa, mul_inv_cancel_left₀ ha₀0,
      mul_inv_cancel_left₀ ha₀0, e₀, e₀]

end Paired

@[expose] def BlockNormalMat (K : Type) [Field K] {e : ℕ} (C : Matrix (Fin e) (Fin e) K) :
    Prop :=
  ∀ γ₀ γ₁ : LinearMap.BilinForm K (Fin e → K), γ₀.IsAlt → γ₁.IsAlt → γ₀.Nondegenerate →
    γ₁.Nondegenerate → (∀ z z', γ₀ (C *ᵥ z) (C *ᵥ z') = γ₀ z z') →
    (∀ z z', γ₁ (C *ᵥ z) (C *ᵥ z') = γ₁ z z') →
    ∃ Φ : Matrix (Fin e) (Fin e) K, Φ * C = C * Φ ∧ ∀ z z', γ₁ (Φ *ᵥ z) (Φ *ᵥ z') = γ₀ z z'

theorem blockNormalMat_toMatrix {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D]
    {e : ℕ} (b : Basis (Fin e) K D) {c : D →ₗ[K] D} (h : BlockNormal K D c) :
    BlockNormalMat K (LinearMap.toMatrix b b c) := by
  intro γ₀ γ₁ halt₀ halt₁ hnd₀ hnd₁ hinv₀ hinv₁
  set E := b.equivFun with hE
  have hEc : ∀ x, LinearMap.toMatrix b b c *ᵥ E x = E (c x) := fun x => by
    rw [hE, Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  have hEμ : ∀ (μ : D →ₗ[K] D) x, LinearMap.toMatrix b b μ *ᵥ E x = E (μ x) := fun μ x => by
    rw [hE, Basis.equivFun_apply, Basis.equivFun_apply, LinearMap.toMatrix_mulVec_repr]
  set β₀ := γ₀.compl₁₂ (E : D →ₗ[K] (Fin e → K)) (E : D →ₗ[K] (Fin e → K)) with hβ₀
  set β₁ := γ₁.compl₁₂ (E : D →ₗ[K] (Fin e → K)) (E : D →ₗ[K] (Fin e → K)) with hβ₁
  have e₀ : ∀ u v, β₀ u v = γ₀ (E u) (E v) := fun u v => rfl
  have e₁ : ∀ u v, β₁ u v = γ₁ (E u) (E v) := fun u v => rfl
  have hnd : ∀ γ : LinearMap.BilinForm K (Fin e → K), γ.Nondegenerate →
      (γ.compl₁₂ (E : D →ₗ[K] (Fin e → K)) (E : D →ₗ[K] (Fin e → K))).Nondegenerate := by
    intro γ hγ
    refine ⟨fun u hu => E.injective ?_, fun v hv => E.injective ?_⟩
    · rw [map_zero]
      refine hγ.1 _ fun z => ?_
      have := hu (E.symm z)
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at this
      exact this
    · rw [map_zero]
      refine hγ.2 _ fun z => ?_
      have := hv (E.symm z)
      simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply] at this
      exact this
  obtain ⟨μ, hμc, hμ⟩ := h β₀ β₁ (fun u => halt₀ (E u)) (fun u => halt₁ (E u)) (hnd γ₀ hnd₀)
    (hnd γ₁ hnd₁) (fun u v => by rw [e₀, e₀, ← hEc, ← hEc, hinv₀])
    (fun u v => by rw [e₁, e₁, ← hEc, ← hEc, hinv₁])
  refine ⟨LinearMap.toMatrix b b (μ : D →ₗ[K] D), ?_, fun z z' => ?_⟩
  · rw [← LinearMap.toMatrix_mul, ← LinearMap.toMatrix_mul]
    congr 1
    exact LinearMap.ext fun u => hμc u
  · obtain ⟨u, rfl⟩ := E.surjective z
    obtain ⟨v, rfl⟩ := E.surjective z'
    rw [hEμ, hEμ, ← e₁, LinearEquiv.coe_coe, hμ, e₀]

end WitSpBlk

end CFSG.StandardType
