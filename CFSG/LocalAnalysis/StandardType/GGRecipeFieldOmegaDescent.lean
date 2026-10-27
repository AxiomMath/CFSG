module

public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldOmegaGroup
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldLinearLang
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.GroupTheory.WeirSylow QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus quadPlus_apply quadMinus_apply)

namespace RecipeFieldOmega

section Descent

variable {K : Type} [Field K] (K₀ : Subfield K)

@[expose] def inclVec {ι : Type*} (w : ι → K₀) : ι → K := fun i => (w i : K)

theorem inclVec_apply {ι : Type*} (w : ι → K₀) (i : ι) : inclVec K₀ w i = w i := rfl

theorem inclVec_add {ι : Type*} (w w' : ι → K₀) :
    inclVec K₀ (w + w') = inclVec K₀ w + inclVec K₀ w' := by
  funext i
  simp [inclVec]

theorem inclVec_smul {ι : Type*} (a : K₀) (w : ι → K₀) :
    inclVec K₀ (a • w) = (a : K) • inclVec K₀ w := by
  funext i
  simp [inclVec]

theorem inclVec_injective {ι : Type*} : Function.Injective (inclVec (ι := ι) K₀) :=
  fun _ _ h => funext fun i => Subtype.ext (congrFun h i)

theorem inclVec_single {ι : Type*} [DecidableEq ι] (i : ι) :
    inclVec K₀ (Pi.single i 1) = Pi.single i 1 := by
  funext j
  by_cases h : j = i
  · subst h
    simp [inclVec]
  · simp [inclVec, h]

theorem eq_of_forall_inclVec {d : ℕ} {Q₁ Q₂ : QuadraticForm K (Fin d → K)}
    (h : ∀ w : Fin d → K₀, Q₁ (inclVec K₀ w) = Q₂ (inclVec K₀ w)) : Q₁ = Q₂ := by
  rw [← toQuadraticMap_toBilin Q₁ (Pi.basisFun K (Fin d)),
    ← toQuadraticMap_toBilin Q₂ (Pi.basisFun K (Fin d))]
  congr 1
  refine LinearMap.ext_basis (Pi.basisFun K (Fin d)) (Pi.basisFun K (Fin d)) fun i j => ?_
  rw [toBilin_apply, toBilin_apply]
  have h1 : ∀ k, Q₁ (Pi.basisFun K (Fin d) k) = Q₂ (Pi.basisFun K (Fin d) k) := fun k => by
    rw [Pi.basisFun_apply, ← inclVec_single K₀ k]
    exact h _
  have h2 : Q₁ (Pi.basisFun K (Fin d) i + Pi.basisFun K (Fin d) j) =
      Q₂ (Pi.basisFun K (Fin d) i + Pi.basisFun K (Fin d) j) := by
    rw [Pi.basisFun_apply, Pi.basisFun_apply, ← inclVec_single K₀ i, ← inclVec_single K₀ j,
      ← inclVec_add]
    exact h _
  simp only [polar, h1, h2]

variable {K₀}

theorem coe_polar_subfield {M : Type*} [AddCommGroup M] (f : M → K₀) (x y : M) :
    ((polar f x y : K₀) : K) = polar (fun m => (f m : K)) x y := by
  simp [polar]

@[expose] noncomputable def descForm {d : ℕ} (Q' : QuadraticForm K (Fin d → K))
    (hQ' : ∀ w : Fin d → K₀, Q' (inclVec K₀ w) ∈ K₀) : QuadraticForm K₀ (Fin d → K₀) :=
  QuadraticMap.ofPolar (fun w => ⟨Q' (inclVec K₀ w), hQ' w⟩)
    (fun a w => Subtype.ext (by
      change Q' (inclVec K₀ (a • w)) = (a : K) * (a : K) * Q' (inclVec K₀ w)
      rw [inclVec_smul, QuadraticMap.map_smul, smul_eq_mul]))
    (fun x x' y => Subtype.ext (by
      rw [Subfield.coe_add, coe_polar_subfield, coe_polar_subfield, coe_polar_subfield]
      change polar Q' (inclVec K₀ (x + x')) (inclVec K₀ y) =
        polar Q' (inclVec K₀ x) (inclVec K₀ y) + polar Q' (inclVec K₀ x') (inclVec K₀ y)
      rw [inclVec_add, polar_add_left]))
    (fun a x y => Subtype.ext (by
      rw [smul_eq_mul, Subfield.coe_mul, coe_polar_subfield, coe_polar_subfield]
      change polar Q' (inclVec K₀ (a • x)) (inclVec K₀ y) =
        (a : K) * polar Q' (inclVec K₀ x) (inclVec K₀ y)
      rw [inclVec_smul, polar_smul_left, smul_eq_mul]))

theorem descForm_apply {d : ℕ} (Q' : QuadraticForm K (Fin d → K))
    (hQ' : ∀ w : Fin d → K₀, Q' (inclVec K₀ w) ∈ K₀) (w : Fin d → K₀) :
    (descForm Q' hQ' w : K) = Q' (inclVec K₀ w) := rfl

theorem coe_polar_descForm {d : ℕ} (Q' : QuadraticForm K (Fin d → K))
    (hQ' : ∀ w : Fin d → K₀, Q' (inclVec K₀ w) ∈ K₀) (x y : Fin d → K₀) :
    ((polar (descForm Q' hQ') x y : K₀) : K) = polar Q' (inclVec K₀ x) (inclVec K₀ y) := by
  rw [polar, polar, Subfield.coe_sub, Subfield.coe_sub, descForm_apply, descForm_apply,
    descForm_apply, inclVec_add]

theorem polar_eq_sum_single {d : ℕ} (Q' : QuadraticForm K (Fin d → K)) (u v : Fin d → K) :
    polar Q' u v = ∑ j, v j * polar Q' u (Pi.single j 1) := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : K) : Fin d → K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have h := congrArg (polarBilin Q' u) hv
  rw [map_sum] at h
  rw [← polarBilin_apply_apply, h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul, polarBilin_apply_apply]

theorem nondegenerate_descForm {d : ℕ} {Q' : QuadraticForm K (Fin d → K)}
    (hQ' : ∀ w : Fin d → K₀, Q' (inclVec K₀ w) ∈ K₀) (hnd : (polarBilin Q').Nondegenerate) :
    (polarBilin (descForm Q' hQ')).Nondegenerate := by
  have key : ∀ x : Fin d → K₀, (∀ y, polar (descForm Q' hQ') x y = 0) → x = 0 := by
    intro x hx
    have h0 : ∀ v, polar Q' (inclVec K₀ x) v = 0 := by
      intro v
      rw [polar_eq_sum_single]
      refine Finset.sum_eq_zero fun j _ => ?_
      have := congrArg (fun z : K₀ => (z : K)) (hx (Pi.single j 1))
      rw [coe_polar_descForm, inclVec_single, Subfield.coe_zero] at this
      rw [this, mul_zero]
    have h1 : inclVec K₀ x = 0 := hnd.1 _ fun v => by rw [polarBilin_apply_apply, h0]
    exact inclVec_injective K₀ (h1.trans (by funext i; simp [inclVec]))
  refine ⟨fun x hx => key x fun y => ?_, fun y hy => key y fun x => ?_⟩
  · rw [← polarBilin_apply_apply]
    exact hx y
  · rw [polar_comm, ← polarBilin_apply_apply]
    exact hy x

theorem nonempty_isometry_of_descForm {d : ℕ} {Q' : QuadraticForm K (Fin d → K)}
    {hQ' : ∀ w : Fin d → K₀, Q' (inclVec K₀ w) ∈ K₀} {ι₁ : Type} [Fintype ι₁] [DecidableEq ι₁]
    {Q₁ : QuadraticForm K (ι₁ → K)} {Q₁₀ : QuadraticForm K₀ (ι₁ → K₀)}
    (hQ₁ : ∀ w, Q₁ (inclVec K₀ w) = Q₁₀ w) (e : (descForm Q' hQ').IsometryEquiv Q₁₀) :
    Nonempty (Q'.IsometryEquiv Q₁) := by
  set M := LinearMap.toMatrix' e.toLinearEquiv.toLinearMap
  set N := LinearMap.toMatrix' e.toLinearEquiv.symm.toLinearMap
  have hMN : M * N = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  have hNM : N * M = 1 := by
    rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_id]
    congr 1
    ext x
    simp
  have hMNK : M.map K₀.subtype * N.map K₀.subtype = 1 := by
    rw [← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hNMK : N.map K₀.subtype * M.map K₀.subtype = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  let E : (Fin d → K) ≃ₗ[K] (ι₁ → K) := Matrix.toLin'OfInv hNMK hMNK
  have hE : ∀ w, E (inclVec K₀ w) = inclVec K₀ (e w) := by
    intro w
    change Matrix.mulVec (M.map K₀.subtype) (inclVec K₀ w) = inclVec K₀ (e w)
    have h1 := RingHom.map_mulVec K₀.subtype M w
    have h2 : Matrix.mulVec M w = e w := LinearMap.toMatrix'_mulVec _ w
    funext i
    change _ = ((e w i : K₀) : K)
    rw [← h2]
    exact (h1 i).symm
  have hQ : Q₁.comp E.toLinearMap = Q' := eq_of_forall_inclVec K₀ fun w => by
    rw [QuadraticMap.comp_apply, LinearEquiv.coe_coe, hE, hQ₁, e.map_app, descForm_apply]
  refine ⟨⟨E, fun v => ?_⟩⟩
  change Q₁ (E v) = Q' v
  rw [← hQ]
  rfl

theorem rootFree_of_odd [CharP K 2] {σ : K ≃+* K} {p : ℕ} (hp : Odd p) (hσp : σ ^ p = 1)
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) {β γ : K₀} (h : ∀ s : K₀, s ^ 2 + β * s + γ ≠ 0) :
    ∀ s : K, s ^ 2 + (β : K) * s + γ ≠ 0 := by
  intro s hs
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hβ : σ β = β := (hK₀ _).1 β.2
  have hγ : σ γ = γ := (hK₀ _).1 γ.2
  have hσs : σ s ^ 2 + (β : K) * σ s + γ = 0 := by
    have := congrArg σ hs
    rwa [map_add, map_add, map_mul, map_pow, hβ, hγ, map_zero] at this
  have hfac : (σ s - s) * (σ s + s + β) = 0 := by linear_combination hσs - hs
  have hσσ : σ (σ s) = s := by
    rcases mul_eq_zero.1 hfac with h0 | h0
    · rw [sub_eq_zero.1 h0, sub_eq_zero.1 h0]
    · have e : σ s = s + β := by linear_combination h0 - (s + β) * h2
      rw [e, map_add, e, hβ]
      linear_combination (β : K) * h2
  have hpow : ∀ j : ℕ, ((σ ^ 2) ^ j) s = s := by
    intro j
    induction j with
    | zero => rfl
    | succ j ih => rw [pow_succ', RingAut.mul_apply, ih, _root_.sq, RingAut.mul_apply, hσσ]
  obtain ⟨k, hk⟩ := hp
  have hσ1 : σ s = s := by
    have e : σ = (σ ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = p + 1 by omega, pow_succ, hσp, one_mul]
    rw [e, hpow]
  exact h ⟨s, (hK₀ s).2 hσ1⟩ (Subtype.ext (by simpa using hs))

theorem quadPlus_inclVec (n : ℕ) (w : Fin n ⊕ Fin n → K₀) :
    quadPlus n K (inclVec K₀ w) = quadPlus n K₀ w := by
  simp [quadPlus_apply, inclVec]

theorem quadMinus_inclVec (n : ℕ) (β γ : K₀) (w : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K₀) :
    quadMinus n K β γ (inclVec K₀ w) = quadMinus n K₀ β γ w := by
  simp [quadMinus_apply, inclVec]

theorem isPlusType_descForm_iff [Finite K] [CharP K 2] {σ : K ≃+* K} {p : ℕ} (hp : Odd p)
    (hσp : σ ^ p = 1) (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) {n : ℕ} (hn : 1 ≤ n)
    {Q' : QuadraticForm K (Fin (2 * n) → K)} (hQ' : ∀ w : Fin (2 * n) → K₀, Q' (inclVec K₀ w) ∈ K₀)
    (hnd : (polarBilin Q').Nondegenerate) :
    IsPlusType (descForm Q' hQ') ↔ IsPlusType Q' := by
  have hdim : Module.finrank K₀ (Fin (2 * n) → K₀) = 2 * n := Module.finrank_fin_fun K₀
  rcases exists_isometry_quadPlus_or_quadMinus (descForm Q' hQ') (nondegenerate_descForm hQ' hnd)
    hn hdim with he | ⟨β, γ, hβγ, he⟩
  · obtain ⟨e⟩ := he
    obtain ⟨e'⟩ := nonempty_isometry_of_descForm (quadPlus_inclVec n) e
    exact ⟨fun _ => (isPlusType_congr e').2 (isPlusType_quadPlus K n),
      fun _ => (isPlusType_congr e).2 (isPlusType_quadPlus K₀ n)⟩
  · obtain ⟨e⟩ := he
    obtain ⟨e'⟩ := nonempty_isometry_of_descForm (quadMinus_inclVec n β γ) e
    exact ⟨fun h => absurd ((isPlusType_congr e).1 h) (not_isPlusType_quadMinus hn hβγ),
      fun h => absurd ((isPlusType_congr e').1 h)
        (not_isPlusType_quadMinus hn (rootFree_of_odd hp hσp hK₀ hβγ))⟩

end Descent

end RecipeFieldOmega

end CFSG.StandardType
