module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas

public section

namespace CFSG.RankThree.GF2n.Smith81

theorem det_restrict_homology {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Module.Finite K E] (W : Submodule K E) (f : E →ₗ[K] E) (hW : ∀ w ∈ W, f w ∈ W)
    {y : E} (hyW : y ∈ W) (hy0 : y ≠ 0) (ρ : K) (hfy : f y = ρ • y)
    (hf : ∀ w ∈ W, f w - w ∈ Submodule.span K {y}) :
    LinearMap.det (f.restrict hW) = ρ := by
  obtain ⟨v, hv⟩ : ∃ v : W, (v : E) = y := ⟨⟨y, hyW⟩, rfl⟩
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hy0 (by simpa using hv.symm)
  have hey : f.restrict hW v = ρ • v := by
    apply Subtype.ext
    simp [hv, hfy]
  have hp : Submodule.span K {v} ≤ (Submodule.span K {v}).comap (f.restrict hW) := by
    rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_comap, hey]
    exact Submodule.smul_mem _ ρ (Submodule.mem_span_singleton_self v)
  have hres : (f.restrict hW).restrict hp =
      (ρ • LinearMap.id : Submodule.span K {v} →ₗ[K] _) := by
    apply LinearMap.ext
    intro x
    obtain ⟨z, hz⟩ := x
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    simp [Subtype.ext_iff, hey, smul_comm a ρ v]
  have key : ∀ x : W, f.restrict hW x - x ∈ Submodule.span K {v} := by
    intro x
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (hf (x : E) x.2)
    refine Submodule.mem_span_singleton.2 ⟨a, Subtype.ext ?_⟩
    simpa [hv] using ha
  have hQ : (Submodule.span K {v}).mapQ (Submodule.span K {v}) (f.restrict hW) hp =
      LinearMap.id := LinearMap.ext fun x ↦ by
    induction x using Submodule.Quotient.induction_on with
    | _ w => simpa [Submodule.mapQ_apply, Submodule.Quotient.eq] using key w
  have hdet := (f.restrict hW).det_eq_det_mul_det (Submodule.span K {v}) hp
  rw [hres, hQ, LinearMap.det_smul, finrank_span_singleton hv0, pow_one,
    LinearMap.det_id, LinearMap.det_id, mul_one, mul_one] at hdet
  exact hdet

theorem det_restrict_mul_det_restrict {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Module.Finite K E] (B : E →ₗ[K] E →ₗ[K] K) (W₁ W₂ : Submodule K E)
    (h₁ : ∀ a ∈ W₁, (∀ b ∈ W₂, B a b = 0) → a = 0)
    (h₂ : ∀ b ∈ W₂, (∀ a ∈ W₁, B a b = 0) → b = 0)
    (f : E →ₗ[K] E) (hf₁ : ∀ w ∈ W₁, f w ∈ W₁) (hf₂ : ∀ w ∈ W₂, f w ∈ W₂) (ν : K)
    (hB : ∀ a ∈ W₁, ∀ b ∈ W₂, B (f a) (f b) = ν * B a b) :
    LinearMap.det (f.restrict hf₁) * LinearMap.det (f.restrict hf₂) =
      ν ^ Module.finrank K W₁ := by
  obtain ⟨β, hβ⟩ : ∃ β : W₁ →ₗ[K] W₂ →ₗ[K] K, ∀ (a : W₁) (b : W₂), β a b = B a.1 b.1 :=
    ⟨B.compl₁₂ W₁.subtype W₂.subtype, fun a b => rfl⟩
  have hJinj : Function.Injective β.flip := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    have hb' : ∀ a ∈ W₁, B a b.1 = 0 := by
      intro a ha
      have := congrArg (fun φ : Module.Dual K W₁ => φ ⟨a, ha⟩) hb
      simpa [LinearMap.flip_apply, hβ] using this
    exact Subtype.ext (h₂ b.1 b.2 hb')
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have ha' : ∀ b ∈ W₂, B a.1 b = 0 := by
      intro b hb
      have := congrArg (fun φ : W₂ →ₗ[K] K => φ ⟨b, hb⟩) ha
      simpa [hβ] using this
    exact Subtype.ext (h₁ a.1 a.2 ha')
  have hdimβ : Module.finrank K W₁ ≤ Module.finrank K (Module.Dual K W₂) :=
    LinearMap.finrank_le_finrank_of_injective hβinj
  have hdimJ : Module.finrank K W₂ ≤ Module.finrank K (Module.Dual K W₁) :=
    LinearMap.finrank_le_finrank_of_injective hJinj
  simp only [Subspace.dual_finrank_eq] at hdimβ hdimJ
  have hW : Module.finrank K W₂ = Module.finrank K (Module.Dual K W₁) := by
    rw [Subspace.dual_finrank_eq]
    exact le_antisymm hdimJ hdimβ
  have hJsurj : Function.Surjective β.flip :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hW).mp hJinj
  obtain ⟨e, he⟩ : ∃ e : W₂ ≃ₗ[K] Module.Dual K W₁, ∀ b : W₂, e b = β.flip b :=
    ⟨LinearEquiv.ofBijective β.flip ⟨hJinj, hJsurj⟩, fun b => rfl⟩
  have hkey : ∀ b : W₂, (f.restrict hf₁).dualMap (β.flip (f.restrict hf₂ b)) =
      ν • β.flip b := by
    intro b
    apply LinearMap.ext
    intro a
    simp only [LinearMap.dualMap_apply, LinearMap.smul_apply, LinearMap.flip_apply, hβ,
      smul_eq_mul]
    exact hB a.1 a.2 b.1 b.2
  have hT : ∀ φ : Module.Dual K W₁,
      (f.restrict hf₁).dualMap (e (f.restrict hf₂ (e.symm φ))) = ν • φ := by
    intro φ
    rw [he, hkey, ← he, e.apply_symm_apply]
  have hcomp : (f.restrict hf₁).dualMap ∘ₗ
      ((e : W₂ →ₗ[K] Module.Dual K W₁) ∘ₗ (f.restrict hf₂) ∘ₗ
        (e.symm : Module.Dual K W₁ →ₗ[K] W₂)) = ν • LinearMap.id := by
    apply LinearMap.ext
    intro φ
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearMap.smul_apply,
      LinearMap.id_apply]
    exact hT φ
  have hdetT := LinearMap.det_conj (f.restrict hf₂) e
  calc LinearMap.det (f.restrict hf₁) * LinearMap.det (f.restrict hf₂)
      = LinearMap.det ((f.restrict hf₁).dualMap) *
          LinearMap.det ((e : W₂ →ₗ[K] Module.Dual K W₁) ∘ₗ (f.restrict hf₂) ∘ₗ
            (e.symm : Module.Dual K W₁ →ₗ[K] W₂)) := by
        rw [LinearMap.det_dualMap, hdetT]
    _ = LinearMap.det ((f.restrict hf₁).dualMap ∘ₗ
          ((e : W₂ →ₗ[K] Module.Dual K W₁) ∘ₗ (f.restrict hf₂) ∘ₗ
            (e.symm : Module.Dual K W₁ →ₗ[K] W₂))) :=
        (LinearMap.det_comp _ _).symm
    _ = ν ^ Module.finrank K W₁ := by
        rw [hcomp, LinearMap.det_smul, LinearMap.det_id, mul_one, Subspace.dual_finrank_eq]

theorem exists_matrix_det_eq {K F E : Type*} [Field K] [Field F] [AddCommGroup E] [Module K E]
    [Module.Finite K E] {n : ℕ} (θ : K ≃+* F) (ψ : E ≃+ (Fin n → F))
    (hψ : ∀ (c : K) (e : E), ψ (c • e) = θ c • ψ e) (U : E →ₗ[K] E) :
    ∃ A : Matrix (Fin n) (Fin n) F, (∀ e, ψ (U e) = A.mulVec (ψ e)) ∧
      A.det = θ (LinearMap.det U) := by
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : E ≃ₗ[K] (Fin n → K), ∀ e i, Φ e i = θ.symm (ψ e i) :=
    ⟨{ toFun := fun e i => θ.symm (ψ e i)
       map_add' := fun x y => by
         funext i
         simp
       map_smul' := fun c x => by
         funext i
         have h : ψ (c • x) i = θ c * ψ x i := by
           rw [hψ c x, Pi.smul_apply, smul_eq_mul]
         simp [h]
       invFun := fun x => ψ.symm (fun i => θ (x i))
       left_inv := fun x => by
         simp
       right_inv := fun x => by
         funext i
         simp }, fun _ _ => rfl⟩
  have hθΦ : ∀ x i, θ (Φ x i) = ψ x i := fun x i => by
    rw [hΦ, RingEquiv.apply_symm_apply]
  obtain ⟨b, hb⟩ : ∃ b : Module.Basis (Fin n) K E, ∀ e i, b.repr e i = Φ e i :=
    ⟨Module.Basis.ofEquivFun Φ, fun e i => Module.Basis.ofEquivFun_repr_apply Φ e i⟩
  have hU : ∀ e, Φ (U e) = (LinearMap.toMatrix b b U).mulVec (Φ e) := by
    intro e
    have hfe : ⇑(b.repr e) = Φ e := funext fun i => hb e i
    have hfu : ⇑(b.repr (U e)) = Φ (U e) := funext fun i => hb (U e) i
    have h := LinearMap.toMatrix_mulVec_repr b b U e
    rw [hfe, hfu] at h
    exact h.symm
  refine ⟨(LinearMap.toMatrix b b U).map θ, fun e => ?_, ?_⟩
  · funext i
    rw [← hθΦ (U e) i, hU e]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, hθΦ, Matrix.map_apply]
  · rw [← LinearMap.det_toMatrix b U]
    exact (RingEquiv.map_det θ _).symm

end CFSG.RankThree.GF2n.Smith81
