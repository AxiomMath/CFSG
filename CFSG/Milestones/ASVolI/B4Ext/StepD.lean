module

public import CFSG.Milestones.ASVolI.B4Ext.StepN

public section

namespace CFSG.ASVolI

open CFSG.GroupTheory.GLnTwoSplitting CFSG.Quasithin.JonesParshall Module Submodule

section BlocksD

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] {φ : Dual (ZMod 2) W} {w₀ : W}
  (hw₀ : φ w₀ = 1)

@[expose] def burnsideB49x_eD (φ : Dual (ZMod 2) W) (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ) →ₗ[ZMod 2] ZMod 2 :=
  β.compl₁₂ (LinearMap.ker φ).subtype (LinearMap.ker φ).subtype

@[expose] def burnsideB49x_eR (φ : Dual (ZMod 2) W) (w₀ : W)
    (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) : Dual (ZMod 2) ↥(LinearMap.ker φ) :=
  (β w₀) ∘ₗ (LinearMap.ker φ).subtype

@[expose] def burnsideB49x_eC (φ : Dual (ZMod 2) W) (w₀ : W)
    (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) : Dual (ZMod 2) ↥(LinearMap.ker φ) :=
  (β.flip w₀) ∘ₗ (LinearMap.ker φ).subtype

@[expose] def burnsideB49x_eA (w₀ : W) (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) : ZMod 2 :=
  β w₀ w₀

theorem burnsideB49x_eblocks_apply (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) (x y : W) :
    β x y = burnsideB49x_eD φ β (burnsideB49_proj φ hw₀ x) (burnsideB49_proj φ hw₀ y) +
      φ x * burnsideB49x_eR φ w₀ β (burnsideB49_proj φ hw₀ y) +
      φ y * burnsideB49x_eC φ w₀ β (burnsideB49_proj φ hw₀ x) +
      φ x * φ y * burnsideB49x_eA w₀ β := by
  conv_lhs => rw [burnsideB49x_decomp hw₀ x, burnsideB49x_decomp hw₀ y]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    burnsideB49x_eD, burnsideB49x_eR, burnsideB49x_eC, burnsideB49x_eA, LinearMap.compl₁₂_apply,
    LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply]
  ring

include hw₀ in
theorem burnsideB49x_eblocks_ext {β β' : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2}
    (hD : burnsideB49x_eD φ β = burnsideB49x_eD φ β')
    (hR : burnsideB49x_eR φ w₀ β = burnsideB49x_eR φ w₀ β')
    (hC : burnsideB49x_eC φ w₀ β = burnsideB49x_eC φ w₀ β')
    (hA : burnsideB49x_eA w₀ β = burnsideB49x_eA w₀ β') : β = β' := by
  ext x y
  rw [burnsideB49x_eblocks_apply hw₀ β x y, burnsideB49x_eblocks_apply hw₀ β' x y, hD, hR, hC, hA]

theorem burnsideB49x_eblocks_add (β β' : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    burnsideB49x_eD φ (β + β') = burnsideB49x_eD φ β + burnsideB49x_eD φ β' ∧
    burnsideB49x_eR φ w₀ (β + β') = burnsideB49x_eR φ w₀ β + burnsideB49x_eR φ w₀ β' ∧
    burnsideB49x_eC φ w₀ (β + β') = burnsideB49x_eC φ w₀ β + burnsideB49x_eC φ w₀ β' ∧
    burnsideB49x_eA w₀ (β + β') = burnsideB49x_eA w₀ β + burnsideB49x_eA w₀ β' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext a b
    simp [burnsideB49x_eD]
  · ext b
    simp [burnsideB49x_eR]
  · ext a
    simp [burnsideB49x_eC]
  · simp [burnsideB49x_eA]

theorem burnsideB49x_eblocks_sub (β β' : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    burnsideB49x_eD φ (β - β') = burnsideB49x_eD φ β - burnsideB49x_eD φ β' ∧
    burnsideB49x_eR φ w₀ (β - β') = burnsideB49x_eR φ w₀ β - burnsideB49x_eR φ w₀ β' ∧
    burnsideB49x_eC φ w₀ (β - β') = burnsideB49x_eC φ w₀ β - burnsideB49x_eC φ w₀ β' ∧
    burnsideB49x_eA w₀ (β - β') = burnsideB49x_eA w₀ β - burnsideB49x_eA w₀ β' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext a b
    simp [burnsideB49x_eD]
  · ext b
    simp [burnsideB49x_eR]
  · ext a
    simp [burnsideB49x_eC]
  · simp [burnsideB49x_eA]

@[expose] noncomputable def burnsideB49x_eBuild
    (D : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ) →ₗ[ZMod 2] ZMod 2)
    (R C : Dual (ZMod 2) ↥(LinearMap.ker φ)) (A : ZMod 2) :
    W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2 :=
  D.compl₁₂ (burnsideB49_proj φ hw₀) (burnsideB49_proj φ hw₀) +
    φ.smulRight (R ∘ₗ burnsideB49_proj φ hw₀) +
    (φ.smulRight (C ∘ₗ burnsideB49_proj φ hw₀)).flip + A • φ.smulRight φ

theorem burnsideB49x_eBuild_apply
    (D : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ) →ₗ[ZMod 2] ZMod 2)
    (R C : Dual (ZMod 2) ↥(LinearMap.ker φ)) (A : ZMod 2) (x y : W) :
    burnsideB49x_eBuild hw₀ D R C A x y =
      D (burnsideB49_proj φ hw₀ x) (burnsideB49_proj φ hw₀ y) +
        φ x * R (burnsideB49_proj φ hw₀ y) + φ y * C (burnsideB49_proj φ hw₀ x) +
        A * (φ x * φ y) := by
  simp [burnsideB49x_eBuild]

theorem burnsideB49x_eBuild_blocks
    (D : ↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ) →ₗ[ZMod 2] ZMod 2)
    (R C : Dual (ZMod 2) ↥(LinearMap.ker φ)) (A : ZMod 2) :
    burnsideB49x_eD φ (burnsideB49x_eBuild hw₀ D R C A) = D ∧
    burnsideB49x_eR φ w₀ (burnsideB49x_eBuild hw₀ D R C A) = R ∧
    burnsideB49x_eC φ w₀ (burnsideB49x_eBuild hw₀ D R C A) = C ∧
    burnsideB49x_eA w₀ (burnsideB49x_eBuild hw₀ D R C A) = A := by
  have hφy : ∀ y : ↥(LinearMap.ker φ), φ (y : W) = 0 := fun y => LinearMap.mem_ker.1 y.2
  have hpr0 := burnsideB49x_proj_w₀ hw₀
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext a b
    simp only [burnsideB49x_eD, LinearMap.compl₁₂_apply, Submodule.subtype_apply,
      burnsideB49x_eBuild_apply, burnsideB49_proj_ker hw₀, hφy, zero_mul, mul_zero, add_zero]
  · ext b
    simp only [burnsideB49x_eR, LinearMap.comp_apply, Submodule.subtype_apply,
      burnsideB49x_eBuild_apply, burnsideB49_proj_ker hw₀, hφy, hpr0, hw₀, map_zero,
      LinearMap.zero_apply, one_mul, zero_add, zero_mul, mul_zero, add_zero]
  · ext a
    simp only [burnsideB49x_eC, LinearMap.comp_apply, Submodule.subtype_apply,
      LinearMap.flip_apply, burnsideB49x_eBuild_apply, burnsideB49_proj_ker hw₀, hφy, hpr0, hw₀,
      map_zero, one_mul, zero_add, zero_mul, mul_zero, add_zero]
  · simp only [burnsideB49x_eA, burnsideB49x_eBuild_apply, hpr0, hw₀, map_zero,
      LinearMap.zero_apply, mul_one, zero_add, mul_zero, add_zero]

end BlocksD

section KEquivD

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)

theorem burnsideB49x_eD_muD (k : ↥(burnsideB49_K φ w₀))
    (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    burnsideB49x_eD φ (burnsideB49x_muD W k β) =
      burnsideB49x_muD _ (burnsideB49_Kres φ w₀ k) (burnsideB49x_eD φ β) := by
  ext a b
  simp only [burnsideB49x_eD, LinearMap.compl₁₂_apply, Submodule.subtype_apply,
    burnsideB49x_muD_apply, burnsideB49_Kres_symm_apply]

theorem burnsideB49x_eR_muD (k : ↥(burnsideB49_K φ w₀))
    (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    burnsideB49x_eR φ w₀ (burnsideB49x_muD W k β) =
      burnsideB49_KresDual φ w₀ k (burnsideB49x_eR φ w₀ β) := by
  ext b
  simp only [burnsideB49x_eR, LinearMap.comp_apply, Submodule.subtype_apply,
    burnsideB49x_muD_apply, burnsideB49_KresDual_apply, burnsideB49_Kres_symm_apply,
    burnsideB49x_K_symm_w₀]

theorem burnsideB49x_eC_muD (k : ↥(burnsideB49_K φ w₀))
    (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    burnsideB49x_eC φ w₀ (burnsideB49x_muD W k β) =
      burnsideB49_KresDual φ w₀ k (burnsideB49x_eC φ w₀ β) := by
  ext a
  simp only [burnsideB49x_eC, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply,
    burnsideB49x_muD_apply, burnsideB49_KresDual_apply, burnsideB49_Kres_symm_apply,
    burnsideB49x_K_symm_w₀]

theorem burnsideB49x_eA_muD (k : ↥(burnsideB49_K φ w₀))
    (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) :
    burnsideB49x_eA w₀ (burnsideB49x_muD W k β) = burnsideB49x_eA w₀ β := by
  simp only [burnsideB49x_eA, burnsideB49x_muD_apply, burnsideB49x_K_symm_w₀]

include hw₀ in
theorem burnsideB49x_kstepD (hdim : 4 ≤ finrank (ZMod 2) ↥(LinearMap.ker φ))
    (IH : ∀ δ' : (↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) →
        (↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ) →ₗ[ZMod 2] ZMod 2),
      δ' ∈ Z1A (burnsideB49x_muD ↥(LinearMap.ker φ)) →
        δ' ∈ B1A (burnsideB49x_muD ↥(LinearMap.ker φ)))
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)}
    (hδ : δ ∈ Z1A (burnsideB49x_muD W)) :
    ∃ Y₀ : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2, ∀ k ∈ burnsideB49_K φ w₀,
      δ k = burnsideB49x_muD W k Y₀ - Y₀ := by
  have hκi := burnsideB49_Kres_injective φ hw₀
  have hκs := burnsideB49_Kres_surjective φ hw₀
  let e : ↥(burnsideB49_K φ w₀) ≃* (↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) :=
    MulEquiv.ofBijective (burnsideB49_Kres φ w₀) ⟨hκi, hκs⟩
  have he : ∀ T, burnsideB49_Kres φ w₀ (e.symm T) = T := fun T => e.apply_symm_apply T
  have he' : ∀ k, e.symm (burnsideB49_Kres φ w₀ k) = k := fun k => e.symm_apply_apply k
  have hδK : ∀ k k' : ↥(burnsideB49_K φ w₀),
      δ ((k * k' : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W) =
        δ k + burnsideB49x_muD W k (δ k') :=
    fun k k' => hδ (k : W ≃ₗ[ZMod 2] W) k'
  have hdimD : 4 ≤ finrank (ZMod 2) (Dual (ZMod 2) ↥(LinearMap.ker φ)) := by
    rw [Subspace.dual_finrank_eq]
    exact hdim
  obtain ⟨d, hd⟩ := IH (fun T => burnsideB49x_eD φ (δ (e.symm T))) (fun T T' => by
    show burnsideB49x_eD φ (δ ((e.symm (T * T') : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W)) =
      burnsideB49x_eD φ (δ (e.symm T)) +
        burnsideB49x_muD _ T (burnsideB49x_eD φ (δ (e.symm T')))
    rw [map_mul, hδK, (burnsideB49x_eblocks_add (φ := φ) (w₀ := w₀) _ _).1, burnsideB49x_eD_muD, he])
  have hker : ∀ (k : ↥(burnsideB49_K φ w₀)), burnsideB49_KresDual φ w₀ k = 1 → k = 1 :=
    fun k hk => burnsideB49x_KresDual_injective hw₀ (by rw [hk, map_one])
  obtain ⟨r, hr⟩ := exists_eq_of_isCocycle hdimD (burnsideB49_KresDual φ w₀)
    (burnsideB49x_KresDual_transv hw₀)
    (fun k => burnsideB49x_eR φ w₀ (δ k)) (fun k k' => by
      show burnsideB49x_eR φ w₀ (δ ((k * k' : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W)) = _
      rw [hδK, (burnsideB49x_eblocks_add (φ := φ) (w₀ := w₀) _ _).2.1, burnsideB49x_eR_muD])
    (fun k hk => by
      obtain rfl := hker k hk
      show burnsideB49x_eR φ w₀ (δ 1) = 0
      rw [Z1A_one hδ]
      ext b
      simp [burnsideB49x_eR])
  obtain ⟨c, hc⟩ := exists_eq_of_isCocycle hdimD (burnsideB49_KresDual φ w₀)
    (burnsideB49x_KresDual_transv hw₀)
    (fun k => burnsideB49x_eC φ w₀ (δ k)) (fun k k' => by
      show burnsideB49x_eC φ w₀ (δ ((k * k' : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W)) = _
      rw [hδK, (burnsideB49x_eblocks_add (φ := φ) (w₀ := w₀) _ _).2.2.1, burnsideB49x_eC_muD])
    (fun k hk => by
      obtain rfl := hker k hk
      show burnsideB49x_eC φ w₀ (δ 1) = 0
      rw [Z1A_one hδ]
      ext a
      simp [burnsideB49x_eC])
  have hA : ∀ k : ↥(burnsideB49_K φ w₀), burnsideB49x_eA w₀ (δ k) = 0 :=
    burnsideB49_hom_eq_zero_of_perfect (burnsideB49_K_perfect hw₀ (by omega)) (fun k k' => by
      show burnsideB49x_eA w₀ (δ ((k * k' : ↥(burnsideB49_K φ w₀)) : W ≃ₗ[ZMod 2] W)) = _
      rw [hδK, (burnsideB49x_eblocks_add (φ := φ) (w₀ := w₀) _ _).2.2.2, burnsideB49x_eA_muD])
  refine ⟨burnsideB49x_eBuild hw₀ d r c 0, fun k hk => ?_⟩
  obtain ⟨hbD, hbR, hbC, hbA⟩ := burnsideB49x_eBuild_blocks hw₀ d r c 0
  set k' : ↥(burnsideB49_K φ w₀) := ⟨k, hk⟩ with hk'def
  have hk' : (k' : W ≃ₗ[ZMod 2] W) = k := rfl
  rw [← hk']
  apply burnsideB49x_eblocks_ext hw₀
  · rw [(burnsideB49x_eblocks_sub (φ := φ) (w₀ := w₀) _ _).1, burnsideB49x_eD_muD, hbD]
    have := congrFun hd (burnsideB49_Kres φ w₀ k')
    simp only [coboundaryA_apply, he'] at this
    exact this.symm
  · rw [(burnsideB49x_eblocks_sub (φ := φ) (w₀ := w₀) _ _).2.1, burnsideB49x_eR_muD, hbR]
    rw [show burnsideB49x_eR φ w₀ (δ k') = _ from hr k', two_sub]
  · rw [(burnsideB49x_eblocks_sub (φ := φ) (w₀ := w₀) _ _).2.2.1, burnsideB49x_eC_muD, hbC]
    rw [show burnsideB49x_eC φ w₀ (δ k') = _ from hc k', two_sub]
  · rw [(burnsideB49x_eblocks_sub (φ := φ) (w₀ := w₀) _ _).2.2.2, burnsideB49x_eA_muD, hbA, hA k', sub_self]

end KEquivD

section QStepD

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]
  {φ : Dual (ZMod 2) W} {w₀ : W} (hw₀ : φ w₀ = 1)

include hw₀ in
theorem burnsideB49x_qstepD (hdim : 4 ≤ finrank (ZMod 2) ↥(LinearMap.ker φ))
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)}
    (hδ : δ ∈ Z1A (burnsideB49x_muD W)) (hK : ∀ k ∈ burnsideB49_K φ w₀, δ k = 0) :
    ∀ (u : W) (h : φ u = 0), δ (burnsideB49_tv φ u h) = 0 := by
  have hκs := burnsideB49_Kres_surjective φ hw₀
  have hφy : ∀ y : ↥(LinearMap.ker φ), φ (y : W) = 0 := fun y => LinearMap.mem_ker.1 y.2
  let t : ↥(LinearMap.ker φ) → (W ≃ₗ[ZMod 2] W) := fun u => burnsideB49_tv φ (u : W) (hφy u)
  let dQ : ↥(LinearMap.ker φ) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) := fun u => δ (t u)
  have hQ1 : ∀ u v, dQ (u + v) = dQ u + burnsideB49x_muD W (t u) (dQ v) := by
    intro u v
    have : t (u + v) = t u * t v := (burnsideB49_tv_mul _ _ _).symm
    show δ (t (u + v)) = δ (t u) + burnsideB49x_muD W (t u) (δ (t v))
    rw [this, hδ]
  have hQ2 : ∀ (k : ↥(burnsideB49_K φ w₀)) u,
      dQ (burnsideB49_Kres φ w₀ k u) = burnsideB49x_muD W k (dQ u) := by
    intro k u
    have hconj : (k : W ≃ₗ[ZMod 2] W) * t u * (k : W ≃ₗ[ZMod 2] W)⁻¹ =
        t (burnsideB49_Kres φ w₀ k u) :=
      burnsideB49_conj_tv (hφy u) (burnsideB49_K_le_stab φ w₀ k.2) _
    have h1 := Z1A_conj hδ (k : W ≃ₗ[ZMod 2] W) (t u)
    rw [hconj, hK k k.2] at h1
    show δ (t (burnsideB49_Kres φ w₀ k u)) = burnsideB49x_muD W k (δ (t u))
    rw [h1, map_zero, add_zero]
    exact sub_zero (burnsideB49x_muD W k (δ (t u)))
  have hmuT : ∀ u (β : W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2) x y, burnsideB49x_muD W (t u) β x y =
      β (x + φ x • (u : W)) (y + φ y • (u : W)) := by
    intro u β x y
    rw [burnsideB49x_muD_apply, burnsideB49x_tv_symm_apply, burnsideB49x_tv_symm_apply]
  have hinvK : ∀ (k : ↥(burnsideB49_K φ w₀)) u x y,
      dQ (burnsideB49_Kres φ w₀ k u) ((k : W ≃ₗ[ZMod 2] W) x) ((k : W ≃ₗ[ZMod 2] W) y) =
        dQ u x y := by
    intro k u x y
    rw [hQ2, burnsideB49x_muD_apply, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  have hT : ∀ u a b : ↥(LinearMap.ker φ), dQ u a b = 0 := by
    refine burnsideB49x_inv_three hdim (fun u a b => dQ u a b) (fun u a b b' => by simp)
      (fun T u a b => ?_)
    obtain ⟨k, rfl⟩ := hκs T
    exact hinvK k u a b
  have hR : ∀ u b : ↥(LinearMap.ker φ), dQ u w₀ b = 0 := by
    refine burnsideB49x_inv_two (by omega) (fun u b => dQ u w₀ b) (fun u b b' => by simp)
      (fun T u b => ?_)
    obtain ⟨k, rfl⟩ := hκs T
    have := hinvK k u w₀ b
    rwa [k.2.2] at this
  have hC : ∀ u a : ↥(LinearMap.ker φ), dQ u a w₀ = 0 := by
    refine burnsideB49x_inv_two (by omega) (fun u a => dQ u a w₀) (fun u a a' => by simp)
      (fun T u a => ?_)
    obtain ⟨k, rfl⟩ := hκs T
    have := hinvK k u a w₀
    rwa [k.2.2] at this
  have hA : ∀ u : ↥(LinearMap.ker φ), dQ u w₀ w₀ = 0 := by
    refine burnsideB49x_inv_one (by omega) (fun u => dQ u w₀ w₀) (fun u v => ?_) (fun T u => ?_)
    · show dQ (u + v) w₀ w₀ = dQ u w₀ w₀ + dQ v w₀ w₀
      rw [hQ1, LinearMap.add_apply, LinearMap.add_apply, hmuT, hw₀, one_smul]
      simp only [map_add, LinearMap.add_apply, hR, hC, hT, add_zero]
    · obtain ⟨k, rfl⟩ := hκs T
      have := hinvK k u w₀ w₀
      rwa [k.2.2] at this
  intro u h
  set u' : ↥(LinearMap.ker φ) := ⟨u, LinearMap.mem_ker.2 h⟩ with hu'
  show dQ u' = 0
  ext x y
  rw [burnsideB49x_eblocks_apply hw₀ (dQ u') x y]
  simp only [burnsideB49x_eD, burnsideB49x_eR, burnsideB49x_eC, burnsideB49x_eA,
    LinearMap.compl₁₂_apply, LinearMap.comp_apply, Submodule.subtype_apply, LinearMap.flip_apply,
    hT, hR, hC, hA, mul_zero, add_zero, LinearMap.zero_apply]

include hw₀ in
theorem burnsideB49x_stepD (hφ : φ ≠ 0) (hdim : 4 ≤ finrank (ZMod 2) ↥(LinearMap.ker φ))
    (IH : ∀ δ' : (↥(LinearMap.ker φ) ≃ₗ[ZMod 2] ↥(LinearMap.ker φ)) →
        (↥(LinearMap.ker φ) →ₗ[ZMod 2] ↥(LinearMap.ker φ) →ₗ[ZMod 2] ZMod 2),
      δ' ∈ Z1A (burnsideB49x_muD ↥(LinearMap.ker φ)) →
        δ' ∈ B1A (burnsideB49x_muD ↥(LinearMap.ker φ)))
    {δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2)}
    (hδ : δ ∈ Z1A (burnsideB49x_muD W)) : δ ∈ B1A (burnsideB49x_muD W) := by
  obtain ⟨Y₀, hY₀⟩ := burnsideB49x_kstepD hw₀ hdim IH hδ
  set δ₁ := δ - coboundaryA (burnsideB49x_muD W) Y₀ with hδ₁
  have hδ₁Z : δ₁ ∈ Z1A (burnsideB49x_muD W) := sub_mem hδ (B1A_le_Z1A _ ⟨Y₀, rfl⟩)
  have hδ₁K : ∀ k ∈ burnsideB49_K φ w₀, δ₁ k = 0 := fun k hk => by
    rw [hδ₁, Pi.sub_apply, coboundaryA_apply, hY₀ k hk]
    exact sub_self (burnsideB49x_muD W k Y₀ - Y₀)
  have hδ₁Q := burnsideB49x_qstepD hw₀ hdim hδ₁Z hδ₁K
  have hδ₁P := burnsideB49x_vanish_stab hw₀ hδ₁Z hδ₁K hδ₁Q
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  haveI : Finite (W ≃ₗ[ZMod 2] W) :=
    Finite.of_injective (fun f : W ≃ₗ[ZMod 2] W => (f : W → W))
      (fun _ _ h => LinearEquiv.ext (congrFun h))
  refine mem_B1A_of_restrict (fun m => two_add_self m) (burnsideB49_stab_index_odd hφ) hδ
    (m := Y₀) (fun s hs => ?_)
  have h := hδ₁P s hs
  rw [hδ₁, Pi.sub_apply, coboundaryA_apply] at h
  exact sub_eq_zero.1 h

end QStepD

section InductionD

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

universe u

theorem burnsideB49x_H1D_of_base
    (base : ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W],
      finrank (ZMod 2) W = 5 → ∀ δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2),
        δ ∈ Z1A (burnsideB49x_muD W) → δ ∈ B1A (burnsideB49x_muD W)) :
    ∀ (n : ℕ), 5 ≤ n → ∀ (W : Type u) [AddCommGroup W] [Module (ZMod 2) W]
      [FiniteDimensional (ZMod 2) W], finrank (ZMod 2) W = n →
        ∀ δ : (W ≃ₗ[ZMod 2] W) → (W →ₗ[ZMod 2] W →ₗ[ZMod 2] ZMod 2),
          δ ∈ Z1A (burnsideB49x_muD W) → δ ∈ B1A (burnsideB49x_muD W) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact base
  | succ m hm ih =>
    intro W _ _ _ hW δ hδ
    obtain ⟨φ, -, w₀, hw₀⟩ := burnsideB49x_exists_sep (E := W) (S := ⊥)
      (by rw [finrank_bot, hW]; omega)
    have hφ : φ ≠ 0 := fun h => by
      rw [h, LinearMap.zero_apply] at hw₀
      exact zero_ne_one hw₀
    have hker := burnsideB49_finrank_ker φ hw₀
    exact burnsideB49x_stepD hw₀ hφ (by omega) (ih _ (by omega)) hδ

end InductionD

end CFSG.ASVolI
