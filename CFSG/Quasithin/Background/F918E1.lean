module

public import CFSG.Quasithin.Background.B1Transvection

public section

namespace CFSG.Quasithin

section LinearGen

private theorem ite_aux {B : Type*} [DecidableEq B] {i j : B} (hij : i ≠ j) (r k : B) :
    ((if k = r then (1 : ZMod 2) else 0) + (if k = j then (1 : ZMod 2) else 0) •
        (if i = r then (1 : ZMod 2) else 0)) =
      (if r = k then (1 : ZMod 2) else 0) + (if i = r ∧ j = k then (1 : ZMod 2) else 0) := by
  by_cases h1 : r = k <;> by_cases h2 : k = j <;> by_cases h3 : i = r <;> simp_all [eq_comm]

private theorem linear_gen {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [Finite E]
    (S : Set E) (hS : Submodule.span (ZMod 2) S = ⊤)
    (Λ : Subgroup (E ≃ₗ[ZMod 2] E))
    (hΛ : ∀ c ∈ S, ∀ (f : Module.Dual (ZMod 2) E) (h : f c = 0),
      LinearEquiv.transvection h ∈ Λ) :
    Λ = ⊤ := by
  classical
  obtain ⟨B, hBS, hspan, hli⟩ := exists_linearIndependent (ZMod 2) S
  let b : Module.Basis B (ZMod 2) E := Module.Basis.mk hli (by
    rw [Subtype.range_coe, hspan, hS])
  have : Fintype B := Fintype.ofFinite B
  let Θ : (E ≃ₗ[ZMod 2] E) → Matrix B B (ZMod 2) :=
    fun φ => LinearMap.toMatrix b b φ.toLinearMap
  have hΘmul : ∀ φ ψ, Θ (φ * ψ) = Θ φ * Θ ψ := by
    intro φ ψ
    exact LinearMap.toMatrix_mul b φ.toLinearMap ψ.toLinearMap
  have hΘone : Θ 1 = 1 := LinearMap.toMatrix_one b
  have hΘinj : Function.Injective Θ := by
    intro φ ψ h
    exact LinearEquiv.toLinearMap_injective ((LinearMap.toMatrix b b).injective h)
  rw [eq_top_iff]
  intro φ _
  have hdet : (Θ φ).det ≠ 0 := by
    have h1 : Θ φ * Θ φ⁻¹ = 1 := by rw [← hΘmul, mul_inv_cancel, hΘone]
    have h2 := congrArg Matrix.det h1
    rw [Matrix.det_mul, Matrix.det_one] at h2
    exact left_ne_zero_of_mul_eq_one h2
  have key : ∃ ℓ ∈ Λ, Θ ℓ = Θ φ := by
    refine Matrix.diagonal_transvection_induction_of_det_ne_zero
      (fun M => ∃ ℓ ∈ Λ, Θ ℓ = M) (Θ φ) hdet ?_ ?_ ?_
    · intro D hD
      rw [Matrix.det_diagonal] at hD
      have hD1 : ∀ i, D i = 1 := by
        intro i
        have := (Finset.prod_ne_zero_iff.mp hD) i (Finset.mem_univ i)
        revert this
        generalize D i = a
        revert a
        decide
      have : Matrix.diagonal D = 1 := by
        rw [show D = fun _ => 1 from funext hD1]
        exact Matrix.diagonal_one
      exact ⟨1, Λ.one_mem, by rw [hΘone, this]⟩
    · rintro ⟨i, j, hij, c⟩
      show ∃ ℓ ∈ Λ, Θ ℓ = Matrix.transvection i j c
      have hc : c = 0 ∨ c = 1 := by revert c; decide
      rcases hc with rfl | rfl
      · exact ⟨1, Λ.one_mem, by rw [hΘone, Matrix.transvection_zero]⟩
      · have hbi : b i = (i : E) := Module.Basis.mk_apply _ _ i
        have hji : b.coord j (b i) = 0 := by
          simp [Module.Basis.coord_apply, hij]
        refine ⟨LinearEquiv.transvection hji, hΛ (b i) (hbi ▸ hBS i.2) (b.coord j) hji, ?_⟩
        ext r k
        simp only [Θ, LinearMap.toMatrix_apply, Matrix.transvection, Matrix.add_apply,
          Matrix.single_apply, LinearEquiv.coe_coe, LinearEquiv.transvection.apply,
          Module.Basis.coord_apply, map_add, map_smul, Module.Basis.repr_self,
          Finsupp.add_apply, Finsupp.smul_apply, Finsupp.single_apply, Matrix.one_apply]
        exact ite_aux hij r k
    · rintro A B - - ⟨ℓ₁, h₁, rfl⟩ ⟨ℓ₂, h₂, rfl⟩
      exact ⟨ℓ₁ * ℓ₂, Λ.mul_mem h₁ h₂, hΘmul ℓ₁ ℓ₂⟩
  obtain ⟨ℓ, hℓ, hℓφ⟩ := key
  rw [← hΘinj hℓφ]
  exact hℓ

end LinearGen

section MulAutLin

variable (W : Type*) [CommGroup W] [Module (ZMod 2) (Additive W)]

@[expose] noncomputable def mulAutLin : MulAut W ≃* (Additive W ≃ₗ[ZMod 2] Additive W) where
  toFun φ :=
    { AddMonoidHom.toZModLinearMap 2 (MulEquiv.toAdditive φ : Additive W →+ Additive W) with
      invFun := fun x => Additive.ofMul (φ.symm (Additive.toMul x))
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  invFun e := MulEquiv.toAdditive.symm e.toAddEquiv
  left_inv φ := by ext; rfl
  right_inv e := by ext; rfl
  map_mul' φ ψ := by ext; rfl

theorem mulAutLin_apply (φ : MulAut W) (x : Additive W) :
    mulAutLin W φ x = Additive.ofMul (φ (Additive.toMul x)) := rfl

theorem mulAutLin_symm_apply (e : Additive W ≃ₗ[ZMod 2] Additive W) (w : W) :
    (mulAutLin W).symm e w = Additive.toMul (e (Additive.ofMul w)) := rfl

variable {W}

@[expose] noncomputable def tvAut (F : Module.Dual (ZMod 2) (Additive W)) (y : W)
    (h : F (Additive.ofMul y) = 0) : MulAut W :=
  (mulAutLin W).symm (LinearEquiv.transvection h)

theorem zmod_two_cases (a : ZMod 2) : a = 0 ∨ a = 1 := by revert a; decide

theorem tvAut_of_eq_zero {F : Module.Dual (ZMod 2) (Additive W)} {y : W}
    (h : F (Additive.ofMul y) = 0) {v : W} (hv : F (Additive.ofMul v) = 0) :
    tvAut F y h v = v := by
  rw [tvAut, mulAutLin_symm_apply, LinearEquiv.transvection.apply, hv, zero_smul, add_zero]
  rfl

theorem tvAut_of_eq_one {F : Module.Dual (ZMod 2) (Additive W)} {y : W}
    (h : F (Additive.ofMul y) = 0) {v : W} (hv : F (Additive.ofMul v) = 1) :
    tvAut F y h v = v * y := by
  rw [tvAut, mulAutLin_symm_apply, LinearEquiv.transvection.apply, hv, one_smul]
  rfl

theorem exists_extend_dual {V : Type*} [CommGroup V] [Module (ZMod 2) (Additive V)]
    (U : Subgroup V) [Module (ZMod 2) (Additive ↥U)]
    (f : Module.Dual (ZMod 2) (Additive ↥U)) :
    ∃ F : Module.Dual (ZMod 2) (Additive V),
      ∀ x : ↥U, F (Additive.ofMul (x : V)) = f (Additive.ofMul x) := by
  let ι : Additive ↥U →ₗ[ZMod 2] Additive V :=
    AddMonoidHom.toZModLinearMap 2 (MonoidHom.toAdditive U.subtype)
  have hι : LinearMap.ker ι = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro a b hab
    exact Additive.toMul.injective (Subtype.ext (Additive.ofMul.injective hab))
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective ι hι
  refine ⟨f ∘ₗ g, fun x => ?_⟩
  have h1 : ι (Additive.ofMul x) = Additive.ofMul (x : V) := rfl
  have := congrArg f (LinearMap.congr_fun hg (Additive.ofMul x))
  rw [LinearMap.id_apply, LinearMap.comp_apply, h1] at this
  simpa using this

private theorem closure_preimage_eq_top {V : Type*} [Group V] (O : Set V) (U : Subgroup V)
    (hU : U = Subgroup.closure O) :
    Subgroup.closure ((Subtype.val : ↥U → V) ⁻¹' O) = ⊤ := by
  subst hU
  exact Subgroup.closure_closure_coe_preimage

private theorem span_eq_top_of_closure {W : Type*} [CommGroup W] [Module (ZMod 2) (Additive W)]
    (T : Set W) (hT : Subgroup.closure T = ⊤) :
    Submodule.span (ZMod 2) (Additive.ofMul '' T) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have key : ∀ w : W, w ∈ Subgroup.closure T →
      Additive.ofMul w ∈ Submodule.span (ZMod 2) (Additive.ofMul '' T) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw => exact Submodule.subset_span ⟨w, hw, rfl⟩
    | one => exact Submodule.zero_mem _
    | mul a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | inv a _ ha => exact Submodule.neg_mem _ ha
  exact key (Additive.toMul x) (by rw [hT]; exact Subgroup.mem_top _)

end MulAutLin

theorem b410 {V : Type} [CommGroup V] [Finite V] (hexp : ∀ v : V, v ^ 2 = 1)
    (G : Subgroup (MulAut V)) (u : V) (hu : u ≠ 1)
    (hT : ∀ t : MulAut V, IsTransvectionWith t u → t ∈ G)
    (U : Subgroup V) (hU : U = Subgroup.closure {y | ∃ g ∈ G, g u = y})
    (L : Subgroup (MulAut V))
    (hL : L = Subgroup.closure
      {x | ∃ g ∈ G, ∃ t : MulAut V, IsTransvectionWith t u ∧ x = g * t * g⁻¹}) :
    autSub L U = ⊤ := by
  classical
  have h2V : ∀ x : Additive V, (2 : ℕ) • x = 0 := by
    intro x
    apply Multiplicative.ofAdd.injective
    exact hexp (Additive.toMul x)
  let _ : Module (ZMod 2) (Additive V) := AddCommGroup.zmodModule h2V
  have h2U : ∀ x : Additive ↥U, (2 : ℕ) • x = 0 := by
    intro x
    apply Multiplicative.ofAdd.injective
    exact Subtype.ext (hexp (Additive.toMul x : ↥U))
  let _ : Module (ZMod 2) (Additive ↥U) := AddCommGroup.zmodModule h2U
  set O : Set V := {y | ∃ g ∈ G, g u = y} with hO
  have hGU : ∀ g ∈ G, ∀ y ∈ U, g y ∈ U := by
    intro g hg y hy
    rw [hU] at hy ⊢
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨g', hg', rfl⟩ := hy
      exact Subgroup.subset_closure ⟨g * g', G.mul_mem hg hg', rfl⟩
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul a b _ _ iha ihb => rw [map_mul]; exact Subgroup.mul_mem _ iha ihb
    | inv a _ ih => rw [map_inv]; exact Subgroup.inv_mem _ ih
  have hLG : L ≤ G := by
    rw [hL, Subgroup.closure_le]
    rintro _ ⟨g, hg, t, ht, rfl⟩
    exact G.mul_mem (G.mul_mem hg (hT t ht)) (G.inv_mem hg)
  have hstab : ∀ g ∈ G, g ∈ stabSub U := by
    intro g hg w
    refine ⟨fun h => ?_, hGU g hg w⟩
    simpa using hGU g⁻¹ (G.inv_mem hg) _ h
  have hΛ : ∀ c ∈ Additive.ofMul '' ((Subtype.val : ↥U → V) ⁻¹' O),
      ∀ (f : Module.Dual (ZMod 2) (Additive ↥U)) (h : f c = 0),
      LinearEquiv.transvection h ∈
        (autSub L U).comap (mulAutLin ↥U).symm.toMonoidHom := by
    intro c hc f hf
    obtain ⟨w, hw, rfl⟩ := hc
    obtain ⟨g₀, hg₀, hg₀w⟩ := hw
    obtain ⟨F, hF⟩ := exists_extend_dual U f
    have hFw : F (Additive.ofMul (w : V)) = 0 := by rw [hF w]; exact hf
    have hFt : (F ∘ₗ (mulAutLin V g₀).toLinearMap) (Additive.ofMul u) = 0 := by
      simp [mulAutLin_apply, hg₀w, hFw]
    have ht : IsTransvectionWith (tvAut (F ∘ₗ (mulAutLin V g₀).toLinearMap) u hFt) u := by
      refine ⟨hu, fun v => ?_⟩
      rcases zmod_two_cases ((F ∘ₗ (mulAutLin V g₀).toLinearMap) (Additive.ofMul v)) with h | h
      · exact Or.inl (tvAut_of_eq_zero _ h)
      · exact Or.inr (tvAut_of_eq_one _ h)
    have hTvL : tvAut F (w : V) hFw ∈ L := by
      have : tvAut F (w : V) hFw =
          g₀ * tvAut (F ∘ₗ (mulAutLin V g₀).toLinearMap) u hFt * g₀⁻¹ := by
        ext v
        have hv' : (F ∘ₗ (mulAutLin V g₀).toLinearMap) (Additive.ofMul (g₀⁻¹ v)) =
            F (Additive.ofMul v) := by
          simp [mulAutLin_apply]
        rw [MulAut.mul_apply, MulAut.mul_apply]
        rcases zmod_two_cases (F (Additive.ofMul v)) with h | h
        · rw [tvAut_of_eq_zero _ h, tvAut_of_eq_zero _ (hv'.trans h)]
          simp
        · rw [tvAut_of_eq_one _ h, tvAut_of_eq_one _ (hv'.trans h), map_mul, hg₀w]
          simp
      rw [this, hL]
      exact Subgroup.subset_closure ⟨g₀, hg₀, _, ht, rfl⟩
    show tvAut f w hf ∈ autSub L U
    rw [mem_autSub]
    refine ⟨⟨_, hstab _ (hLG hTvL)⟩, hTvL, ?_⟩
    ext x
    show tvAut F (w : V) hFw (x : V) = ((tvAut f w hf x : ↥U) : V)
    rcases zmod_two_cases (f (Additive.ofMul x)) with h | h
    · rw [tvAut_of_eq_zero hf h, tvAut_of_eq_zero hFw (by rw [hF]; exact h)]
    · rw [tvAut_of_eq_one hf h, tvAut_of_eq_one hFw (by rw [hF]; exact h)]
      rfl
  have hmain := linear_gen (Additive.ofMul '' ((Subtype.val : ↥U → V) ⁻¹' O))
    (span_eq_top_of_closure _ (closure_preimage_eq_top O U hU))
    ((autSub L U).comap (mulAutLin ↥U).symm.toMonoidHom) hΛ
  rw [eq_top_iff]
  intro φ _
  have : mulAutLin ↥U φ ∈ (autSub L U).comap (mulAutLin ↥U).symm.toMonoidHom := by
    rw [hmain]
    exact Subgroup.mem_top _
  simpa using this

end CFSG.Quasithin
