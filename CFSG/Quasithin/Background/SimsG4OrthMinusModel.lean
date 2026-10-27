module

public import CFSG.Quasithin.SteinbergCBOmegaFourMinus
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders
public import CFSG.Quasithin.Background.SimsG4OrthURefl

public section

namespace CFSG.Quasithin.SimsG4.OrthMinus

open Module Matrix QuadraticMap CFSG.Quasithin.SteinbergCB CFSG.Quasithin.SimsG4

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

theorem exists_irred_quadratic {K : Type} [Field K] [Finite K] [CharP K 2] :
    ∃ c : K, ∀ s : K, s ^ 2 + 1 * s + c ≠ 0 := by
  have hni : ¬ Function.Injective (fun s : K => s ^ 2 + s) := fun h => zero_ne_one (h (by
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, one_pow]
    exact (CharTwo.add_self_eq_zero (1 : K)).symm))
  rw [Finite.injective_iff_surjective] at hni
  obtain ⟨c, hc⟩ := not_forall.1 hni
  refine ⟨c, fun s hs => hc ⟨s, ?_⟩⟩
  have h : s ^ 2 + s = -c := by linear_combination hs
  show s ^ 2 + s = c
  rw [h, CharTwo.neg_eq]

section Trace

variable {F : Type} [Field F]

theorem trace_twistLin (σ : F →+* F) (g : Matrix (Fin 2) (Fin 2) F) :
    LinearMap.trace F (Matrix (Fin 2) (Fin 2) F) (twistLin σ g) =
      g.trace * (g.map σ).trace := by
  rw [LinearMap.trace_eq_matrix_trace F (Matrix.stdBasis F (Fin 2) (Fin 2))]
  simp only [Matrix.trace, Fintype.sum_prod_type, Fin.sum_univ_two, LinearMap.toMatrix_apply,
    Matrix.diag_apply, twistLin_apply, Matrix.stdBasis_eq_single]
  simp [Matrix.stdBasis, Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply]
  ring

theorem trace_twistRep [Finite F] {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) {ω : F}
    (hω : σ ω ≠ ω) (g : SpecialLinearGroup (Fin 2) F) :
    ((LinearMap.trace (frobFixed σ) (twistedForm σ)
        ((twistRep hinv g : twistedForm σ ≃ₗ[frobFixed σ] twistedForm σ) :
          twistedForm σ →ₗ[frobFixed σ] twistedForm σ) : frobFixed σ) : F) =
      (g : Matrix (Fin 2) (Fin 2) F).trace * σ (g : Matrix (Fin 2) (Fin 2) F).trace := by
  have : Module.Finite (frobFixed σ) (twistedForm σ) := Module.Finite.of_finite
  set Lb := LinearEquiv.ofBijective _ (liftBaseChange_twistedForm_bijective hinv hω)
  have hconj : LinearMap.baseChange F ((twistRep hinv g : twistedForm σ ≃ₗ[frobFixed σ]
      twistedForm σ) : twistedForm σ →ₗ[frobFixed σ] twistedForm σ) =
      Lb.symm.conj (twistLin σ (g : Matrix (Fin 2) (Fin 2) F)) := by
    apply LinearMap.ext
    intro t
    apply Lb.injective
    rw [LinearEquiv.conj_apply, LinearEquiv.symm_symm, LinearMap.comp_apply,
      LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact liftBaseChange_twistRep hinv g t
  have h := LinearMap.trace_baseChange ((twistRep hinv g : twistedForm σ ≃ₗ[frobFixed σ]
      twistedForm σ) : twistedForm σ →ₗ[frobFixed σ] twistedForm σ) F
  rw [hconj, LinearMap.trace_conj', trace_twistLin] at h
  have hσtr : ((g : Matrix (Fin 2) (Fin 2) F).map σ).trace =
      σ (g : Matrix (Fin 2) (Fin 2) F).trace := by
    simp [Matrix.trace_fin_two]
  rw [hσtr] at h
  exact h.symm

end Trace

section Transport

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]
  {F₀ : Type} [Field F₀] {W₀ : Type} [AddCommGroup W₀] [Module F₀ W₀]
  {e : K ≃+* F₀} {Q : QuadraticForm K W} {Q₀ : QuadraticForm F₀ W₀}

theorem polar_transport (ψ : W ≃ₛₗ[(e : K →+* F₀)] W₀) (hψ : ∀ x, Q₀ (ψ x) = e (Q x))
    (x y : W) : polar Q₀ (ψ x) (ψ y) = e (polar Q x y) := by
  simp only [QuadraticMap.polar, ← map_add, hψ, map_sub]

theorem symm_transport (ψ : W ≃ₛₗ[(e : K →+* F₀)] W₀) (hψ : ∀ x, Q₀ (ψ x) = e (Q x))
    (X : W₀) : Q (ψ.symm X) = e.symm (Q₀ X) := by
  rw [← ψ.apply_symm_apply X, hψ, ψ.apply_symm_apply, RingEquiv.symm_apply_apply]

theorem reflK_transport [CharP K 2] [CharP F₀ 2] (ψ : W ≃ₛₗ[(e : K →+* F₀)] W₀)
    (hψ : ∀ x, Q₀ (ψ x) = e (Q x)) (r : W) (X : W₀) :
    ψ (reflK Q r (ψ.symm X)) = reflK Q₀ (ψ r) X := by
  have h := polar_transport ψ hψ (ψ.symm X) r
  rw [ψ.apply_symm_apply] at h
  rw [reflK_apply, reflK_apply, map_add, LinearEquiv.map_smulₛₗ, ψ.apply_symm_apply,
    RingEquiv.coe_toRingHom, ← h]

variable (e) in
@[expose] def conjHom (ψ : W ≃ₛₗ[(e : K →+* F₀)] W₀) : (W₀ ≃ₗ[F₀] W₀) →* (W ≃ₗ[K] W) where
  toFun f := ψ.trans (f.trans ψ.symm)
  map_one' := by
    ext x
    simp
  map_mul' f g := by
    ext x
    simp

theorem conjHom_injective (ψ : W ≃ₛₗ[(e : K →+* F₀)] W₀) : Function.Injective (conjHom e ψ) := by
  rw [injective_iff_map_eq_one]
  intro f hf
  ext X
  have h : ψ.symm (f (ψ (ψ.symm X))) = ψ.symm X := LinearEquiv.congr_fun hf (ψ.symm X)
  rw [ψ.apply_symm_apply] at h
  exact ψ.symm.injective h

end Transport

section Fixed

variable {F : Type} [Field F]

theorem mul_swap_mul_transpose [CharP F 2] (a : Matrix (Fin 2) (Fin 2) F) :
    a * !![0, 1; 1, 0] * aᵀ = a.det • !![0, 1; 1, 0] := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
  · linear_combination (a 0 0 * a 0 1) * h2
  · linear_combination (a 0 1 * a 1 0) * h2
  · linear_combination (a 0 1 * a 1 0) * h2
  · linear_combination (a 1 0 * a 1 1) * h2

theorem exists_twistRep_fixed [CharP F 2] {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x)
    (P : GL (Fin 2) F) :
    ∃ X : twistedForm σ, X ≠ 0 ∧ ∀ g : SpecialLinearGroup (Fin 2) F,
      (∀ i j, ((P : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) *
        ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) i j ∈ frobFixed σ) →
        twistRep hinv g X = X := by
  set Pm : Matrix (Fin 2) (Fin 2) F := (P : Matrix (Fin 2) (Fin 2) F) with hPm
  set Pi : Matrix (Fin 2) (Fin 2) F := ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) with hPi
  have hPPi : Pm * Pi = 1 := by
    rw [hPm, hPi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hPiP : Pi * Pm = 1 := by
    rw [hPm, hPi, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hT : (Pi.map σ)ᵀ * (Pm.map σ)ᵀ = 1 := by
    rw [← Matrix.transpose_mul, ← Matrix.map_mul, hPPi, Matrix.map_one _ (map_zero σ) (map_one σ),
      Matrix.transpose_one]
  set J : twistedForm σ := twMk hinv 0 1 0 with hJ
  have hJc : (J : Matrix (Fin 2) (Fin 2) F) = !![0, 1; 1, 0] := by
    rw [hJ, twMk_coe]
    simp
  let X : twistedForm σ := ⟨Pi * J * (Pi.map σ)ᵀ, twist_mem hinv Pi J.2⟩
  have hXc : (X : Matrix (Fin 2) (Fin 2) F) = Pi * J * (Pi.map σ)ᵀ := rfl
  refine ⟨X, ?_, ?_⟩
  · intro hX0
    have h0 : (X : Matrix (Fin 2) (Fin 2) F) = 0 := by rw [hX0]; rfl
    have h1 : Pm * (X : Matrix (Fin 2) (Fin 2) F) * (Pm.map σ)ᵀ =
        (J : Matrix (Fin 2) (Fin 2) F) := by
      rw [hXc, show Pm * (Pi * (J : Matrix (Fin 2) (Fin 2) F) * (Pi.map σ)ᵀ) * (Pm.map σ)ᵀ =
        (Pm * Pi) * (J : Matrix (Fin 2) (Fin 2) F) * ((Pi.map σ)ᵀ * (Pm.map σ)ᵀ) by
          simp only [Matrix.mul_assoc], hPPi, hT, Matrix.one_mul, Matrix.mul_one]
    rw [h0, Matrix.mul_zero, Matrix.zero_mul, hJc] at h1
    have := congrFun (congrFun h1 0) 1
    simp at this
  · intro g hg
    set a : Matrix (Fin 2) (Fin 2) F := Pm * (g : Matrix (Fin 2) (Fin 2) F) * Pi with ha
    have haσ : a.map σ = a := by
      ext i j
      exact mem_frobFixed.1 (hg i j)
    have hdet : a.det = 1 := by
      rw [ha, Matrix.det_mul, Matrix.det_mul, mul_comm (Pm.det), mul_assoc, ← Matrix.det_mul,
        hPPi, Matrix.det_one, mul_one, g.2]
    have hga : (g : Matrix (Fin 2) (Fin 2) F) = Pi * a * Pm := by
      rw [ha, show Pi * (Pm * (g : Matrix (Fin 2) (Fin 2) F) * Pi) * Pm =
        (Pi * Pm) * (g : Matrix (Fin 2) (Fin 2) F) * (Pi * Pm) by simp only [Matrix.mul_assoc],
        hPiP, Matrix.one_mul, Matrix.mul_one]
    apply Subtype.ext
    rw [twistRep_apply, hXc, hga]
    have key : Pi * a * Pm * (Pi * (J : Matrix (Fin 2) (Fin 2) F) * (Pi.map σ)ᵀ) *
        ((Pi * a * Pm).map σ)ᵀ =
        Pi * (a * (Pm * Pi) * (J : Matrix (Fin 2) (Fin 2) F) *
          ((Pi.map σ)ᵀ * (Pm.map σ)ᵀ) * (a.map σ)ᵀ) * (Pi.map σ)ᵀ := by
      simp only [Matrix.map_mul, Matrix.transpose_mul, Matrix.mul_assoc]
    rw [key, hPPi, hT, haσ, Matrix.mul_one, Matrix.mul_one, hJc, mul_swap_mul_transpose, hdet,
      one_smul]

@[expose] def uSL (b : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, b; 0, 1], by simp [Matrix.det_fin_two]⟩

theorem uSL_coe (b : F) : (uSL b : Matrix (Fin 2) (Fin 2) F) = !![1, b; 0, 1] := rfl

theorem map_transpose_fin_two (σ : F →+* F) (a b c d : F) :
    (!![a, b; c, d].map σ)ᵀ = !![σ a, σ c; σ b, σ d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem eq_smul_of_twistRep_uSL [CharP F 2] {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) {ω : F}
    (hω : σ ω ≠ ω) (X : twistedForm σ) (hX : ∀ b : F, twistRep hinv (uSL b) X = X) :
    ∃ a : frobFixed σ, X = a • twMk hinv 1 0 0 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hXe := twistedForm_eq X
  set a := (X : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set x := (X : Matrix (Fin 2) (Fin 2) F) 0 1 with hx
  set d := (X : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  have hentry : ∀ b : F, !![1, b; 0, 1] * !![a, x; σ x, d] * (!![1, b; 0, 1].map σ)ᵀ =
      !![a, x; σ x, d] := by
    intro b
    have h := congrArg Subtype.val (hX b)
    rw [twistRep_apply, uSL_coe, hXe] at h
    exact h
  have e : ∀ b : F, x + b * d = x ∧ a + b * σ x + (x + b * d) * σ b = a := by
    intro b
    have h := hentry b
    rw [map_transpose_fin_two, map_one, map_zero, Matrix.mul_fin_two, Matrix.mul_fin_two] at h
    have h01 := congrFun (congrFun h 0) 1
    have h00 := congrFun (congrFun h 0) 0
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_cons] at h01 h00
    exact ⟨by linear_combination h01, by linear_combination h00⟩
  have hd0 : d = 0 := by
    have h := (e 1).1
    linear_combination h
  have hσx : σ x = x := by
    have h := (e 1).2
    rw [hd0, map_one] at h
    linear_combination h - x * h2
  have hx0 : x = 0 := by
    have h := (e ω).2
    rw [hd0, hσx] at h
    have hne : ω + σ ω ≠ 0 := by
      intro h'
      apply hω
      linear_combination h' - ω * h2
    have : x * (ω + σ ω) = 0 := by linear_combination h
    exact (mul_eq_zero.1 this).resolve_right hne
  refine ⟨⟨a, twistedForm_diag_mem X.2 0⟩, ?_⟩
  apply Subtype.ext
  have hrhs : ((⟨a, twistedForm_diag_mem X.2 0⟩ : frobFixed σ) • twMk hinv 1 0 0 :
      twistedForm σ).val = !![a, 0; 0, 0] := by
    rw [Submodule.coe_smul, twMk_coe]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Subfield.smul_def]
  rw [hrhs, hXe, hd0, hx0, map_zero]

theorem twistRep_uSL_e {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) (b : F) :
    twistRep hinv (uSL b) (twMk hinv 1 0 0) = twMk hinv 1 0 0 := by
  apply Subtype.ext
  rw [twistRep_apply, uSL_coe, twMk_coe, map_transpose_fin_two, map_one, map_zero,
    Matrix.mul_fin_two, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

@[expose] def swapSL [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

@[expose] def lSL (y : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; y, 1], by simp [Matrix.det_fin_two]⟩

theorem span_twistRep_orbit_eq_top [CharP F 2] {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) :
    Submodule.span (frobFixed σ)
      (Set.range fun g : SpecialLinearGroup (Fin 2) F => twistRep hinv g (twMk hinv 1 0 0)) =
        ⊤ := by
  refine eq_top_iff.2 fun X _ => ?_
  set S := Set.range fun g : SpecialLinearGroup (Fin 2) F => twistRep hinv g (twMk hinv 1 0 0)
  have hE : twMk hinv 1 0 0 ∈ Submodule.span (frobFixed σ) S :=
    Submodule.subset_span ⟨1, by simp⟩
  have hJ : twistRep hinv swapSL (twMk hinv 1 0 0) ∈ Submodule.span (frobFixed σ) S :=
    Submodule.subset_span ⟨swapSL, rfl⟩
  set x := (X : Matrix (Fin 2) (Fin 2) F) 0 1 with hx
  have hl : twistRep hinv (lSL (σ x)) (twMk hinv 1 0 0) ∈ Submodule.span (frobFixed σ) S :=
    Submodule.subset_span ⟨_, rfl⟩
  have hN : x * σ x ∈ frobFixed σ := mem_frobFixed.2 (by rw [map_mul, hinv, mul_comm])
  have hXe := twistedForm_eq X
  have hdec : X = (⟨(X : Matrix (Fin 2) (Fin 2) F) 0 0, twistedForm_diag_mem X.2 0⟩ - 1 :
      frobFixed σ) • twMk hinv 1 0 0 +
      (⟨(X : Matrix (Fin 2) (Fin 2) F) 1 1, twistedForm_diag_mem X.2 1⟩ - ⟨x * σ x, hN⟩ :
        frobFixed σ) • twistRep hinv swapSL (twMk hinv 1 0 0) +
      twistRep hinv (lSL (σ x)) (twMk hinv 1 0 0) := by
    apply Subtype.ext
    simp only [Submodule.coe_add, Submodule.coe_smul, twistRep_apply, twMk_coe]
    rw [show ((swapSL : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![0, 1; 1, 0] from rfl, show ((lSL (σ x) : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) = !![1, 0; σ x, 1] from rfl, map_transpose_fin_two,
      map_transpose_fin_two, map_one, map_zero, hinv, Matrix.mul_fin_two, Matrix.mul_fin_two,
      Matrix.mul_fin_two, Matrix.mul_fin_two]
    have h10 : (X : Matrix (Fin 2) (Fin 2) F) 1 0 = σ x := (twistedForm_entry X.2 0 1).symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Subfield.smul_def, ← hx, h10] <;> ring
  rw [hdec]
  exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.smul_mem _ _ hE)
    (Submodule.smul_mem _ _ hJ)) hl

theorem eq_frobFixed_or_top {σ : F →+* F} (hinv : ∀ x, σ (σ x) = x) (K₀ : Subfield F)
    (h : frobFixed σ ≤ K₀) : K₀ = frobFixed σ ∨ K₀ = ⊤ := by
  by_cases hK : K₀ ≤ frobFixed σ
  · exact Or.inl (le_antisymm hK h)
  · right
    obtain ⟨x, hxK, hxF⟩ := Set.not_subset.1 hK
    have hx : σ x ≠ x := fun h' => hxF (mem_frobFixed.2 h')
    refine eq_top_iff.2 fun y _ => ?_
    obtain ⟨α, β, hα, hβ, rfl⟩ := exists_frob_decomp hinv hx y
    exact K₀.add_mem (h (mem_frobFixed.2 hα)) (K₀.mul_mem (h (mem_frobFixed.2 hβ)) hxK)

end Fixed

section Model

variable {K : Type} [Field K] {W : Type} [AddCommGroup W] [Module K W]

theorem polarBilin_nondegenerate (Q : QuadraticForm K W)
    (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0) : (polarBilin Q).Nondegenerate :=
  ⟨fun x hx => hnd x fun y => by rw [← polarBilin_apply_apply]; exact hx y,
    fun y hy => hnd y fun x => by rw [polar_comm, ← polarBilin_apply_apply]; exact hy x⟩

@[expose] def coordEquiv {F₀ : Type} [Field F₀] (e : K ≃+* F₀) (ι : Type) :
    (ι → K) ≃ₛₗ[(e : K →+* F₀)] (ι → F₀) where
  toFun v i := e (v i)
  invFun v i := e.symm (v i)
  map_add' v w := funext fun i => map_add e _ _
  map_smul' c v := funext fun i => map_mul e _ _
  left_inv v := funext fun i => e.symm_apply_apply _
  right_inv v := funext fun i => e.apply_symm_apply _

theorem quadMinus_coordEquiv {F₀ : Type} [Field F₀] (e : K ≃+* F₀) (b c : K)
    (v : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) :
    CFSG.LieType.Universal.Spin.quadMinus 2 F₀ (e b) (e c) (coordEquiv e _ v) =
      e (CFSG.LieType.Universal.Spin.quadMinus 2 K b c v) := by
  rw [CFSG.LieType.Universal.Spin.quadMinus_apply, CFSG.LieType.Universal.Spin.quadMinus_apply]
  simp [coordEquiv, map_add, map_mul, map_sum, map_pow]

theorem exists_sl2_model [Finite K] [CharP K 2] (Q : QuadraticForm K W)
    (hdim : finrank K W = 4) (hnd : ∀ x, (∀ y, polar Q x y = 0) → x = 0)
    (hminus : ∀ U : Submodule K W, (∀ u ∈ U, Q u = 0) → finrank K U ≤ 1) :
    ∃ (L : Type) (_ : Field L) (_ : Finite L) (_ : CharP L 2) (ι : K →+* L)
      (ρ : SpecialLinearGroup (Fin 2) L →* (W ≃ₗ[K] W)),
      Nat.card L = Nat.card K ^ 2 ∧
      (∀ y : L, y ∈ ι.fieldRange ↔ y ^ Nat.card K = y) ∧
      (∀ K₀ : Subfield L, ι.fieldRange ≤ K₀ → K₀ = ι.fieldRange ∨ K₀ = ⊤) ∧
      Function.Injective ρ ∧ (∀ g x, Q (ρ g x) = Q x) ∧
      (∀ (r s : W) (g : SpecialLinearGroup (Fin 2) L), reflK Q r * reflK Q s = ρ g →
        ι (polar Q r s) ^ 2 = (g : Matrix (Fin 2) (Fin 2) L).trace *
          (g : Matrix (Fin 2) (Fin 2) L).trace ^ Nat.card K) ∧
      (∀ P : GL (Fin 2) L, ∃ w : W, w ≠ 0 ∧ ∀ g : SpecialLinearGroup (Fin 2) L,
        (∀ i j, ((P : Matrix (Fin 2) (Fin 2) L) * (g : Matrix (Fin 2) (Fin 2) L) *
          ((P⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) i j ∈ ι.fieldRange) →
          ρ g w = w) ∧
      (∃ w₁ : W, w₁ ≠ 0 ∧ (∀ b : L, ρ (uSL b) w₁ = w₁) ∧
        (∀ w : W, (∀ b : L, ρ (uSL b) w = w) → ∃ c : K, w = c • w₁) ∧
        Submodule.span K (Set.range fun g => ρ g w₁) = ⊤) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨k, -, hk⟩ := FiniteField.card K 2
  have hK : Nat.card K = 2 ^ (k : ℕ) := by rw [Nat.card_eq_fintype_card, hk]
  have hk1 : 1 ≤ (k : ℕ) := k.pos
  have hF : Nat.card (GaloisField 2 (2 * k)) = (2 ^ (k : ℕ)) ^ 2 := by
    rw [GaloisField.card 2 (2 * k) (by omega), ← pow_mul, mul_comm]
  obtain ⟨σ, hσ⟩ := exists_frob_ringHom hk1 hF
  have hinv := frob_frob hF hσ
  obtain ⟨ω, hω⟩ := exists_frob_ne hk1 hF hσ
  have h2 := two_eq_zero_of_card hk1 hF
  have hF0 := card_frobFixed hk1 hF hσ
  have : Fintype (frobFixed σ) := Fintype.ofFinite _
  let e : K ≃+* frobFixed σ := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hK, hF0])
  obtain ⟨c, hc⟩ := exists_irred_quadratic (K := K)
  have hc₀ : ∀ s : frobFixed σ, s ^ 2 + e 1 * s + e c ≠ 0 := fun s hs => hc (e.symm s) (by
    have h := congrArg e.symm hs
    simpa only [map_add, map_mul, map_pow, RingEquiv.symm_apply_apply, map_zero] using h)
  have : FiniteDimensional K W := Module.finite_of_finrank_pos (by omega)
  have hQminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
    rintro ⟨U, hU, hUs⟩
    have := hminus U hUs
    omega
  obtain ⟨α⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType
    (polarBilin_nondegenerate Q hnd) (n := 2) (by norm_num) (by rw [hdim]) hQminus hc
  have : Module.Finite (frobFixed σ) (twistedForm σ) := Module.Finite.of_finite
  have hW₀ : finrank (frobFixed σ) (twistedForm σ) = 4 := finrank_twistedForm hinv hω
  have hQ₀minus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType (twistedDet σ) := by
    rintro ⟨U, hU, hUs⟩
    have := finrank_le_one_of_totally_singular U hUs
    omega
  obtain ⟨β⟩ := CFSG.GroupTheory.WeirSylow.nonempty_isometry_of_not_isPlusType
    (polarBilin_nondegenerate (twistedDet σ) (twistedDet_polar_nondegenerate h2 hinv hω))
    (n := 2) (by norm_num) (by rw [hW₀]) hQ₀minus hc₀
  let ψ : W ≃ₛₗ[(e : K →+* frobFixed σ)] twistedForm σ :=
    (α.toLinearEquiv.trans (coordEquiv e _)).trans β.symm.toLinearEquiv
  have hψ : ∀ x, twistedDet σ (ψ x) = e (Q x) := by
    intro x
    change twistedDet σ (β.symm (coordEquiv e _ (α x))) = e (Q x)
    rw [β.symm.map_app, quadMinus_coordEquiv, α.map_app]
  let ι : K →+* GaloisField 2 (2 * k) := (frobFixed σ).subtype.comp (e : K →+* frobFixed σ)
  have hrange : ι.fieldRange = frobFixed σ := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact (e x).2
    · intro hy
      exact ⟨e.symm ⟨y, hy⟩, by simp [ι]⟩
  let ρ := (conjHom e ψ).comp (twistRep hinv)
  have hρ : ∀ g x, ρ g x = ψ.symm (twistRep hinv g (ψ x)) := fun g x => rfl
  have : CharP (frobFixed σ) 2 := inferInstance
  refine ⟨GaloisField 2 (2 * k), inferInstance, inferInstance, inferInstance, ι, ρ, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF, hK]
  · intro y
    rw [hrange, mem_frobFixed, hσ, hK]
  · intro K₀ hK₀
    rw [hrange] at hK₀ ⊢
    exact eq_frobFixed_or_top hinv K₀ hK₀
  · exact (conjHom_injective ψ).comp (twistRep_injective h2 hinv)
  · intro g x
    rw [hρ, symm_transport ψ hψ, twistedDet_twistRep, hψ, RingEquiv.symm_apply_apply]
  · intro r s g hg
    have h1 : twistRep hinv g = reflK (twistedDet σ) (ψ r) * reflK (twistedDet σ) (ψ s) := by
      ext X
      have hX := LinearEquiv.congr_fun hg (ψ.symm X)
      rw [LinearEquiv.mul_apply, hρ, ψ.apply_symm_apply] at hX
      have hX' := congrArg ψ hX
      rw [ψ.apply_symm_apply, ← ψ.symm_apply_apply (reflK Q s (ψ.symm X)), reflK_transport ψ hψ,
        reflK_transport ψ hψ] at hX'
      rw [LinearEquiv.mul_apply, ← hX']
    have h3 := trace_twistRep hinv hω g
    rw [h1, trace_reflK_mul (twistedDet σ) (by rw [hW₀]; decide), polar_transport ψ hψ, hσ,
      ← hK] at h3
    have h4 : ι (polar Q r s) ^ 2 =
        ((e (polar Q r s) ^ 2 : frobFixed σ) : GaloisField 2 (2 * k)) := by
      simp [ι]
    rw [h4, h3]
  · intro P
    obtain ⟨X, hX0, hX⟩ := exists_twistRep_fixed hinv P
    refine ⟨ψ.symm X, fun h => hX0 (by simpa using congrArg ψ h), fun g hg => ?_⟩
    rw [hρ, ψ.apply_symm_apply, hX g (fun i j => hrange ▸ hg i j)]
  · have hψρ : ∀ g w, ψ (ρ g w) = twistRep hinv g (ψ w) := fun g w => by
      rw [hρ, ψ.apply_symm_apply]
    have hE0 : twMk hinv 1 0 0 ≠ 0 := by
      intro h0
      have := congrArg (fun X : twistedForm σ => X.1 0 0) h0
      simp [twMk_coe] at this
    refine ⟨ψ.symm (twMk hinv 1 0 0), fun h => hE0 (by simpa using congrArg ψ h), ?_, ?_, ?_⟩
    · intro b
      rw [hρ, ψ.apply_symm_apply, twistRep_uSL_e]
    · intro w hw
      obtain ⟨a, ha⟩ := eq_smul_of_twistRep_uSL hinv hω (ψ w) fun b => by
        rw [← hψρ, hw b]
      refine ⟨e.symm a, ?_⟩
      have h := congrArg ψ.symm ha
      rw [ψ.symm_apply_apply, LinearEquiv.map_smulₛₗ] at h
      exact h
    · set V := Submodule.span K (Set.range fun g => ρ g (ψ.symm (twMk hinv 1 0 0))) with hV
      have hle : Submodule.span (frobFixed σ) (Set.range fun g : SpecialLinearGroup (Fin 2)
          (GaloisField 2 (2 * k)) => twistRep hinv g (twMk hinv 1 0 0)) ≤
          V.comap (ψ.symm : twistedForm σ →ₛₗ[(e.symm : frobFixed σ →+* K)] W) := by
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        refine Submodule.subset_span ⟨g, ?_⟩
        show ρ g (ψ.symm (twMk hinv 1 0 0)) = ψ.symm (twistRep hinv g (twMk hinv 1 0 0))
        rw [hρ, ψ.apply_symm_apply]
      rw [span_twistRep_orbit_eq_top hinv] at hle
      refine eq_top_iff.2 fun w _ => ?_
      have h := hle (Submodule.mem_top : ψ w ∈ ⊤)
      change ψ.symm (ψ w) ∈ V at h
      rwa [ψ.symm_apply_apply] at h

end Model

end CFSG.Quasithin.SimsG4.OrthMinus
