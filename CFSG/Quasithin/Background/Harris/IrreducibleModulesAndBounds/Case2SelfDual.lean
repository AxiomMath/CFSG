module

public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.Background.SmithB45M22HatHat

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.CharacterTheory.SteinbergBY
  CFSG.CharacterTheory.SteinbergBY.FieldFour CFSG.Quasithin.HatM22
open scoped Matrix

@[expose] def trZ (x : FieldFour) : ZMod 2 := reZ (x + frob x)

theorem trZ_add (x y : FieldFour) : trZ (x + y) = trZ x + trZ y := by
  revert x y; decide

theorem trZ_ω : trZ ω = 1 := by decide

@[expose] def hermF (x y : Fin 6 → FieldFour) : FieldFour :=
  (fun i => frob (x i)) ⬝ᵥ (hatM22Form.mulVec y)

theorem hermF_add_left (x x' y : Fin 6 → FieldFour) :
    hermF (x + x') y = hermF x y + hermF x' y := by
  unfold hermF
  rw [← add_dotProduct]
  congr 1
  funext i
  simp [map_add]

theorem hermF_add_right (x y y' : Fin 6 → FieldFour) :
    hermF x (y + y') = hermF x y + hermF x y' := by
  unfold hermF
  rw [Matrix.mulVec_add, dotProduct_add]

@[expose] noncomputable def hermTrace : LinearMap.BilinForm (ZMod 2) (Fin 6 → FieldFour) :=
  have hc2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
  have hz : ∀ x y : Fin 6 → FieldFour, trZ (hermF 0 y) = 0 ∧ trZ (hermF x 0) = 0 := fun x y => by
    have h1 := hermF_add_left 0 0 y
    have h2 := hermF_add_right x 0 0
    rw [add_zero] at h1 h2
    have e1 : hermF 0 y = 0 := by
      have := congrArg (fun t => t - hermF 0 y) h1
      simpa using this.symm
    have e2 : hermF x 0 = 0 := by
      have := congrArg (fun t => t - hermF x 0) h2
      simpa using this.symm
    rw [e1, e2]
    decide
  LinearMap.mk₂ (ZMod 2) (fun x y => trZ (hermF x y))
    (fun x x' y => by rw [hermF_add_left, trZ_add])
    (fun c x y => by
      rcases hc2 c with rfl | rfl
      · simp only [zero_smul]; exact (hz x y).1.trans (by simp)
      · simp)
    (fun x y y' => by rw [hermF_add_right, trZ_add])
    (fun c x y => by
      rcases hc2 c with rfl | rfl
      · simp only [zero_smul]; exact (hz x y).2.trans (by simp)
      · simp)

theorem hermTrace_apply (x y : Fin 6 → FieldFour) : hermTrace x y = trZ (hermF x y) := rfl

theorem mulVec_dotProduct_transpose {n : Type} [Fintype n] {R : Type} [CommSemiring R]
    (A : Matrix n n R) (v w : n → R) : (A *ᵥ v) ⬝ᵥ w = v ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [Matrix.mulVec_transpose, dotProduct_comm v, dotProduct_comm (A *ᵥ v),
    ← Matrix.dotProduct_mulVec]

theorem hatM22Form_inv_mul : hatM22FormInv * hatM22Form = 1 :=
  mul_eq_one_comm.1 hatM22Form_mul_inv

theorem hermF_eq (x y : Fin 6 → FieldFour) :
    hermF x y = ((fun i => frob (x i)) ᵥ* hatM22Form) ⬝ᵥ y := by
  unfold hermF
  rw [Matrix.dotProduct_mulVec]

theorem hermF_invariant {g : Matrix (Fin 6) (Fin 6) FieldFour}
    (hg : (frobPow 1 g)ᵀ * hatM22Form * g = hatM22Form) (x y : Fin 6 → FieldFour) :
    hermF (g *ᵥ x) (g *ᵥ y) = hermF x y := by
  have h1 : (fun i => frob ((g *ᵥ x) i)) = (g.map frob) *ᵥ (fun i => frob (x i)) := by
    funext i
    exact RingHom.map_mulVec frob g x i
  unfold hermF
  rw [h1, Matrix.mulVec_mulVec, mulVec_dotProduct_transpose, Matrix.mulVec_mulVec,
    ← frobPow_one_eq, ← Matrix.mul_assoc, hg]

theorem hermTrace_invariant {g : Matrix (Fin 6) (Fin 6) FieldFour}
    (hg : (frobPow 1 g)ᵀ * hatM22Form * g = hatM22Form) (x y : Fin 6 → FieldFour) :
    hermTrace (g *ᵥ x) (g *ᵥ y) = hermTrace x y := by
  rw [hermTrace_apply, hermTrace_apply, hermF_invariant hg]

theorem hermTrace_sepLeft : ∀ x : Fin 6 → FieldFour, (∀ y, hermTrace x y = 0) → x = 0 := by
  intro x hx
  by_contra hne
  set sx : Fin 6 → FieldFour := fun i => frob (x i) with hsx
  set u : Fin 6 → FieldFour := sx ᵥ* hatM22Form with hu
  have hsx0 : sx ≠ 0 := by
    intro h0
    apply hne
    funext i
    have := congrFun h0 i
    simp only [hsx, Pi.zero_apply] at this
    have h2 : frob (x i) = frob 0 := by rw [this, map_zero]
    simpa using frob.injective h2
  have hu0 : u ≠ 0 := by
    intro h0
    apply hsx0
    have : u ᵥ* hatM22FormInv = sx := by
      rw [hu, Matrix.vecMul_vecMul, hatM22Form_mul_inv, Matrix.vecMul_one]
    rw [← this, h0, Matrix.zero_vecMul]
  obtain ⟨j, hj⟩ : ∃ j, u j ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hu0 (funext hall)
  have h1 := hx (Pi.single j ((u j)⁻¹ * ω))
  rw [hermTrace_apply, hermF_eq, ← hsx, ← hu, dotProduct_single, mul_inv_cancel_left₀ hj,
    trZ_ω] at h1
  exact one_ne_zero h1

theorem hermTrace_sepRight : ∀ y : Fin 6 → FieldFour, (∀ x, hermTrace x y = 0) → y = 0 := by
  intro y hy
  by_contra hne
  set v : Fin 6 → FieldFour := hatM22Form *ᵥ y with hv
  have hv0 : v ≠ 0 := by
    intro h0
    apply hne
    have : hatM22FormInv *ᵥ v = y := by
      rw [hv, Matrix.mulVec_mulVec, hatM22Form_inv_mul, Matrix.one_mulVec]
    rw [← this, h0, Matrix.mulVec_zero]
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hv0 (funext hall)
  have h1 := hy (Pi.single i (frob ((v i)⁻¹ * ω)))
  have h2 : (fun k => frob ((Pi.single i (frob ((v i)⁻¹ * ω)) : Fin 6 → FieldFour) k)) =
      Pi.single i ((v i)⁻¹ * ω) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [frob_frob]
    · simp [hk]
  rw [hermTrace_apply, hermF, h2, ← hv, single_dotProduct, mul_right_comm, inv_mul_cancel₀ hi, one_mul, trZ_ω] at h1
  exact one_ne_zero h1

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem selfDual_of_hatM22 {L : Subgroup (GLV V)} (ψ : V ≃ₗ[ZMod 2] (Fin 6 → FieldFour))
    (hψ : ∀ k ∈ L, ∃ γ : ↥hatM22Γ₀, ∀ v : V,
      ψ (k v) = (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour)).mulVec (ψ v)) :
    SelfDual L ⊤ := by
  let e : ↥(⊤ : Submodule (ZMod 2) V) ≃ₗ[ZMod 2] (Fin 6 → FieldFour) :=
    Submodule.topEquiv.trans ψ
  refine ⟨hermTrace.compl₁₂ e.toLinearMap e.toLinearMap, ⟨?_, ?_⟩, ?_⟩
  · intro i hi
    apply e.injective
    rw [map_zero]
    apply hermTrace_sepLeft
    intro y
    simpa using hi (e.symm y)
  · intro j hj
    apply e.injective
    rw [map_zero]
    apply hermTrace_sepRight
    intro x
    simpa using hj (e.symm x)
  · intro k hk i j i' j' hi hj
    obtain ⟨γ, hγ⟩ := hψ k hk
    have hki : e i' = (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour)).mulVec (e i) := by
      have h := hγ (i : V)
      show ψ (i' : V) = _
      rw [← hi]; exact h
    have hkj : e j' = (((γ : Matrix.GeneralLinearGroup (Fin 6) FieldFour) :
        Matrix (Fin 6) (Fin 6) FieldFour)).mulVec (e j) := by
      have h := hγ (j : V)
      show ψ (j' : V) = _
      rw [← hj]; exact h
    simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe]
    rw [hki, hkj, hermTrace_invariant (hatM22Form_invariant γ γ.2)]

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
