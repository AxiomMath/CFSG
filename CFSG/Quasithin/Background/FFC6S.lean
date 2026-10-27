module

public import CFSG.Quasithin.Background.FFC5Coh3

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Quasithin.JonesParshall Matrix

section Tau

@[expose] def tauSL : SL3F2 →* SL3F2 where
  toFun γ := ⟨((γ⁻¹ : SL3F2) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ, by
    rw [Matrix.det_transpose]
    exact (γ⁻¹).2⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' γ δ := by
    apply Subtype.ext
    show (((γ * δ)⁻¹ : SL3F2) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ =
      ((γ⁻¹ : SL3F2) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *
        ((δ⁻¹ : SL3F2) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ
    rw [_root_.mul_inv_rev, Matrix.SpecialLinearGroup.coe_mul, Matrix.transpose_mul]

theorem tauSL_inv_coe (γ : SL3F2) :
    (((tauSL γ)⁻¹ : SL3F2) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = (γ : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ := by
  rw [← map_inv]
  show ((((γ⁻¹)⁻¹ : SL3F2) : Matrix (Fin 3) (Fin 3) (ZMod 2)))ᵀ = _
  rw [inv_inv]

theorem tauSL_tauSL (γ : SL3F2) : tauSL (tauSL γ) = γ := by
  apply Subtype.ext
  show (((tauSL γ)⁻¹ : SL3F2) : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = _
  rw [tauSL_inv_coe, Matrix.transpose_transpose]

end Tau

section Dual

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent in
theorem card_le_card_dual {E : Type} [AddCommGroup E] [Finite E] [Module (ZMod 2) E] :
    Nat.card E ≤ Nat.card (E →+ ZMod 2) := by
  classical
  have : Fintype E := Fintype.ofFinite E
  have hfin : FiniteDimensional (ZMod 2) E := Module.Finite.of_finite
  have hE : Fintype.card E = 2 ^ Module.finrank (ZMod 2) E := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := E)
    simpa [ZMod.card] using this
  let e : (E →+ ZMod 2) ≃ Module.Dual (ZMod 2) E :=
    { toFun := fun f =>
        { toFun := f
          map_add' := f.map_add
          map_smul' := fun c x => by
            rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
            · simp
            · simp }
      invFun := fun f => f.toAddMonoidHom
      left_inv := fun f => rfl
      right_inv := fun f => rfl }
  have : Finite (Module.Dual (ZMod 2) E) :=
    Finite.of_injective (fun f : Module.Dual (ZMod 2) E => (f : E → ZMod 2)) DFunLike.coe_injective
  have : Fintype (Module.Dual (ZMod 2) E) := Fintype.ofFinite _
  have hD : Fintype.card (Module.Dual (ZMod 2) E) =
      2 ^ Module.finrank (ZMod 2) (Module.Dual (ZMod 2) E) := by
    have := Module.card_eq_pow_finrank (K := ZMod 2) (V := Module.Dual (ZMod 2) E)
    simpa [ZMod.card] using this
  rw [Subspace.dual_finrank_eq] at hD
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hE, hD]

end Dual

section Main

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

variable {E : Type} [AddCommGroup E]

theorem dot_formula (θ : E →+ (Fin 3 → ZMod 2)) (w : Fin 3 → E)
    (hw : ∀ i, θ (w i) = Pi.single i 1) (h : E →+ ZMod 2) (hh : ∀ m, θ m = 0 → h m = 0) (m : E) :
    h m = ∑ i, θ m i * h (w i) := by
  have hθm' : θ (∑ i, (θ m i).val • w i) = θ m := by
    rw [map_sum]
    simp only [map_nsmul, hw]
    have h1 : ∀ i, (θ m i).val • (Pi.single i (1 : ZMod 2) : Fin 3 → ZMod 2) =
        Pi.single i (θ m i) := by
      intro i
      rw [← Pi.single_smul]
      congr 1
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_zmod_val]
    simp only [h1]
    exact Finset.univ_sum_single (θ m)
  have h1 : h (m - ∑ i, (θ m i).val • w i) = 0 := hh _ (by rw [map_sub, hθm', sub_self])
  rw [map_sub, sub_eq_zero] at h1
  rw [h1, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

@[expose] def evalW (w : Fin 3 → E) (h : E →+ ZMod 2) : Fin 3 → ZMod 2 := fun i => h (w i)

theorem evalW_add (w : Fin 3 → E) (h h' : E →+ ZMod 2) :
    evalW w (h + h') = evalW w h + evalW w h' := rfl

theorem evalW_sub (w : Fin 3 → E) (h h' : E →+ ZMod 2) :
    evalW w (h - h') = evalW w h - evalW w h' := rfl

theorem evalW_inj (θ : E →+ (Fin 3 → ZMod 2)) (w : Fin 3 → E) (hw : ∀ i, θ (w i) = Pi.single i 1)
    (h : E →+ ZMod 2) (hh : ∀ m, θ m = 0 → h m = 0) (h0 : evalW w h = 0) : h = 0 := by
  ext m
  rw [dot_formula θ w hw h hh m]
  have : ∀ i, h (w i) = 0 := fun i => congrFun h0 i
  simp [this]

theorem evalW_comp (μ : SL3F2 →* AddMonoid.End E) (θ : E →+ (Fin 3 → ZMod 2)) (w : Fin 3 → E)
    (hw : ∀ i, θ (w i) = Pi.single i 1) (hθe : ∀ γ m, θ (μ γ m) = muF2 3 γ (θ m))
    (h : E →+ ZMod 2) (hh : ∀ m, θ m = 0 → h m = 0) (y : SL3F2) :
    evalW w (h.comp (μ y)) = (y : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ evalW w h := by
  funext i
  show h (μ y (w i)) = _
  rw [dot_formula θ w hw h hh, hθe, hw i,
    show muF2 3 y (Pi.single i 1) = (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Pi.single i 1 from rfl,
    Matrix.mulVec_single_one]
  simp [Matrix.mulVec, dotProduct, Matrix.col, evalW]

@[expose] def ccf (μ : SL3F2 →* AddMonoid.End E) (f : E →+ ZMod 2) (x : SL3F2) : E →+ ZMod 2 :=
  f.comp (μ x⁻¹) - f

theorem ccf_apply (μ : SL3F2 →* AddMonoid.End E) (f : E →+ ZMod 2) (x : SL3F2) (m : E) :
    ccf μ f x m = f (μ x⁻¹ m) - f m := rfl

theorem ccf_van (μ : SL3F2 →* AddMonoid.End E) (θ : E →+ (Fin 3 → ZMod 2))
    (hker : ∀ m, θ m = 0 → ∀ γ, μ γ m = m) (f : E →+ ZMod 2) (x : SL3F2) :
    ∀ m, θ m = 0 → ccf μ f x m = 0 := by
  intro m hm
  rw [ccf_apply, hker m hm, sub_self]

theorem ccf_mul (μ : SL3F2 →* AddMonoid.End E) (f : E →+ ZMod 2) (x y : SL3F2) :
    ccf μ f (x * y) = ccf μ f x + (ccf μ f y).comp (μ x⁻¹) := by
  ext m
  have h1 : ((ccf μ f y).comp (μ x⁻¹)) m = ccf μ f y (μ x⁻¹ m) := rfl
  rw [AddMonoidHom.add_apply, h1, ccf_apply, ccf_apply, ccf_apply, _root_.mul_inv_rev, map_mul]
  show f (μ y⁻¹ (μ x⁻¹ m)) - f m = f (μ x⁻¹ m) - f m + (f (μ y⁻¹ (μ x⁻¹ m)) - f (μ x⁻¹ m))
  abel

theorem ccf_add (μ : SL3F2 →* AddMonoid.End E) (f f' : E →+ ZMod 2) (x : SL3F2) :
    ccf μ (f + f') x = ccf μ f x + ccf μ f' x := by
  ext m
  simp only [ccf_apply, AddMonoidHom.add_apply]
  abel

@[expose] def Gcoc (μ : SL3F2 →* AddMonoid.End E) (w : Fin 3 → E) (f : E →+ ZMod 2) (γ : SL3F2) :
    Fin 3 → ZMod 2 := evalW w (ccf μ f (tauSL γ))

theorem Gcoc_cocycle (μ : SL3F2 →* AddMonoid.End E) (θ : E →+ (Fin 3 → ZMod 2)) (w : Fin 3 → E)
    (hw : ∀ i, θ (w i) = Pi.single i 1) (hθe : ∀ γ m, θ (μ γ m) = muF2 3 γ (θ m))
    (hker : ∀ m, θ m = 0 → ∀ γ, μ γ m = m) (f : E →+ ZMod 2) :
    Gcoc μ w f ∈ Z1A (muF2 3) := by
  intro γ δ
  show evalW w (ccf μ f (tauSL (γ * δ))) =
    evalW w (ccf μ f (tauSL γ)) + muF2 3 γ (evalW w (ccf μ f (tauSL δ)))
  rw [map_mul, ccf_mul, evalW_add,
    evalW_comp μ θ w hw hθe _ (ccf_van μ θ hker f (tauSL δ)) (tauSL γ)⁻¹, tauSL_inv_coe,
    Matrix.transpose_transpose]
  rfl

theorem card_le_sixteen [Finite E] [Module (ZMod 2) E]
    (μ : SL3F2 →* AddMonoid.End E) (θ : E →+ (Fin 3 → ZMod 2)) (hθs : Function.Surjective θ)
    (hθe : ∀ γ m, θ (μ γ m) = muF2 3 γ (θ m)) (hker : ∀ m, θ m = 0 → ∀ γ, μ γ m = m)
    (hinv : ∀ f : E →+ ZMod 2, (∀ γ m, f (μ γ m) = f m) → f = 0) : Nat.card E ≤ 16 := by
  classical
  choose w hw using fun i : Fin 3 => hθs (Pi.single i 1)
  let Ψ : (E →+ ZMod 2) →+ (SL3F2 → Fin 3 → ZMod 2) :=
    { toFun := fun f γ => Gcoc μ w f γ
      map_zero' := by
        funext γ
        show evalW w (ccf μ 0 (tauSL γ)) = 0
        have : ccf μ 0 (tauSL γ) = 0 := by
          ext m
          simp [ccf_apply]
        rw [this]
        rfl
      map_add' := fun f f' => by
        funext γ
        show evalW w (ccf μ (f + f') (tauSL γ)) =
          evalW w (ccf μ f (tauSL γ)) + evalW w (ccf μ f' (tauSL γ))
        rw [ccf_add, evalW_add] }
  have hΨinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro f hf
    have h1 : ∀ x : SL3F2, evalW w (ccf μ f x) = 0 := by
      intro x
      have h := congrFun hf (tauSL x)
      have h' : evalW w (ccf μ f (tauSL (tauSL x))) = 0 := h
      rwa [tauSL_tauSL] at h'
    have h2 : ∀ x : SL3F2, ccf μ f x = 0 := fun x =>
      evalW_inj θ w hw _ (ccf_van μ θ hker f x) (h1 x)
    refine hinv f fun γ m => ?_
    have h3 := congrArg (fun g : E →+ ZMod 2 => g m) (h2 γ⁻¹)
    simp only [ccf_apply, inv_inv] at h3
    exact sub_eq_zero.1 h3
  have hcases : ∀ f, Ψ f ∈ B1A (muF2 3) ∨ Ψ f - cocycle3 ∈ B1A (muF2 3) := fun f =>
    Z1A_three_cases (Gcoc_cocycle μ θ w hw hθe hker f)
  let φ : (E →+ ZMod 2) → ↥(B1A (muF2 3)) × Bool := fun f =>
    if h : Ψ f ∈ B1A (muF2 3) then (⟨Ψ f, h⟩, false)
    else (⟨Ψ f - cocycle3, (hcases f).resolve_left h⟩, true)
  have hφ : Function.Injective φ := by
    intro f f' hff'
    apply hΨinj
    by_cases h : Ψ f ∈ B1A (muF2 3) <;> by_cases h' : Ψ f' ∈ B1A (muF2 3)
    · simp only [φ, h, h', dite_true] at hff'
      exact congrArg Subtype.val (Prod.mk.inj hff').1
    · simp [φ, h, h'] at hff'
    · simp [φ, h, h'] at hff'
    · simp only [φ, h, h', dite_false] at hff'
      have := congrArg Subtype.val (Prod.mk.inj hff').1
      exact sub_left_injective this
  have hB8 : Nat.card ↥(B1A (muF2 3)) ≤ 8 := by
    have h1 : Function.Surjective (coboundaryA (muF2 3)).rangeRestrict :=
      AddMonoidHom.rangeRestrict_surjective _
    have h2 := Nat.card_le_card_of_surjective _ h1
    have h3 : Nat.card (Fin 3 → ZMod 2) = 8 := by
      rw [Nat.card_eq_fintype_card]
      simp [ZMod.card]
    exact h3 ▸ h2
  calc Nat.card E ≤ Nat.card (E →+ ZMod 2) := card_le_card_dual
    _ ≤ Nat.card (↥(B1A (muF2 3)) × Bool) := Nat.card_le_card_of_injective φ hφ
    _ = Nat.card ↥(B1A (muF2 3)) * 2 := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    _ ≤ 8 * 2 := Nat.mul_le_mul_right 2 hB8

end Main

end FFC

end CFSG.Quasithin
