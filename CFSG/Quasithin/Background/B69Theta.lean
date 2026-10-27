module

public import CFSG.Quasithin.Background.HSL3Bridge

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix H H.SL3Pair
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification

namespace B69

variable {K : Type} [Field K]

theorem finrank_coordImage [Finite K] (σ : K ≃+* K) (W : Submodule K (Fin 3 → K)) :
    Module.finrank K (coordImage σ W) = Module.finrank K W := by
  have e : W ≃ coordImage σ W :=
    { toFun := fun w => ⟨fun i => σ (w.1 i), coord_mem_coordImage w.2⟩
      invFun := fun v => ⟨fun i => σ.symm (v.1 i), v.2⟩
      left_inv := fun w => by ext i; simp
      right_inv := fun v => by ext i; simp }
  have h1 : Nat.card ↥(coordImage σ W) = Nat.card K ^ Module.finrank K (coordImage σ W) :=
    Module.natCard_eq_pow_finrank (K := K) (V := coordImage σ W)
  have h2 : Nat.card ↥W = Nat.card K ^ Module.finrank K W :=
    Module.natCard_eq_pow_finrank (K := K) (V := W)
  have h3 : Nat.card ↥(coordImage σ W) = Nat.card ↥W := (Nat.card_congr e).symm
  rw [h1, h2] at h3
  exact Nat.pow_right_injective (Finite.one_lt_card (α := K)) h3

omit [Field K] in
theorem finrank_map_mulVecLin [Field K] (A : GL (Fin 3) K) (W : Submodule K (Fin 3 → K)) :
    Module.finrank K (W.map (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) K))) =
      Module.finrank K W := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin 3) (Fin 3) K)) := by
    exact Matrix.mulVec_injective_iff_isUnit.2 A.isUnit
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm

theorem type_preserving_of_semilinear [Finite K] (A : GL (Fin 3) K) (σ : K ≃+* K) :
    ∀ W : Submodule K (Fin 3 → K), Module.finrank K W = 1 →
      ∃ W' : Submodule K (Fin 3 → K), Module.finrank K W' = 1 ∧
        (projStabilizer W).map ((LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K σ : MulAut (projectiveSL 3 K)) :
          projectiveSL 3 K →* projectiveSL 3 K) = projStabilizer W' := by
  intro W hW
  obtain ⟨-, -, -, -, -, -, hc, hf, -⟩ := standard_automorphism_transport (K := K) (n := 3)
  refine ⟨(coordImage σ W).map (mulVecLin (A : Matrix (Fin 3) (Fin 3) K)), ?_, ?_⟩
  · rw [finrank_map_mulVecLin, finrank_coordImage, hW]
  · have e : ((LinearFlag.conjAut 3 K A * LinearFlag.fieldAut 3 K σ : MulAut (projectiveSL 3 K)) :
        projectiveSL 3 K →* projectiveSL 3 K) =
        (LinearFlag.conjAut 3 K A : projectiveSL 3 K →* projectiveSL 3 K).comp
          (LinearFlag.fieldAut 3 K σ : projectiveSL 3 K →* projectiveSL 3 K) := rfl
    rw [e, ← Subgroup.map_map, hf, hc]

section Dual

variable [Finite K]

theorem exists_dual_coord {L : Type*} [Group L] [Group.IsPerfect L] {M : Type*} [CommGroup M]
    (ρ : L →* MulAut M) (r₁ r₂ : L →* ↥(StatedSL 3 K)) (thb : MulAut (projectiveSL 3 K))
    (hthb : ∀ l, thb (proj 3 K ((slEquiv K).symm (r₁ l))) = proj 3 K ((slEquiv K).symm (r₂ l)))
    (hnot : ¬ ∀ W : Submodule K (Fin 3 → K), Module.finrank K W = 1 →
      ∃ W' : Submodule K (Fin 3 → K), Module.finrank K W' = 1 ∧
        (projStabilizer W).map (thb : projectiveSL 3 K →* projectiveSL 3 K) = projStabilizer W')
    (e₂ : M ≃* StdMod (Fin 3) K)
    (he₂ : ∀ (l : L) (s : M), e₂ (ρ l s) = matAut ((r₂ l : ↥(StatedSL 3 K)) : GL (Fin 3) K) (e₂ s)) :
    ∃ e₂' : M ≃* StdMod (Fin 3) K, ∀ (l : L) (s : M),
      e₂' (ρ l s) = matAut (dualGL ((r₁ l : ↥(StatedSL 3 K)) : GL (Fin 3) K)) (e₂' s) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := K) (n := 3) le_rfl
  obtain ⟨A, σ, ε, hε, hθ⟩ := hgen thb
  have hε1 : ε = 1 := by
    by_contra hne
    have hε0 : ε = 0 := by omega
    apply hnot
    rw [hε0, pow_zero, mul_one] at hθ
    intro W hW
    rw [hθ]
    exact type_preserving_of_semilinear A σ W hW
  subst hε1
  set θ := CFSG.QuasithinUnique.K1.stdAut A σ 1 with hθdef
  have hdesc : descendAut 3 K θ = thb := by
    rw [hθdef, CFSG.QuasithinUnique.K1.descendAut_stdAut, hθ]
  let ρ₁ : L →* Matrix.SpecialLinearGroup (Fin 3) K := (slEquiv K).symm.toMonoidHom.comp r₁
  let ρ₂ : L →* Matrix.SpecialLinearGroup (Fin 3) K := (slEquiv K).symm.toMonoidHom.comp r₂
  let β : L →* Matrix.SpecialLinearGroup (Fin 3) K := (θ : _ →* _).comp ρ₁
  have hcen : ∀ l, (β l)⁻¹ * ρ₂ l ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
    intro l
    have h1 : proj 3 K (β l) = proj 3 K (ρ₂ l) := by
      have := hthb l
      rw [← hdesc, descendAut_proj] at this
      exact this
    rw [← scalars_eq_center]
    exact proj_eq_proj_iff.mp h1
  let d : L →* Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) :=
    { toFun := fun x => ⟨(β x)⁻¹ * ρ₂ x, hcen x⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := by
        intro x y
        apply Subtype.ext
        change (β (x * y))⁻¹ * ρ₂ (x * y) = ((β x)⁻¹ * ρ₂ x) * ((β y)⁻¹ * ρ₂ y)
        have hcx := Subgroup.mem_center_iff.mp (hcen x) (β y)⁻¹
        calc (β (x * y))⁻¹ * ρ₂ (x * y) = (β y)⁻¹ * ((β x)⁻¹ * ρ₂ x) * ρ₂ y := by
              rw [map_mul, map_mul]; group
          _ = ((β x)⁻¹ * ρ₂ x) * (β y)⁻¹ * ρ₂ y := by rw [hcx]
          _ = ((β x)⁻¹ * ρ₂ x) * ((β y)⁻¹ * ρ₂ y) := by rw [mul_assoc] }
  have hd := CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_one_of_commutative d
  have key : ∀ l, r₂ l = slEquiv K (θ ((slEquiv K).symm (r₁ l))) := by
    intro l
    have h3 : (β l)⁻¹ * ρ₂ l = 1 := by
      have := congrArg (fun f : L →* Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) =>
        (f l : Matrix.SpecialLinearGroup (Fin 3) K)) hd
      simpa [d] using this
    have h4 : ρ₂ l = β l := (inv_mul_eq_one.mp h3).symm
    have h5 := congrArg (slEquiv K) h4
    rw [show ρ₂ l = (slEquiv K).symm (r₂ l) from rfl, MulEquiv.apply_symm_apply] at h5
    exact h5
  have hmat : ∀ l, ((r₂ l : ↥(StatedSL 3 K)) : GL (Fin 3) K) =
      A * mapGL σ (dualGL ((r₁ l : ↥(StatedSL 3 K)) : GL (Fin 3) K)) * A⁻¹ := by
    intro l
    apply Units.ext
    rw [key l, Units.val_mul, Units.val_mul, coe_mapGL, coe_slEquiv, hθdef,
      CFSG.QuasithinUnique.K1.coe_stdAut_one, coe_dualGL]
    conv_rhs => rw [← MulEquiv.apply_symm_apply (slEquiv K) (r₁ l), coe_slEquiv_inv]
  refine ⟨e₂.trans (twistAut A σ), fun l s => ?_⟩
  show twistAut A σ (e₂ (ρ l s)) = matAut (dualGL ((r₁ l : ↥(StatedSL 3 K)) : GL (Fin 3) K))
    (twistAut A σ (e₂ s))
  rw [he₂ l s, hmat l]
  have := congrArg (fun f : MulAut (StdMod (Fin 3) K) => f (e₂ s))
    (twistAut_mul A (dualGL ((r₁ l : ↥(StatedSL 3 K)) : GL (Fin 3) K)) σ)
  simpa using this

end Dual

end B69

end CFSG.Quasithin
