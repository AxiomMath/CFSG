module

public import CFSG.Quasithin.H13.L32NLem1442r
public import CFSG.Quasithin.H13.L32NLem1442e
public import CFSG.Quasithin.H13.L32NLem14324a
public import CFSG.Quasithin.H13.L32NLem14411b

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Matrix

namespace L1442

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

theorem case5_of_model (h12213 : Stmt12_2_13) (h9 : G112Concl9 (D.img (l32nH T V)))
    {b₁ b₂ : Bool} {e : D.V ≃ₗ[ZMod 2] (Fin 8 → ZMod 2)}
    (he : ∀ φ : D.V ≃ₗ[ZMod 2] D.V, φ ∈ D.img (l32nH T V) ↔ ∃ γ ∈ L1442M.g5 b₁ b₂,
      ∀ v, e (φ v) = (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)).mulVec (e v)) :
    Case1442Five T V V₂ g D := by
  classical
  have hB := C.g111.toG101Hyp
  obtain ⟨q, hqU, hqB, hqΓ⟩ := C.exists_quad h12213
  obtain ⟨B', hB'⟩ : ∃ B' : LinearMap.BilinForm (ZMod 2) (Fin 8 → ZMod 2),
      B' = D.B.compl₁₂ e.symm.toLinearMap e.symm.toLinearMap := ⟨_, rfl⟩
  have hB'v : ∀ x y, B' x y = D.B (e.symm x) (e.symm y) := fun x y => by
    rw [hB']
    rfl
  have hQ' : ∀ x y, q (e.symm (x + y)) = q (e.symm x) + q (e.symm y) + B' x y := by
    intro x y
    rw [map_add, hqB, hB'v]
  have hB'ne : B' ≠ 0 := by
    intro h0
    apply C.πa_ne
    refine hB.nondegenerate _ fun w => ?_
    have h1 := LinearMap.congr_fun₂ h0 (e (D.π a)) (e w)
    rwa [hB'v, LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply] at h1
  have hinv' : ∀ γ ∈ L1442M.g5 b₁ b₂, ∀ x,
      q (e.symm ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x)) = q (e.symm x) := by
    intro γ hγ x
    have hφ : e.trans ((L14411.linOf γ).trans e.symm) ∈ D.img (l32nH T V) :=
      (he _).mpr ⟨γ, hγ, fun v => by
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          L14411.linOf_apply]⟩
    have h1 := hqΓ _ hφ (e.symm x)
    rwa [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      L14411.linOf_apply] at h1
  obtain ⟨m, hm, hmq⟩ := L1442Q.quad_eq_model b₁ b₂ (Q' := fun x => q (e.symm x)) hQ' hB'ne hinv'
  have hm' : ∀ x y : Fin 8 → ZMod 2, (m : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x =
      (m : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ y → x = y := by
    intro x y hxy
    have h1 := congrArg
      (fun z => ((m⁻¹ : GL (Fin 8) (ZMod 2)) : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ z) hxy
    simp only [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at h1
    exact h1
  have hmγ : ∀ γ ∈ L1442M.g5 b₁ b₂, ∀ x, (m : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ
      ((γ : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) =
        (γ : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ ((m : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ x) := by
    intro γ hγ x
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul, hm γ hγ]
  set e₁ := e.trans (L14411.linOf m) with he₁
  have he₁v : ∀ v, e₁ v = (m : Matrix (Fin 8) (Fin 8) (ZMod 2)) *ᵥ e v := fun v => rfl
  have hX8 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 3 := by
    obtain ⟨k, hk⟩ := C.exists_card_X
    have hlt : ¬ 16 ≤ Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) := fun h16 =>
      L14324.false_of_concl9 C.X_le hB.X_sq hk h16 h9
    have hlow := C.lower
    rw [h9.1] at hlow
    rw [hk] at hlt hlow ⊢
    have hk3 : 3 ≤ k := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hlow)
    have hk4 : k < 4 := by
      by_contra h4
      exact hlt (by
        have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 4 ≤ k by omega)
        simpa using this)
    rw [show k = 3 by omega]
  refine ⟨b₁, b₂, e₁, ⟨fun u hu => ?_, fun φ => ?_⟩, hX8⟩
  · have h1 := hmq (e (D.π u))
    simp only [LinearEquiv.symm_apply_apply] at h1
    rw [he₁v, ← h1, hqU u hu, sq]
  · rw [he φ]
    constructor
    · rintro ⟨γ, hγ, hγv⟩
      refine ⟨γ, hγ, fun v => ?_⟩
      rw [he₁v, he₁v, hγv, hmγ γ hγ]
    · rintro ⟨γ, hγ, hγv⟩
      refine ⟨γ, hγ, fun v => hm' _ _ ?_⟩
      rw [← he₁v, hγv, he₁v, hmγ γ hγ]

end Ctx

end L1442

end CFSG.Quasithin.H13
