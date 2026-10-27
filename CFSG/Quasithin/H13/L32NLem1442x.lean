module

public import CFSG.Quasithin.H13.L32NLem1442e
public import CFSG.Quasithin.H13.L32NItems144c
public import CFSG.Quasithin.H13.L32NLem14412a

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique Matrix

namespace L1442X

theorem card_le_of_model {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    {Γ X : Subgroup (V ≃ₗ[ZMod 2] V)} {e : V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)}
    (he : ∀ φ : V ≃ₗ[ZMod 2] V, φ ∈ Γ ↔ ∃ γ ∈ L1442M.m22,
      ∀ v, e (φ v) = (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (e v))
    (hrank : ∀ E : Subgroup (GL (Fin 12) (ZMod 2)), E ≤ L1442M.m22 → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ 2 ^ 5)
    (hXΓ : X ≤ Γ) (hsq : ∀ x ∈ X, x * x = 1) : Nat.card X ≤ 2 ^ 5 := by
  have hle : X.map (L14411.matOfN e) ≤ L1442M.m22 := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨γ, hγ, hγv⟩ := (he x).mp (hXΓ hx)
    rwa [(L14411.matOfN_eq_iff e x γ).mpr hγv]
  have hsq' : ∀ y ∈ X.map (L14411.matOfN e), y * y = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, hsq x hx, map_one]
  have h := hrank _ hle hsq'
  rwa [Subgroup.card_map_of_injective (L14411.matOfN_injective e)] at h

end L1442X

namespace L1442

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ : Subgroup G} {g a : G} {D : HatModelU (fsuU T V)}
  (C : Ctx G T L V V₂ g a D)
include C

theorem case6_of_model (h12213 : Stmt12_2_13)
    (h13 : G11.SzG11S.G112Concl13S (D.img (l32nH T V)))
    {e : D.V ≃ₗ[ZMod 2] (Fin 12 → ZMod 2)}
    (he : ∀ φ : D.V ≃ₗ[ZMod 2] D.V, φ ∈ D.img (l32nH T V) ↔ ∃ γ ∈ L1442M.m22,
      ∀ v, e (φ v) = (γ : Matrix (Fin 12) (Fin 12) (ZMod 2)).mulVec (e v))
    (hrank : ∀ E : Subgroup (GL (Fin 12) (ZMod 2)), E ≤ L1442M.m22 → (∀ x ∈ E, x * x = 1) →
      Nat.card E ≤ 2 ^ 5)
    (huniq : ∀ {Q' : (Fin 12 → ZMod 2) → ZMod 2}
      {B' : LinearMap.BilinForm (ZMod 2) (Fin 12 → ZMod 2)},
      (∀ x y, Q' (x + y) = Q' x + Q' y + B' x y) → B' ≠ 0 →
      (∀ γ ∈ L1442M.m22, ∀ x, Q' ((γ : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ x) = Q' x) →
      ∀ x, Q' x = L1442M.quadOf L1442M.q12 x) :
    Case1442Six T V V₂ g D := by
  classical
  have hB := C.g111.toG101Hyp
  obtain ⟨q, hqU, hqB, hqΓ⟩ := C.exists_quad h12213
  obtain ⟨B', hB'⟩ : ∃ B' : LinearMap.BilinForm (ZMod 2) (Fin 12 → ZMod 2),
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
  have hinv' : ∀ γ ∈ L1442M.m22, ∀ x,
      q (e.symm ((γ : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ x)) = q (e.symm x) := by
    intro γ hγ x
    have hφ : e.trans ((L14411.linOfN γ).trans e.symm) ∈ D.img (l32nH T V) :=
      (he _).mpr ⟨γ, hγ, fun v => by
        rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          L14411.linOfN_apply]⟩
    have h1 := hqΓ _ hφ (e.symm x)
    rwa [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
      L14411.linOfN_apply] at h1
  have hq12 := huniq (Q' := fun x => q (e.symm x)) hQ' hB'ne hinv'
  have hX5 : Nat.card ↥(D.img (CFSG.conjugate (l32nW T V V₂) g)) = 2 ^ 5 := by
    have hup := L1442X.card_le_of_model he hrank C.X_le hB.X_sq
    have hlow := C.lower
    rw [h13.1.1] at hlow
    exact le_antisymm hup (by simpa using hlow)
  refine ⟨e, ⟨fun u hu => ?_, he⟩, hX5⟩
  have h1 := hq12 (e (D.π u))
  simp only [LinearEquiv.symm_apply_apply] at h1
  rw [← h1, hqU u hu, sq]

end Ctx

end L1442

end CFSG.Quasithin.H13
