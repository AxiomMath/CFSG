module

public import CFSG.Quasithin.Background.HL3NineW9
public import CFSG.Quasithin.Background.H47WBase
public import CFSG.Quasithin.Vol2.Ch9L34NormGen

public section

namespace CFSG.Quasithin.H47W

open CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.Ch9.L34M
  CFSG.Quasithin.H13.Ch9.L34N CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H.L3W9
  CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H CFSG.Fischer

theorem congr_trans_hom {V W X : Type} [CommGroup V] [CommGroup W] [CommGroup X]
    (e : V ≃* W) (f : W ≃* X) :
    (MulAut.congr (e.trans f)).toMonoidHom =
      (MulAut.congr f).toMonoidHom.comp (MulAut.congr e).toMonoidHom := by
  ext g x
  simp [MulAut.congr_apply]

theorem map_congr_trans' {V W X : Type} [CommGroup V] [CommGroup W] [CommGroup X]
    (e : V ≃* W) (f : W ≃* X) (S : Subgroup (MulAut V)) :
    S.map (MulAut.congr (e.trans f)).toMonoidHom =
      (S.map (MulAut.congr e).toMonoidHom).map (MulAut.congr f).toMonoidHom := by
  rw [congr_trans_hom, ← Subgroup.map_map]

theorem map_congr_symm {V W : Type} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (S : Subgroup (MulAut V)) :
    (S.map (MulAut.congr e).toMonoidHom).map (MulAut.congr e.symm).toMonoidHom = S := by
  rw [Subgroup.map_map, ← congr_trans_hom]
  have h : e.trans e.symm = MulEquiv.refl V := MulEquiv.ext fun x => by simp
  rw [h]
  have h2 : (MulAut.congr (MulEquiv.refl V)).toMonoidHom = MonoidHom.id (MulAut V) := by
    ext g x
    simp [MulAut.congr_apply]
  rw [h2, Subgroup.map_id]

theorem rk_commV_congr_eq {V W : Type} [CommGroup V] [Finite V] [CommGroup W] [Finite W]
    (e : V ≃* W) (g : MulAut V) :
    rk ↥(commV (Subgroup.zpowers (MulAut.congr e g))) = rk ↥(commV (Subgroup.zpowers g)) := by
  have h1 := rk_commV_zpowers_eq_sub (MulAut.congr e g)
  have h2 := rk_commV_zpowers_eq_sub g
  have h3 := rk_fixV_zpowers_congr e g
  have h4 : rk V = rk W := by
    unfold rk
    rw [Nat.card_congr e.toEquiv]
  omega

theorem hmodEquiv_apply {K : Type} [Field K] [Finite K] [CharP K 2] (φ0 : K ≃+* F4)
    (Y : HMod 1 K) : hmodEquiv φ0 Y = toW9 (code ((mat Y).map φ0)) := rfl

theorem congr_hmod_fldAut {K : Type} [Field K] [Finite K] [CharP K 2] (φ0 : K ≃+* F4)
    (φ : K ≃+* K) (h : ∀ x : K, φ0 (φ x) = cj (φ0 x)) :
    congrHom (hmodEquiv φ0) (fldAut φ) = fld9 := by
  have key : ∀ X : HMod 1 K, hmodEquiv φ0 (fldAut φ X) = fld9 (hmodEquiv φ0 X) := by
    intro X
    have hY : ((mat X).map φ).map φ0 = ((mat X).map φ0).map cj := by
      ext i j
      simp [Matrix.map_apply, h]
    have hfld : CFSG.Quasithin.H13.Ch9.Herm9.fld (CFSG.Quasithin.H13.Ch9.Herm9.code
        ((mat X).map φ0)) = CFSG.Quasithin.H13.Ch9.Herm9.code (((mat X).map φ0).map cj) := by
      unfold CFSG.Quasithin.H13.Ch9.Herm9.fld
      rw [CFSG.Quasithin.H13.Ch9.Herm9.herm_code (isHerm_map φ0 X)]
      rfl
    rw [hmodEquiv_apply, hmodEquiv_apply, mat_fldAut, fld9_toW9, hY, hfld]
  refine MulEquiv.ext fun w => ?_
  have := key ((hmodEquiv φ0).symm w)
  rw [MulEquiv.apply_symm_apply] at this
  exact this

theorem exists_phi0 (K : Type) [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    Nonempty (K ≃+* F4) := by
  have : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = Fintype.card F4 := by
    rw [← Nat.card_eq_fintype_card, hK, F4.card]
    norm_num
  exact ⟨FiniteField.ringEquivOfCardEq hc⟩

noncomputable def gl3map {A B : Type} [Field A] [Field B] (f : A ≃+* B) :
    GL (Fin 3) A →* GL (Fin 3) B :=
  Units.map ((f.toRingHom.mapMatrix : Matrix (Fin 3) (Fin 3) A →+* Matrix (Fin 3) (Fin 3) B) :
    Matrix (Fin 3) (Fin 3) A →* Matrix (Fin 3) (Fin 3) B)

theorem coe_gl3map {A B : Type} [Field A] [Field B] (f : A ≃+* B) (g : GL (Fin 3) A) :
    ((gl3map f g : GL (Fin 3) B) : Matrix (Fin 3) (Fin 3) B) =
      (g : Matrix (Fin 3) (Fin 3) A).map f := by
  ext i j
  simp [gl3map, RingHom.mapMatrix_apply]

theorem pointwise_of_ne_one {K : Type} [Field K] [Finite K] (φ0 : K ≃+* F4) (φ : K ≃+* K)
    (hφ : φ ≠ 1) : ∀ x : K, φ0 (φ x) = cj (φ0 x) := by
  let ψ : F4 ≃+* F4 := φ0.symm.trans (φ.trans φ0)
  rcases ringEquiv_eq_refl_or_cj ψ with h | h
  · exfalso
    apply hφ
    ext x
    have hx := congrArg (fun σ : F4 ≃+* F4 => σ (φ0 x)) h
    simp only [ψ, RingEquiv.trans_apply, RingEquiv.symm_apply_apply, RingEquiv.refl_apply] at hx
    simpa using φ0.injective hx
  · intro x
    have hx := congrArg (fun σ : F4 ≃+* F4 => σ (φ0 x)) h
    simp only [ψ, RingEquiv.trans_apply, RingEquiv.symm_apply_apply] at hx
    exact hx

theorem congr_trans_apply {V W X : Type} [CommGroup V] [CommGroup W] [CommGroup X]
    (e : V ≃* W) (f : W ≃* X) (g : MulAut V) :
    MulAut.congr (e.trans f) g = MulAut.congr f (MulAut.congr e g) := by
  ext v
  simp [MulAut.congr_apply]

theorem cj_mk_ne : cj (mk 0 1) ≠ mk 0 1 := by
  intro h
  have := congrArg (fun x : F4 => x.code.val) h
  exact absurd this (by decide)

end CFSG.Quasithin.H47W
