module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3L3MultA
public import CFSG.Quasithin.Background.FFC4Zmod

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup Matrix

variable {W : Type} [CommGroup W] [Finite W]

private noncomputable def f4g_restrict {K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R) (h : ↥K') : ↥R →* ↥R where
  toFun r := ⟨(h : MulAut W) (r : W), hK'R h h.2 r r.2⟩
  map_one' := by ext; simp
  map_mul' := by intro a b; ext; simp

private noncomputable def f4g_g {K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) (h : ↥K') :
    Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) →*
      Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  ψ.toMonoidHom.comp ((f4g_restrict hK'R h).comp ψ.symm.toMonoidHom)

private noncomputable def f4g_Tmat {K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) (h : ↥K')
    (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2) :=
  Multiplicative.toAdd (f4g_g hK'R ψ h (Multiplicative.ofAdd X))

private noncomputable def f4g_T {K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) (h : ↥K') :
    Matrix (Fin 3) (Fin 3) (ZMod 2) →+ Matrix (Fin 3) (Fin 3) (ZMod 2) where
  toFun := f4g_Tmat hK'R ψ h
  map_zero' := by
    simp only [f4g_Tmat, ofAdd_zero, map_one, toAdd_one]
  map_add' := by
    intro X Y
    simp only [f4g_Tmat, ofAdd_add, map_mul, toAdd_mul]

omit [Finite W] in
private theorem f4g_T_left {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (h : ↥K') (A : GL (Fin 3) (ZMod 2)) (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    f4g_T hK'R ψ h ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X) =
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * f4g_T hK'R ψ h X := by
  let l : ↥K := ρ.symm A
  let u : ↥R := ψ.symm (Multiplicative.ofAdd X)
  have hρl : (ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) := by simp [l]
  have hlu : (l : MulAut W) (u : W) ∈ R := hKR l l.2 (u : W) u.2
  have harg : Multiplicative.toAdd (ψ ⟨(u : W), u.2⟩) = X := by
    rw [show (⟨(u : W), u.2⟩ : ↥R) = u from rfl]
    rw [show u = ψ.symm (Multiplicative.ofAdd X) from rfl, MulEquiv.apply_symm_apply,
      toAdd_ofAdd]
  have hψl : ψ ⟨(l : MulAut W) (u : W), hlu⟩ = Multiplicative.ofAdd
      ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X) := by
    rw [hψ l (u : W) u.2 hlu, hρl]
    exact congrArg (fun z => Multiplicative.ofAdd
      ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * z)) harg
  have hsymm : ψ.symm (Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X)) =
      ⟨(l : MulAut W) (u : W), hlu⟩ := by
    rw [← hψl, MulEquiv.symm_apply_apply]
  have hcomm : (h : MulAut W) ((l : MulAut W) (u : W)) =
      (l : MulAut W) ((h : MulAut W) (u : W)) := by
    rw [← MulAut.mul_apply, (hKK' l l.2 h h.2).symm, MulAut.mul_apply]
  have hg : f4g_g hK'R ψ h (Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X)) =
      ψ ⟨(l : MulAut W) ((h : MulAut W) (u : W)),
        hKR l l.2 _ (hK'R h h.2 (u : W) u.2)⟩ := by
    show ψ (f4g_restrict hK'R h (ψ.symm (Multiplicative.ofAdd
      ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X)))) = _
    rw [hsymm]
    exact congrArg ψ (Subtype.ext hcomm)
  have hTu : f4g_T hK'R ψ h X = Multiplicative.toAdd
      (ψ ⟨(h : MulAut W) (u : W), hK'R h h.2 (u : W) u.2⟩) := rfl
  change Multiplicative.toAdd
    (f4g_g hK'R ψ h (Multiplicative.ofAdd ((A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X))) =
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      Multiplicative.toAdd (f4g_g hK'R ψ h (Multiplicative.ofAdd X))
  rw [hg]
  rw [hψ l ((h : MulAut W) (u : W)) (hK'R h h.2 (u : W) u.2)
    (hKR l l.2 _ (hK'R h h.2 (u : W) u.2)), hρl, toAdd_ofAdd]
  rw [← hTu]
  change (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) * f4g_Tmat hK'R ψ h X =
    (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
      Multiplicative.toAdd (f4g_g hK'R ψ h (Multiplicative.ofAdd X))
  rfl

omit [Finite W] in
private theorem f4g_T_mul_apply {K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (h h' : ↥K') (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    f4g_T hK'R ψ (h * h') X = f4g_T hK'R ψ h (f4g_T hK'R ψ h' X) := by
  change Multiplicative.toAdd
    (f4g_g hK'R ψ (h * h') (Multiplicative.ofAdd X)) = Multiplicative.toAdd
    (f4g_g hK'R ψ h (Multiplicative.ofAdd
      (Multiplicative.toAdd (f4g_g hK'R ψ h' (Multiplicative.ofAdd X)))))
  have hgg : f4g_g hK'R ψ (h * h') (Multiplicative.ofAdd X) =
      f4g_g hK'R ψ h (f4g_g hK'R ψ h' (Multiplicative.ofAdd X)) := by
    show ψ (f4g_restrict hK'R (h * h') (ψ.symm (Multiplicative.ofAdd X))) =
      ψ (f4g_restrict hK'R h (ψ.symm (f4g_g hK'R ψ h' (Multiplicative.ofAdd X))))
    have h1 : f4g_restrict hK'R (h * h') (ψ.symm (Multiplicative.ofAdd X)) =
        f4g_restrict hK'R h (f4g_restrict hK'R h' (ψ.symm (Multiplicative.ofAdd X))) := by
      apply Subtype.ext
      simp [f4g_restrict, MulAut.mul_apply]
    have h2 : f4g_g hK'R ψ h' (Multiplicative.ofAdd X) =
        ψ (f4g_restrict hK'R h' (ψ.symm (Multiplicative.ofAdd X))) := rfl
    rw [h1, h2, MulEquiv.symm_apply_apply]
  rw [hgg, ofAdd_toAdd]

omit [Finite W] in
private theorem f4g_T_eq_mul {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (h : ↥K') (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    f4g_T hK'R ψ h X = X * f4g_T hK'R ψ h 1 :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.s16h_e3_mul_eq_right_of_commute_left
    (f4g_T hK'R ψ h)
    (fun A X => f4g_T_left hKK' hKR hK'R ρ ψ hψ h A X) X

omit [Finite W] in
private theorem f4g_T_one_one {K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) :
    f4g_T hK'R ψ (1 : ↥K') 1 = 1 := by
  have h1 : f4g_g hK'R ψ (1 : ↥K') =
      MonoidHom.id (Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
    refine MonoidHom.ext fun Y => ?_
    have hfix : f4g_restrict hK'R (1 : ↥K') (ψ.symm Y) = ψ.symm Y := by
      apply Subtype.ext
      simp [f4g_restrict]
    change ψ (f4g_restrict hK'R (1 : ↥K') (ψ.symm Y)) = Y
    rw [hfix, MulEquiv.apply_symm_apply]
  change Multiplicative.toAdd (f4g_g hK'R ψ (1 : ↥K')
    (Multiplicative.ofAdd (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)))) = 1
  rw [h1, MonoidHom.id_apply, toAdd_ofAdd]

omit [Finite W] in
private theorem f4g_T_one_mul {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (h h' : ↥K') :
    f4g_T hK'R ψ (h * h') 1 = f4g_T hK'R ψ h' 1 * f4g_T hK'R ψ h 1 := by
  rw [f4g_T_mul_apply hK'R ψ h h' 1]
  exact f4g_T_eq_mul hKK' hKR hK'R ρ ψ hψ h (f4g_T hK'R ψ h' 1)

omit [Finite W] in
private theorem f4g_T_one_mul_inv {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (h : ↥K') : f4g_T hK'R ψ h 1 * f4g_T hK'R ψ h⁻¹ 1 = 1 := by
  have hh := f4g_T_one_mul hKK' hKR hK'R ρ ψ hψ h⁻¹ h
  rw [inv_mul_cancel, f4g_T_one_one hK'R ψ] at hh
  exact hh.symm

omit [Finite W] in
private theorem f4g_T_one_inv_mul {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (h : ↥K') : f4g_T hK'R ψ h⁻¹ 1 * f4g_T hK'R ψ h 1 = 1 := by
  have hh := f4g_T_one_mul hKK' hKR hK'R ρ ψ hψ h h⁻¹
  rw [mul_inv_cancel, f4g_T_one_one hK'R ψ] at hh
  exact hh.symm

private noncomputable def f4g_sigmaFun {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (h : ↥K') : GL (Fin 3) (ZMod 2) :=
  Units.mk ((f4g_T hK'R ψ h 1)ᵀ) ((f4g_T hK'R ψ h⁻¹ 1)ᵀ)
    (by rw [← Matrix.transpose_mul, f4g_T_one_inv_mul hKK' hKR hK'R ρ ψ hψ h,
      Matrix.transpose_one])
    (by rw [← Matrix.transpose_mul, f4g_T_one_mul_inv hKK' hKR hK'R ρ ψ hψ h,
      Matrix.transpose_one])

private noncomputable def f4g_sigma {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩))) :
    ↥K' →* GL (Fin 3) (ZMod 2) where
  toFun := f4g_sigmaFun hKK' hKR hK'R ρ ψ hψ
  map_one' := by
    apply Units.ext
    simp only [f4g_sigmaFun, Units.val_mk]
    rw [f4g_T_one_one hK'R ψ, Matrix.transpose_one]
    rfl
  map_mul' := by
    intro h h'
    apply Units.ext
    simp only [f4g_sigmaFun, Units.val_mk, Units.val_mul]
    rw [f4g_T_one_mul hKK' hKR hK'R ρ ψ hψ h h', Matrix.transpose_mul]

omit [Finite W] in
private theorem f4g_sigma_apply {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (h : ↥K') (r : W) (hr : r ∈ R) (hhr : (h : MulAut W) r ∈ R) :
    ψ ⟨(h : MulAut W) r, hhr⟩ = Multiplicative.ofAdd
      (Multiplicative.toAdd (ψ ⟨r, hr⟩) *
        ((f4g_sigmaFun hKK' hKR hK'R ρ ψ hψ h : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ)) := by
  have hT : f4g_T hK'R ψ h (Multiplicative.toAdd (ψ ⟨r, hr⟩)) =
      Multiplicative.toAdd (ψ ⟨(h : MulAut W) r, hhr⟩) := by
    change Multiplicative.toAdd (f4g_g hK'R ψ h
      (Multiplicative.ofAdd (Multiplicative.toAdd (ψ ⟨r, hr⟩)))) = _
    rw [ofAdd_toAdd]
    congr 1
    show ψ (f4g_restrict hK'R h (ψ.symm (ψ ⟨r, hr⟩))) = _
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hB : (f4g_sigmaFun hKK' hKR hK'R ρ ψ hψ h :
      Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = f4g_T hK'R ψ h 1 := by
    simp only [f4g_sigmaFun, Units.val_mk, Matrix.transpose_transpose]
  apply Multiplicative.toAdd.injective
  rw [toAdd_ofAdd, ← hT, f4g_T_eq_mul hKK' hKR hK'R ρ ψ hψ h
    (Multiplicative.toAdd (ψ ⟨r, hr⟩)), ← hB]

omit [Finite W] in
private theorem f4g_fix_of_sigma_one {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (h : ↥K') (hh : f4g_sigma hKK' hKR hK'R ρ ψ hψ h = 1) :
    ∀ r ∈ R, (h : MulAut W) r = r := by
  intro r hr
  have hψr := f4g_sigma_apply hKK' hKR hK'R ρ ψ hψ h r hr (hK'R h h.2 r hr)
  rw [show f4g_sigmaFun hKK' hKR hK'R ρ ψ hψ h = 1 from hh] at hψr
  simp only [Units.val_one, Matrix.transpose_one, mul_one, ofAdd_toAdd] at hψr
  exact congrArg Subtype.val (ψ.injective hψr)

omit [Finite W] in
private theorem f4g_sigma_injective {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (hsimple : IsSimpleGroup ↥K')
    (hnt : ¬ ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r = r) :
    Function.Injective (f4g_sigma hKK' hKR hK'R ρ ψ hψ) := by
  rw [injective_iff_map_eq_one]
  intro h hh
  refine (hsimple.eq_bot_or_eq_top_of_normal (f4g_sigma hKK' hKR hK'R ρ ψ hψ).ker).elim ?_ ?_
  · intro hbot
    have hmem : h ∈ (⊥ : Subgroup ↥K') := by
      rw [← hbot]
      exact MonoidHom.mem_ker.mpr hh
    exact Subgroup.mem_bot.mp hmem
  · intro htop
    exfalso
    apply hnt
    intro k hk r hr
    let k' : ↥K' := ⟨k, hk⟩
    have hk1 : f4g_sigma hKK' hKR hK'R ρ ψ hψ k' = 1 := by
      have hmem : k' ∈ (f4g_sigma hKK' hKR hK'R ρ ψ hψ).ker := by
        rw [htop]
        exact Subgroup.mem_top k'
      exact MonoidHom.mem_ker.mp hmem
    exact f4g_fix_of_sigma_one hKK' hKR hK'R ρ ψ hψ k' hk1 r hr

private theorem f4g_card_GL : Nat.card (GL (Fin 3) (ZMod 2)) = 168 := by
  have hTop : CFSG.Open.StatedSL 3 (ZMod 2) = ⊤ :=
    le_antisymm le_top (fun x _ => CFSG.Quasithin.FFC.mem_statedSL_zmod x)
  let ιe : GL (Fin 3) (ZMod 2) ≃* ↥(CFSG.Open.StatedSL 3 (ZMod 2)) :=
    Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr hTop).symm
  rw [← CFSG.Open.StatedAPI.card_statedSL_three_zmod_two]
  exact Nat.card_congr ιe.toEquiv

omit [Finite W] in
theorem f4g_sigma_of_coords {K K' : Subgroup (MulAut W)} {R : Subgroup W}
    (hKK' : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a)
    (hKR : ∀ k ∈ K, ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (hK'R : ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r ∈ R)
    (ρ : ↥K ≃* GL (Fin 3) (ZMod 2))
    (ψ : ↥R ≃* Multiplicative (Matrix (Fin 3) (Fin 3) (ZMod 2)))
    (hψ : ∀ (l : ↥K) (u : W) (hu : u ∈ R) (hlu : (l : MulAut W) u ∈ R),
      ψ ⟨(l : MulAut W) u, hlu⟩ = Multiplicative.ofAdd
        ((ρ l : Matrix (Fin 3) (Fin 3) (ZMod 2)) * Multiplicative.toAdd (ψ ⟨u, hu⟩)))
    (hsimple : IsSimpleGroup ↥K') (hcard : Nat.card ↥K' = 168)
    (hnt : ¬ ∀ k ∈ K', ∀ r ∈ R, (k : MulAut W) r = r) :
    ∃ σ : ↥K' ≃* GL (Fin 3) (ZMod 2),
      ∀ (h : ↥K') (r : W) (hr : r ∈ R) (hhr : (h : MulAut W) r ∈ R),
        ψ ⟨(h : MulAut W) r, hhr⟩ = Multiplicative.ofAdd
          (Multiplicative.toAdd (ψ ⟨r, hr⟩) *
            ((σ h : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ)) := by
  have hinj : Function.Injective (f4g_sigma hKK' hKR hK'R ρ ψ hψ) :=
    f4g_sigma_injective hKK' hKR hK'R ρ ψ hψ hsimple hnt
  have hbij : Function.Bijective (f4g_sigma hKK' hKR hK'R ρ ψ hψ) :=
    hinj.bijective_of_nat_card_le (by rw [f4g_card_GL, hcard])
  let σe : ↥K' ≃* GL (Fin 3) (ZMod 2) := MulEquiv.ofBijective _ hbij
  exact ⟨σe, fun h r hr hhr => f4g_sigma_apply hKK' hKR hK'R ρ ψ hψ h r hr hhr⟩

end CFSG.LocalAnalysis.WeakClosure81
