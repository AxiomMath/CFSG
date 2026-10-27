module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresDefs
public import Mathlib.LinearAlgebra.GeneralLinearGroup.AlgEquiv
public import Mathlib.LinearAlgebra.Matrix.ToLin

public section

namespace CFSG.StandardType

namespace LayerCores

open Matrix

variable {D : Type} [Field D] {d : ℕ} {T : Matrix (Fin d) (Fin d) D → Matrix (Fin d) (Fin d) D}

theorem IsInvol.scalar_central (hT : IsInvol T) (c : D) (x : Matrix (Fin d) (Fin d) D) :
    x * T (Matrix.scalar (Fin d) c) = T (Matrix.scalar (Fin d) c) * x := by
  obtain ⟨y, rfl⟩ := hT.surjective x
  have h := (Matrix.scalar_commute c (fun r' => Commute.all c r') y).eq
  rw [← hT.map_mul, ← hT.map_mul, h]

theorem IsInvol.exists_scalar (hT : IsInvol T) (c : D) :
    ∃ c' : D, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) c' := by
  have h : T (Matrix.scalar (Fin d) c) ∈ Set.center (Matrix (Fin d) (Fin d) D) := by
    rw [Semigroup.mem_center_iff]
    exact fun x => hT.scalar_central c x
  rw [Matrix.center_eq_range] at h
  obtain ⟨c', hc'⟩ := h
  exact ⟨c', hc'.symm⟩

theorem scalar_injective [NeZero d] : Function.Injective (Matrix.scalar (Fin d) : D → _) := by
  intro a b h
  have := congrFun (congrFun h 0) 0
  simpa using this

theorem IsInvol.exists_rho (hT : IsInvol T) :
    ∃ ρ : D →+* D, (∀ c, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) (ρ c)) ∧
      ∀ c, ρ (ρ c) = c := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    exact ⟨RingHom.id D, fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
  have : NeZero d := ⟨hd.ne'⟩
  choose g hg using hT.exists_scalar
  have hinj := scalar_injective (D := D) (d := d)
  have h1 : g 1 = 1 := hinj (by
    rw [← hg, _root_.map_one]
    exact hT.map_one)
  have hmul : ∀ a b, g (a * b) = g a * g b := fun a b => hinj (by
    rw [← hg, _root_.map_mul, hT.map_mul, hg, hg, ← _root_.map_mul, mul_comm])
  have h0 : g 0 = 0 := hinj (by
    rw [← hg, _root_.map_zero]
    exact hT.map_zero)
  have hadd : ∀ a b, g (a + b) = g a + g b := fun a b => hinj (by
    rw [← hg, _root_.map_add, hT.map_add, hg, hg, _root_.map_add])
  let ρ : D →+* D :=
    { toFun := g
      map_one' := h1
      map_mul' := hmul
      map_zero' := h0
      map_add' := hadd }
  refine ⟨ρ, hg, fun c => hinj ?_⟩
  show Matrix.scalar (Fin d) (g (g c)) = Matrix.scalar (Fin d) c
  rw [← hg, ← hg, hT.invol]

section CT

variable (ρ : D →+* D)

@[expose] def ct (x : Matrix (Fin d) (Fin d) D) : Matrix (Fin d) (Fin d) D :=
  (x.map ρ)ᵀ

theorem ct_mul (x y : Matrix (Fin d) (Fin d) D) : ct ρ (x * y) = ct ρ y * ct ρ x := by
  simp only [ct, Matrix.map_mul, transpose_mul]

theorem ct_add (x y : Matrix (Fin d) (Fin d) D) : ct ρ (x + y) = ct ρ x + ct ρ y := by
  ext i j
  simp [ct, map_add]

theorem ct_one : ct ρ (1 : Matrix (Fin d) (Fin d) D) = 1 := by
  simp only [ct, Matrix.map_one _ (map_zero ρ) (map_one ρ), transpose_one]

theorem ct_smul (c : D) (x : Matrix (Fin d) (Fin d) D) : ct ρ (c • x) = ρ c • ct ρ x := by
  ext i j
  simp [ct, map_mul]

theorem ct_ct (hρ2 : ∀ c, ρ (ρ c) = c) (x : Matrix (Fin d) (Fin d) D) : ct ρ (ct ρ x) = x := by
  ext i j
  simp [ct, hρ2]

theorem ct_scalar (c : D) : ct ρ (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) (ρ c) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [ct]
  · simp [ct, Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij,
      Matrix.diagonal_apply_ne _ (Ne.symm hij)]

end CT


section Gram

variable (ρ : D →+* D)

theorem IsInvol.map_smul_of_rho (hT : IsInvol T)
    (hρ : ∀ c, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) (ρ c)) (c : D)
    (x : Matrix (Fin d) (Fin d) D) : T (c • x) = ρ c • T x := by
  rw [show c • x = Matrix.scalar (Fin d) c * x by rw [Matrix.scalar_apply, smul_eq_diagonal_mul],
    hT.map_mul, hρ, Matrix.scalar_apply, smul_eq_mul_diagonal]

@[expose] noncomputable def phiOf (hT : IsInvol T)
    (hρ : ∀ c, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) (ρ c))
    (hρ2 : ∀ c, ρ (ρ c) = c) : Matrix (Fin d) (Fin d) D ≃ₐ[D] Matrix (Fin d) (Fin d) D where
  toFun x := ct ρ (T x)
  invFun y := T (ct ρ y)
  left_inv x := by
    show T (ct ρ (ct ρ (T x))) = x
    rw [ct_ct ρ hρ2, hT.invol]
  right_inv y := by
    show ct ρ (T (T (ct ρ y))) = y
    rw [hT.invol, ct_ct ρ hρ2]
  map_mul' x y := by
    show ct ρ (T (x * y)) = ct ρ (T x) * ct ρ (T y)
    rw [hT.map_mul, ct_mul]
  map_add' x y := by
    show ct ρ (T (x + y)) = ct ρ (T x) + ct ρ (T y)
    rw [hT.map_add, ct_add]
  commutes' c := by
    show ct ρ (T (algebraMap D (Matrix (Fin d) (Fin d) D) c)) =
      algebraMap D (Matrix (Fin d) (Fin d) D) c
    have hc : algebraMap D (Matrix (Fin d) (Fin d) D) c = Matrix.scalar (Fin d) c := by
      rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]
    rw [hc, hρ, ct_scalar, hρ2]

theorem phiOf_apply (hT : IsInvol T)
    (hρ : ∀ c, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) (ρ c))
    (hρ2 : ∀ c, ρ (ρ c) = c) (x : Matrix (Fin d) (Fin d) D) :
    phiOf ρ hT hρ hρ2 x = ct ρ (T x) :=
  rfl

theorem exists_conj_phiOf (hT : IsInvol T)
    (hρ : ∀ c, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) (ρ c))
    (hρ2 : ∀ c, ρ (ρ c) = c) :
    ∃ P : GL (Fin d) D, ∀ x, ct ρ (T x) =
      (P : Matrix (Fin d) (Fin d) D) * x * ((P⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) := by
  let f : Module.End D (Fin d → D) ≃ₐ[D] Module.End D (Fin d → D) :=
    (Matrix.toLinAlgEquiv'.symm.trans (phiOf ρ hT hρ hρ2)).trans Matrix.toLinAlgEquiv'
  obtain ⟨L, hL⟩ := f.eq_linearEquivConjAlgEquiv
  have hLL : LinearMap.toMatrix' (L : (Fin d → D) →ₗ[D] (Fin d → D)) *
      LinearMap.toMatrix' (L.symm : (Fin d → D) →ₗ[D] (Fin d → D)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hLL' : LinearMap.toMatrix' (L.symm : (Fin d → D) →ₗ[D] (Fin d → D)) *
      LinearMap.toMatrix' (L : (Fin d → D) →ₗ[D] (Fin d → D)) = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  refine ⟨⟨_, _, hLL, hLL'⟩, fun x => ?_⟩
  have h1 : f (Matrix.toLinAlgEquiv' x) = Matrix.toLinAlgEquiv' (ct ρ (T x)) := by
    show Matrix.toLinAlgEquiv' (phiOf ρ hT hρ hρ2
      (Matrix.toLinAlgEquiv'.symm (Matrix.toLinAlgEquiv' x))) = _
    rw [AlgEquiv.symm_apply_apply, phiOf_apply]
  have h2 : f (Matrix.toLinAlgEquiv' x) = (L : (Fin d → D) →ₗ[D] (Fin d → D)) ∘ₗ
      Matrix.toLinAlgEquiv' x ∘ₗ (L.symm : (Fin d → D) →ₗ[D] (Fin d → D)) := by
    rw [hL]
    rfl
  have h3 := congrArg LinearMap.toMatrix' (h1.symm.trans h2)
  change LinearMap.toMatrix' (Matrix.toLin' (ct ρ (T x))) =
    LinearMap.toMatrix' ((L : (Fin d → D) →ₗ[D] (Fin d → D)) ∘ₗ Matrix.toLin' x ∘ₗ
      (L.symm : (Fin d → D) →ₗ[D] (Fin d → D))) at h3
  rw [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_comp, LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin'] at h3
  rw [h3, Matrix.mul_assoc]
  rfl

theorem IsInvol.exists_gram (hT : IsInvol T)
    (hρ : ∀ c, T (Matrix.scalar (Fin d) c) = Matrix.scalar (Fin d) (ρ c))
    (hρ2 : ∀ c, ρ (ρ c) = c) :
    ∃ H : GL (Fin d) D, ∀ x, T x =
      ((H⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) * (x.map ρ)ᵀ *
        (H : Matrix (Fin d) (Fin d) D) := by
  obtain ⟨P, hP⟩ := exists_conj_phiOf ρ hT hρ hρ2
  have hH1 : ct ρ (P : Matrix (Fin d) (Fin d) D) *
      ct ρ ((P⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) = 1 := by
    rw [← ct_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, ct_one]
  have hH2 : ct ρ ((P⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) *
      ct ρ (P : Matrix (Fin d) (Fin d) D) = 1 := by
    rw [← ct_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, ct_one]
  refine ⟨⟨_, _, hH1, hH2⟩, fun x => ?_⟩
  calc T x = ct ρ (ct ρ (T x)) := (ct_ct ρ hρ2 _).symm
    _ = ct ρ ((P⁻¹ : GL (Fin d) D) : Matrix (Fin d) (Fin d) D) * ct ρ x *
        ct ρ (P : Matrix (Fin d) (Fin d) D) := by
      rw [hP, ct_mul, ct_mul, Matrix.mul_assoc]
    _ = _ := rfl

end Gram

end LayerCores

end CFSG.StandardType
