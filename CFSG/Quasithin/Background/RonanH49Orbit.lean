module

public import CFSG.Quasithin.Background.RonanH49Base
public import CFSG.Quasithin.Background.HL3WrOff

public section

namespace CFSG.Quasithin.RonanH49

open CFSG.Quasithin CFSG.Quasithin.H.L3Wr
open scoped Matrix

theorem orb_det_mat_ne_zero (g : ↥SL32) : (mat g).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp g.1.isUnit).ne_zero

theorem orb_mem_img {g : MulAut WMod} : g ∈ img ↔ ∃ γ, rho γ = g :=
  MonoidHom.mem_range

theorem orb_toAdd_eW (i j : Fin 3) : Multiplicative.toAdd (eW i j) = Matrix.single i j 1 := rfl

theorem orb_toAdd_yW : Multiplicative.toAdd yW = Matrix.single 0 1 1 + Matrix.single 1 0 1 := rfl

theorem orb_toAdd_dWd : Multiplicative.toAdd dWd = 1 := by
  show (Matrix.single 0 0 1 + Matrix.single 1 1 1 + Matrix.single 2 2 1 :
    Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1
  decide +kernel

@[expose] def orbKerCard (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) : ℕ :=
  (Finset.univ.filter fun v : Fin 3 → ZMod 2 => X *ᵥ v = 0).card

theorem orb_mulVec_eq_zero_iff {a : Matrix (Fin 3) (Fin 3) (ZMod 2)} (ha : a.det ≠ 0)
    {w : Fin 3 → ZMod 2} : a *ᵥ w = 0 ↔ w = 0 := by
  have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
  constructor
  · intro h
    have h2 := congrArg (fun u => a⁻¹ *ᵥ u) h
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul a hu] using h2
  · rintro rfl
    exact Matrix.mulVec_zero a

theorem orb_kerCard_mul_mul {a b : Matrix (Fin 3) (Fin 3) (ZMod 2)} (ha : a.det ≠ 0)
    (hb : b.det ≠ 0) (X : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    orbKerCard (a * X * bᵀ) = orbKerCard X := by
  have hbT : bᵀ.det ≠ 0 := by rwa [Matrix.det_transpose]
  have hu : IsUnit bᵀ.det := isUnit_iff_ne_zero.mpr hbT
  have hinv1 : ∀ w : Fin 3 → ZMod 2, bᵀ *ᵥ ((bᵀ)⁻¹ *ᵥ w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv bᵀ hu, Matrix.one_mulVec]
  have hinv2 : ∀ v : Fin 3 → ZMod 2, (bᵀ)⁻¹ *ᵥ (bᵀ *ᵥ v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul bᵀ hu, Matrix.one_mulVec]
  have key : ∀ v : Fin 3 → ZMod 2, (a * X * bᵀ) *ᵥ v = a *ᵥ (X *ᵥ (bᵀ *ᵥ v)) := fun v => by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  unfold orbKerCard
  apply Finset.card_nbij' (fun v => bᵀ *ᵥ v) (fun w => (bᵀ)⁻¹ *ᵥ w)
  · intro v hv
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    rw [key, orb_mulVec_eq_zero_iff ha] at hv
    exact hv
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [key, hinv1, hw, Matrix.mulVec_zero]
  · intro v _
    exact hinv2 v
  · intro w _
    exact hinv1 w

theorem orb_kerCard_E00 : orbKerCard (Matrix.single 0 0 1) = 4 := by decide +kernel

theorem orb_kerCard_yX : orbKerCard (Matrix.single 0 1 1 + Matrix.single 1 0 1) = 2 := by
  decide +kernel

theorem orb_kerCard_one : orbKerCard 1 = 1 := by decide +kernel

@[expose] def orbPerm : List (Matrix (Fin 3) (Fin 3) (ZMod 2)) :=
  [!![1, 0, 0; 0, 1, 0; 0, 0, 1], !![0, 1, 0; 1, 0, 0; 0, 0, 1], !![0, 0, 1; 0, 1, 0; 1, 0, 0],
    !![1, 0, 0; 0, 0, 1; 0, 1, 0], !![0, 0, 1; 1, 0, 0; 0, 1, 0], !![0, 1, 0; 0, 0, 1; 1, 0, 0]]

theorem orb_perm_det : ∀ p ∈ orbPerm, p.det ≠ 0 := by decide +kernel

theorem orb_diag_normal_form : ∀ D : Fin 3 → ZMod 2, D ≠ 0 →
    (∃ p ∈ orbPerm, ∃ q ∈ orbPerm, Matrix.diagonal D = p * Matrix.single 0 0 1 * qᵀ) ∨
    (∃ p ∈ orbPerm, ∃ q ∈ orbPerm,
      Matrix.diagonal D = p * (Matrix.single 0 1 1 + Matrix.single 1 0 1) * qᵀ) ∨
    (∃ p ∈ orbPerm, ∃ q ∈ orbPerm, Matrix.diagonal D = p * 1 * qᵀ) := by
  decide +kernel

theorem orb_mat_of_normal {X P Q p q N : Matrix (Fin 3) (Fin 3) (ZMod 2)} {D : Fin 3 → ZMod 2}
    (hX : X = P * Matrix.diagonal D * Q) (h : Matrix.diagonal D = p * N * qᵀ) :
    X = P * p * N * (Qᵀ * q)ᵀ := by
  simp only [hX, h, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

theorem orb_exists_img_of_eq {w v : WMod} {a b : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (ha : a.det ≠ 0) (hb : b.det ≠ 0)
    (h : Multiplicative.toAdd v = a * Multiplicative.toAdd w * bᵀ) :
    ∃ g ∈ img, g w = v := by
  refine ⟨rho (slOfMat a ha, slOfMat b hb), rho_mem_img _, ?_⟩
  apply Multiplicative.toAdd.injective
  simp only [toAdd_rho, mat_slOfMat]
  exact h.symm

theorem orb_cover_of_normal {v : WMod} {P Q : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    {D : Fin 3 → ZMod 2} (hX : Multiplicative.toAdd v = P * Matrix.diagonal D * Q)
    (hP : P.det = 1) (hQ : Q.det = 1) (hD : D ≠ 0) :
    (∃ g ∈ img, g (eW 0 0) = v) ∨ (∃ g ∈ img, g yW = v) ∨ (∃ g ∈ img, g dWd = v) := by
  have hPp : ∀ p ∈ orbPerm, (P * p).det ≠ 0 := fun p hp => by
    rw [Matrix.det_mul, hP, one_mul]
    exact orb_perm_det p hp
  have hQq : ∀ q ∈ orbPerm, (Qᵀ * q).det ≠ 0 := fun q hq => by
    rw [Matrix.det_mul, Matrix.det_transpose, hQ, one_mul]
    exact orb_perm_det q hq
  rcases orb_diag_normal_form D hD with
    ⟨p, hp, q, hq, h⟩ | ⟨p, hp, q, hq, h⟩ | ⟨p, hp, q, hq, h⟩
  · exact Or.inl (orb_exists_img_of_eq (hPp p hp) (hQq q hq)
      (by rw [orb_toAdd_eW]; exact orb_mat_of_normal hX h))
  · exact Or.inr (Or.inl (orb_exists_img_of_eq (hPp p hp) (hQq q hq)
      (by rw [orb_toAdd_yW]; exact orb_mat_of_normal hX h)))
  · exact Or.inr (Or.inr (orb_exists_img_of_eq (hPp p hp) (hQq q hq)
      (by rw [orb_toAdd_dWd]; exact orb_mat_of_normal hX h)))

theorem orbit_cover (v : WMod) (hv : v ≠ 1) :
    (∃ g ∈ img, g (eW 0 0) = v) ∨ (∃ g ∈ img, g yW = v) ∨ (∃ g ∈ img, g dWd = v) := by
  obtain ⟨L, L', D, hX⟩ :=
    Matrix.Pivot.exists_list_transvec_mul_diagonal_mul_list_transvec (Multiplicative.toAdd v)
  by_cases hD : D = 0
  · exfalso
    apply hv
    apply Multiplicative.toAdd.injective
    rw [hX, hD]
    simp [toAdd_one]
  · exact orb_cover_of_normal hX (Matrix.TransvectionStruct.det_toMatrix_prod L)
      (Matrix.TransvectionStruct.det_toMatrix_prod L') hD

theorem not_orbit_x_y : ¬ ∃ g ∈ img, g (eW 0 0) = yW := by
  rintro ⟨g, hg, h⟩
  obtain ⟨γ, rfl⟩ := orb_mem_img.mp hg
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_rho, orb_toAdd_eW, orb_toAdd_yW] at h'
  have hk := orb_kerCard_mul_mul (orb_det_mat_ne_zero γ.1) (orb_det_mat_ne_zero γ.2)
    (Matrix.single 0 0 1)
  rw [h', orb_kerCard_yX, orb_kerCard_E00] at hk
  omega

theorem not_orbit_x_d : ¬ ∃ g ∈ img, g (eW 0 0) = dWd := by
  rintro ⟨g, hg, h⟩
  obtain ⟨γ, rfl⟩ := orb_mem_img.mp hg
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_rho, orb_toAdd_eW, orb_toAdd_dWd] at h'
  have hk := orb_kerCard_mul_mul (orb_det_mat_ne_zero γ.1) (orb_det_mat_ne_zero γ.2)
    (Matrix.single 0 0 1)
  rw [h', orb_kerCard_one, orb_kerCard_E00] at hk
  omega

theorem not_orbit_y_d : ¬ ∃ g ∈ img, g yW = dWd := by
  rintro ⟨g, hg, h⟩
  obtain ⟨γ, rfl⟩ := orb_mem_img.mp hg
  have h' := congrArg Multiplicative.toAdd h
  rw [toAdd_rho, orb_toAdd_yW, orb_toAdd_dWd] at h'
  have hk := orb_kerCard_mul_mul (orb_det_mat_ne_zero γ.1) (orb_det_mat_ne_zero γ.2)
    (Matrix.single 0 1 1 + Matrix.single 1 0 1)
  rw [h', orb_kerCard_one, orb_kerCard_yX] at hk
  omega

end CFSG.Quasithin.RonanH49
