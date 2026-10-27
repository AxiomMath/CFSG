module

public import CFSG.LocalAnalysis.StandardType.GGHalfFiveCommutant
public import CFSG.LocalAnalysis.StandardType.GGHalfKnownGroups

public section

namespace CFSG.StandardType.GGHalf

open CFSG.LieType.Universal.SpecialLinear Matrix

private theorem one_add_one_f2 : (1 : F2) + 1 = 0 := CharTwo.add_self_eq_zero 1

private theorem Q_mul_self : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F2) * !![1, 1; 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply, one_add_one_f2]

private theorem f2_eq_zero_or_one (z : F2) : z = 0 ∨ z = 1 := by
  have hcard : Nat.card F2 = 2 := by
    have := GaloisField.card 2 1 (by omega)
    simpa using this
  by_cases hz : z = 0
  · exact Or.inl hz
  · obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (0 : F2)).mp hcard
    exact Or.inr ((huniq z hz).trans (huniq 1 one_ne_zero).symm)

private theorem omegaScalar_coe :
    (↑omegaScalar : Matrix (Fin 3) (Fin 3) F4) = Matrix.diagonal (fun _ => f4Omega) := by
  simp only [omegaScalar, Units.coe_map]
  exact Matrix.scalar_apply f4Omega

private theorem diagonal_map_sq (v : Fin 3 → F4) :
    (Matrix.diagonal v).map (fun a => a ^ 2) = Matrix.diagonal (fun i => (v i) ^ 2) := by
  ext i j
  simp [Matrix.map_apply, Matrix.diagonal_apply]

private theorem trace_map_sq (M : Matrix (Fin 3) (Fin 3) F4) :
    Matrix.trace (M.map fun a => a ^ 2) = (Matrix.trace M) ^ 2 := by
  have h : (fun a : F4 => a ^ 2) = ⇑(frobenius F4 2) := by
    funext a; rw [frobenius_def]
  rw [h, ← AddMonoidHom.map_trace (frobenius F4 2) M, frobenius_def]

private noncomputable def phiMat : Matrix (Fin 6) (Fin 6) F2 :=
  resBlocks 3 (Matrix.diagonal fun _ => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F2))

private theorem phiMat_mul_self : phiMat * phiMat = 1 := by
  have hD : (Matrix.diagonal fun _ : Fin 3 => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F2)) *
      (Matrix.diagonal fun _ : Fin 3 => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F2)) = 1 := by
    rw [Matrix.diagonal_mul_diagonal,
      show (fun _ : Fin 3 => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F2) * !![1, 1; 0, 1]) =
        (fun _ => 1) from funext fun _ => Q_mul_self]
    exact Matrix.diagonal_one
  simp only [phiMat]
  rw [← map_mul, hD, map_one]

private theorem phiMat_conj (A : Matrix (Fin 3) (Fin 3) F4) :
    phiMat * resMat 3 A * phiMat = resMat 3 (A.map fun a => a ^ 2) := by
  have hblock : (Matrix.diagonal fun _ : Fin 3 => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F2)) *
      f4Eps.mapMatrix A *
      (Matrix.diagonal fun _ : Fin 3 => (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) F2)) =
      f4Eps.mapMatrix (A.map fun a => a ^ 2) := by
    ext i i'
    rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    simp only [Matrix.map_apply]
    rw [f4Eps_sq]
  simp only [phiMat, resMat, RingHom.comp_apply]
  rw [← map_mul, ← map_mul, hblock]

private theorem det_phiMat : phiMat.det = 1 := by
  have h := congrArg Matrix.det phiMat_mul_self
  rw [Matrix.det_mul, Matrix.det_one] at h
  rcases f2_eq_zero_or_one phiMat.det with h0 | h1
  · rw [h0, zero_mul] at h
    exact (zero_ne_one h).elim
  · exact h1

private noncomputable def phi : SpecialLinearGroup (Fin 6) F2 := ⟨phiMat, det_phiMat⟩

private theorem phi_mul_self : phi * phi = 1 := Subtype.ext phiMat_mul_self

private theorem phi_inv : phi⁻¹ = phi := inv_eq_of_mul_eq_one_right phi_mul_self

private noncomputable def frobGL :
    Matrix.GeneralLinearGroup (Fin 3) F4 →* Matrix.GeneralLinearGroup (Fin 3) F4 :=
  Matrix.GeneralLinearGroup.map (frobenius F4 2)

private theorem coe_frobGL (g : Matrix.GeneralLinearGroup (Fin 3) F4) :
    ((frobGL g : Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      (g : Matrix (Fin 3) (Fin 3) F4).map fun a => a ^ 2 := by
  ext i j
  rw [frobGL, Matrix.GeneralLinearGroup.map_apply, Matrix.map_apply, frobenius_def]

private theorem phi_conj_resGL (g : Matrix.GeneralLinearGroup (Fin 3) F4) :
    phi * resGL 3 g * phi⁻¹ = resGL 3 (frobGL g) := by
  apply Subtype.ext
  rw [phi_inv]
  change (phiMat : Matrix (Fin (3 * 2)) (Fin (3 * 2)) F2) *
      resMat 3 (g : Matrix (Fin 3) (Fin 3) F4) *
      (phiMat : Matrix (Fin (3 * 2)) (Fin (3 * 2)) F2) =
    ((resGL 3 (frobGL g) : SpecialLinearGroup (Fin (3 * 2)) F2) :
      Matrix (Fin (3 * 2)) (Fin (3 * 2)) F2)
  rw [coe_resGL, coe_frobGL]
  exact phiMat_conj _

private theorem zeta5_transpose :
    ((zeta5 : SpecialLinearGroup (Fin 6) F2) : Matrix (Fin 6) (Fin 6) F2).transpose = zeta5 := by
  rw [zeta5_eq, coe_resGL, resMat_transpose, omegaScalar_coe, Matrix.diagonal_transpose]

private theorem graphAut_zeta5 :
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2 zeta5 = zeta5⁻¹ := by
  apply Subtype.ext
  rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_transpose, zeta5_transpose]

private theorem graphAut_resSL (s : SpecialLinearGroup (Fin 3) F4) :
    CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2 (resSL 3 s) =
      resSL 3 (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s) := by
  apply Subtype.ext
  rw [CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix, ← map_inv,
    coe_resSL, coe_resSL, CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut_matrix,
    resMat_transpose]

private theorem frobGL_omegaScalar : frobGL omegaScalar = omegaScalar⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  apply Units.ext
  rw [Units.val_mul, Units.val_one, coe_frobGL]
  rw [omegaScalar_coe, diagonal_map_sq, Matrix.diagonal_mul_diagonal,
    show (fun _ : Fin 3 => f4Omega * f4Omega ^ 2) = (fun _ => 1) from funext fun _ => by
      have : f4Omega * f4Omega ^ 2 = f4Omega ^ 3 := by ring
      rw [this, f4Omega_pow_three]]
  exact Matrix.diagonal_one

private theorem phi_zeta5 : phi * zeta5 * phi⁻¹ = zeta5⁻¹ := by
  rw [zeta5_eq, phi_conj_resGL, frobGL_omegaScalar, map_inv]

private theorem exists_semilinear_form (c : SpecialLinearGroup (Fin 6) F2)
    (hc : c * zeta5 * c⁻¹ = zeta5⁻¹) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 3) F4, c = phi * resGL 3 g := by
  have hc₁ : phi⁻¹ * c ∈ (resGL 3).range := by
    rw [← centralizer_zeta5, Subgroup.mem_centralizer_singleton_iff]
    have hphi : phi⁻¹ * zeta5⁻¹ * phi = zeta5 := by
      rw [← phi_zeta5]; group
    have h : (phi⁻¹ * c) * zeta5 * (phi⁻¹ * c)⁻¹ = zeta5 := by
      calc (phi⁻¹ * c) * zeta5 * (phi⁻¹ * c)⁻¹
          = phi⁻¹ * (c * zeta5 * c⁻¹) * phi := by group
        _ = phi⁻¹ * zeta5⁻¹ * phi := by rw [hc]
        _ = zeta5 := hphi
    have h2 : (phi⁻¹ * c) * zeta5 = zeta5 * (phi⁻¹ * c) := by
      have := congrArg (fun x => x * (phi⁻¹ * c)) h
      simpa [mul_assoc] using this
    exact h2
  obtain ⟨g, hg⟩ := hc₁
  refine ⟨g, ?_⟩
  rw [hg]
  group

private theorem conj_resSL_eq (g : Matrix.GeneralLinearGroup (Fin 3) F4)
    (gs : SpecialLinearGroup (Fin 3) F4) :
    (phi * resGL 3 g) * resSL 3 gs * (phi * resGL 3 g)⁻¹ =
      resGL 3 (frobGL (g * Matrix.SpecialLinearGroup.toGL gs * g⁻¹)) := by
  rw [show resSL 3 gs = resGL 3 (Matrix.SpecialLinearGroup.toGL gs) from rfl,
    _root_.mul_inv_rev]
  rw [show phi * resGL 3 g * resGL 3 (Matrix.SpecialLinearGroup.toGL gs) *
      ((resGL 3 g)⁻¹ * phi⁻¹) =
      phi * (resGL 3 g * resGL 3 (Matrix.SpecialLinearGroup.toGL gs) * (resGL 3 g)⁻¹) * phi⁻¹
      from by group]
  rw [show resGL 3 g * resGL 3 (Matrix.SpecialLinearGroup.toGL gs) * (resGL 3 g)⁻¹ =
      resGL 3 (g * Matrix.SpecialLinearGroup.toGL gs * g⁻¹) from by
        rw [← map_mul, ← map_inv, ← map_mul]]
  exact phi_conj_resGL _

private theorem det_frob_conj (g : Matrix.GeneralLinearGroup (Fin 3) F4)
    (gs : SpecialLinearGroup (Fin 3) F4) :
    ((frobGL (g * Matrix.SpecialLinearGroup.toGL gs * g⁻¹) : Matrix.GeneralLinearGroup (Fin 3) F4) :
      Matrix (Fin 3) (Fin 3) F4).det = 1 := by
  rw [coe_frobGL]
  have hfun : (fun a : F4 => a ^ 2) = ⇑(frobenius F4 2) := by
    funext a; rw [frobenius_def]
  rw [hfun, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hdet : (((g * Matrix.SpecialLinearGroup.toGL gs * g⁻¹ :
      Matrix.GeneralLinearGroup (Fin 3) F4)) : Matrix (Fin 3) (Fin 3) F4).det = 1 := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_units_conj]
    rw [show ((Matrix.SpecialLinearGroup.toGL gs : Matrix.GeneralLinearGroup (Fin 3) F4) :
        Matrix (Fin 3) (Fin 3) F4) = (gs : Matrix (Fin 3) (Fin 3) F4) from rfl,
      Matrix.SpecialLinearGroup.det_coe]
  rw [hdet, map_one]

private noncomputable def tSL (g : Matrix.GeneralLinearGroup (Fin 3) F4)
    (s : SpecialLinearGroup (Fin 3) F4) : SpecialLinearGroup (Fin 3) F4 :=
  ⟨(frobGL (g * Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s) * g⁻¹) :
        Matrix.GeneralLinearGroup (Fin 3) F4),
    det_frob_conj g _⟩

private theorem resSL_tSL (g : Matrix.GeneralLinearGroup (Fin 3) F4)
    (s : SpecialLinearGroup (Fin 3) F4) :
    resSL 3 (tSL g s) = resGL 3 (frobGL (g * Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s) * g⁻¹)) := by
  change resGL 3 (Matrix.SpecialLinearGroup.toGL (tSL g s)) =
    resGL 3 (frobGL (g * Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s) * g⁻¹))
  exact congrArg (resGL 3) (Units.ext rfl)

private theorem trace_tSL (g : Matrix.GeneralLinearGroup (Fin 3) F4)
    (s : SpecialLinearGroup (Fin 3) F4) :
    Matrix.trace (tSL g s : Matrix (Fin 3) (Fin 3) F4) =
      (Matrix.trace ((s⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) ^ 2 := by
  have ht : (tSL g s : Matrix (Fin 3) (Fin 3) F4) =
      (frobGL (g * Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s) * g⁻¹) :
        Matrix (Fin 3) (Fin 3) F4) := rfl
  rw [ht]
  have hfrob : frobGL (g * Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s) * g⁻¹) =
      frobGL g * frobGL (Matrix.SpecialLinearGroup.toGL
        (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s)) *
        (frobGL g)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
  rw [hfrob, Units.val_mul, Units.val_mul]
  rw [Matrix.trace_mul_cycle, Units.inv_mul (frobGL g), one_mul, coe_frobGL]
  rw [show ((Matrix.SpecialLinearGroup.toGL
      (CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s) :
        Matrix.GeneralLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) =
      ((CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 3 F4 s) :
        Matrix (Fin 3) (Fin 3) F4) from rfl]
  rw [trace_map_sq]
  congr 1

theorem graph_case_restrict (α : MulAut (SpecialLinearGroup (Fin 6) F2))
    (c : SpecialLinearGroup (Fin 6) F2)
    (hα : α = MulAut.conj c *
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2)
    (hζ : α zeta5 = zeta5) :
    ∃ α'' : SpecialLinearGroup (Fin 3) F4 →* SpecialLinearGroup (Fin 3) F4,
      (∀ s, α (resSL 3 s) = resSL 3 (α'' s)) ∧
        ∀ s, Matrix.trace (α'' s : Matrix (Fin 3) (Fin 3) F4) =
          (Matrix.trace ((s⁻¹ : SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4)) ^ 2 := by
  subst hα
  have hc : c * zeta5 * c⁻¹ = zeta5⁻¹ := by
    have h1 : c * zeta5⁻¹ * c⁻¹ = zeta5 := by
      simpa only [MulAut.mul_apply, MulAut.conj_apply, graphAut_zeta5] using hζ
    calc c * zeta5 * c⁻¹ = (c * zeta5⁻¹ * c⁻¹)⁻¹ := by group
      _ = zeta5⁻¹ := by rw [h1]
  obtain ⟨g, hg⟩ := exists_semilinear_form c hc
  have key : ∀ s, (MulAut.conj c *
      CFSG.ComponentClassification.CatalogueBGraphForm.slGraphAut 6 F2) (resSL 3 s) =
        resSL 3 (tSL g s) := by
    intro s
    rw [MulAut.mul_apply, MulAut.conj_apply, graphAut_resSL, hg, conj_resSL_eq, resSL_tSL]
  refine ⟨MonoidHom.mk' (tSL g) ?_, key, trace_tSL g⟩
  intro s s'
  apply resSL_injective 3
  rw [map_mul, ← key, ← key, ← key, map_mul, map_mul]

end CFSG.StandardType.GGHalf

end
