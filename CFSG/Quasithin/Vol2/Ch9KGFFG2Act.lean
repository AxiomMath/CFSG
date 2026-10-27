module

public import CFSG.Quasithin.Background.SmithB42G2CurZorn

public section

namespace CFSG.Quasithin.H13.Ch9.KGFF.G2M

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 CFSG.Quasithin.B42G2Id Matrix
open CFSG.Timmesfeld.RankTwo (hexRoot)

variable {F : Type} [Field F] [CharP F 2]

abbrev iA : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank := ⟨0, by decide⟩

abbrev iR : Fin CFSG.Blueprint.Chevalley.Tag.G2.rank := ⟨1, by decide⟩

theorem single_iR_eq : (Pi.single iR 1 : Fin 2 → ℤ) = hexRoot 0 := by
  funext k
  fin_cases k <;> decide

theorem single_iA_eq : (Pi.single iA 1 : Fin 2 → ℤ) = hexRoot 5 := by
  funext k
  fin_cases k <;> decide

theorem zPsi_r (c : F) : zPsi (Pi.single iR 1) c = g2X ![c, 0, 0] := by
  rw [single_iR_eq, zPsi_pos]
  rfl

theorem zPsi_negr (c : F) : zPsi (-Pi.single iR 1) c = g2Y ![c, 0, 0] := by
  have h : (-Pi.single iR 1 : Fin 2 → ℤ) = -hexRoot 0 := by
    funext k
    fin_cases k <;> decide
  rw [h, zPsi_neg]
  rfl

theorem zPsi_a (c : F) : zPsi (Pi.single iA 1) c = g2A (tv 1 0 (by decide) c) := by
  rw [single_iA_eq, zPsi_pos]
  rfl

theorem zPsi_nega (c : F) : zPsi (-Pi.single iA 1) c = g2A (tv 0 1 (by decide) c) := by
  have h : (-Pi.single iA 1 : Fin 2 → ℤ) = -hexRoot 5 := by
    funext k
    fin_cases k <;> decide
  rw [h, zPsi_neg]
  rfl

theorem zPsi_u (c : F) : zPsi (hexRoot 4) c = g2X ![0, c, 0] := by
  rw [zPsi_pos]
  rfl

theorem zPsi_v (c : F) : zPsi (hexRoot 2) c = g2Y ![0, 0, c] := by
  rw [zPsi_pos]
  rfl

@[expose] noncomputable def dA (t : Fˣ) : SL3 F :=
  diag3 ((t⁻¹ : Fˣ) : F) (t : F) 1 (by simp)

@[expose] noncomputable def dR (t : Fˣ) : SL3 F :=
  diag3 ((t : F) * t) ((t⁻¹ : Fˣ) : F) ((t⁻¹ : Fˣ) : F) (by
    rw [Units.val_inv_eq_inv_val]
    field_simp)

omit [CharP F 2] in
theorem dA_mat : ∀ t : Fˣ, ((dA t : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![((t⁻¹ : Fˣ) : F), 0, 0; 0, (t : F), 0; 0, 0, 1] := by
  intro t
  ext i j
  fin_cases i <;> fin_cases j <;> rfl


@[expose] noncomputable def dH (ω : Fˣ) : SL3 F :=
  diag3 1 (ω : F) ((ω⁻¹ : Fˣ) : F) (by simp)

theorem g2X_e0 (c : F) : g2X ![c, 0, 0] = g2X (c • ![1, 0, 0]) := by
  congr 1
  funext k
  fin_cases k <;> simp

theorem g2X_e1 (c : F) : g2X ![0, c, 0] = g2X (c • ![0, 1, 0]) := by
  congr 1
  funext k
  fin_cases k <;> simp

theorem g2Y_e2 (c : F) : g2Y ![0, 0, c] = g2Y (c • ![0, 0, 1]) := by
  congr 1
  funext k
  fin_cases k <;> simp

theorem comm_dA_r (t : Fˣ) (c : F) :
    g2A (dA t) * g2X ![c, 0, 0] * (g2A (dA t))⁻¹ * (g2X ![c, 0, 0])⁻¹ =
      g2X ![((t⁻¹ : Fˣ) : F) * c + c, 0, 0] := by
  rw [g2A_mul_g2X, mul_inv_cancel_right, g2X_inv, dA_mat]
  have h : (!![((t⁻¹ : Fˣ) : F), 0, 0; 0, (t : F), 0; 0, 0, 1] *ᵥ ![c, 0, 0] : Fin 3 → F) =
      ![((t⁻¹ : Fˣ) : F) * c, 0, 0] := by
    funext k
    fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
  rw [h, g2X_e0, g2X_e0, g2X_e0, g2X_smul_mul]

theorem comm_dA_u (t : Fˣ) (c : F) :
    g2A (dA t) * g2X ![0, c, 0] * (g2A (dA t))⁻¹ * (g2X ![0, c, 0])⁻¹ =
      g2X ![0, (t : F) * c + c, 0] := by
  rw [g2A_mul_g2X, mul_inv_cancel_right, g2X_inv, dA_mat]
  have h : (!![((t⁻¹ : Fˣ) : F), 0, 0; 0, (t : F), 0; 0, 0, 1] *ᵥ ![0, c, 0] : Fin 3 → F) =
      ![0, (t : F) * c, 0] := by
    funext k
    fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
  rw [h, g2X_e1, g2X_e1, g2X_e1, g2X_smul_mul]

omit [CharP F 2] in
theorem dR_mat (t : Fˣ) : ((dR t : SL3 F) : Matrix (Fin 3) (Fin 3) F) =
    !![(t : F) * t, 0, 0; 0, ((t⁻¹ : Fˣ) : F), 0; 0, 0, ((t⁻¹ : Fˣ) : F)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem comm_dR_u (t : Fˣ) (c : F) :
    g2A (dR t) * g2X ![0, c, 0] * (g2A (dR t))⁻¹ * (g2X ![0, c, 0])⁻¹ =
      g2X ![0, ((t⁻¹ : Fˣ) : F) * c + c, 0] := by
  rw [g2A_mul_g2X, mul_inv_cancel_right, g2X_inv, dR_mat]
  have h : (!![(t : F) * t, 0, 0; 0, ((t⁻¹ : Fˣ) : F), 0; 0, 0, ((t⁻¹ : Fˣ) : F)] *ᵥ
      ![0, c, 0] : Fin 3 → F) = ![0, ((t⁻¹ : Fˣ) : F) * c, 0] := by
    funext k
    fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
  rw [h, g2X_e1, g2X_e1, g2X_e1, g2X_smul_mul]

theorem comm_dR_v (t : Fˣ) (c : F) :
    g2A (dR t) * g2Y ![0, 0, c] * (g2A (dR t))⁻¹ * (g2Y ![0, 0, c])⁻¹ =
      g2Y ![0, 0, (t : F) * c + c] := by
  rw [g2A_mul_g2Y, mul_inv_cancel_right, g2Y_inv, dR_mat]
  have ht : (t : F) * ((t⁻¹ : Fˣ) : F) = 1 := Units.mul_inv t
  have h : (adjugate !![(t : F) * t, 0, 0; 0, ((t⁻¹ : Fˣ) : F), 0; 0, 0, ((t⁻¹ : Fˣ) : F)])ᵀ *ᵥ
      ![0, 0, c] = ![0, 0, (t : F) * c] := by
    rw [adjugate_fin_three]
    funext k
    fin_cases k <;> simp [mulVec, dotProduct, Fin.sum_univ_three]
  rw [h, g2Y_e2, g2Y_e2, g2Y_e2, g2Y_smul_mul]

theorem eq_of_fixed_r_u {w : Ix3 → F} (hr : g2Act (g2X ![1, 0, 0]) w = w)
    (hu : g2Act (g2X ![0, 1, 0]) w = w) : w = q6 0 0 0 0 0 (w (.inr 2)) := by
  rw [q6_eta w] at hr hu
  rw [g2Act_x0q] at hr
  rw [g2Act_x1q] at hu
  obtain ⟨h0, -, -, -, h4, h5⟩ := q6_inj hr
  obtain ⟨-, h1', -, -, -, h5'⟩ := q6_inj hu
  conv_lhs => rw [q6_eta w]
  simp only [one_mul, add_eq_left] at h0 h4 h5 h1' h5'
  rw [h0, h4, h5, h1', h5']

theorem eq_of_fixed_u_v {w : Ix3 → F} (hu : g2Act (g2X ![0, 1, 0]) w = w)
    (hv : g2Act (g2Y ![0, 0, 1]) w = w) : w = q6 0 (w (.inl 1)) 0 0 0 (w (.inr 2)) := by
  rw [q6_eta w] at hu hv
  rw [g2Act_x1q] at hu
  rw [g2Act_y2q] at hv
  obtain ⟨-, h1, -, h3, -, h5⟩ := q6_inj hu
  obtain ⟨-, h1', -, -, -, -⟩ := q6_inj hv
  conv_lhs => rw [q6_eta w]
  simp only [one_mul, add_eq_left] at h1 h3 h5 h1'
  rw [h1, h3, h5, h1']

theorem g2Act_dH (ω : Fˣ) (b f : F) :
    g2Act (g2A (dH ω)) (q6 0 b 0 0 0 f) = q6 0 ((ω : F) * b) 0 0 0 ((ω : F) * f) := by
  rw [dH, g2Act_diag3]
  apply q6_congr <;> simp

section Psi

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.Quasithin.SmithCurtis CFSG.Quasithin.SmithCurtis.Chev CFSG.Quasithin.B42G2Cur

theorem psi_dC_zero
    (ψ : adjointGroup .G2 F →* cayleyGroup F)
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (t : Fˣ) : ψ (dC .G2 F iA t) = g2A (dA t) := by
  rw [psi_dC ψ hψ iA t, zPsi_a, zPsi_nega]
  change g2A _ * g2A _ * g2A _ * g2A sl3P = _
  rw [← map_mul, ← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, tv10_lit, tv01_lit, dA_mat]
  have hsl : ((sl3P : SL3 F) : Matrix (Fin 3) (Fin 3) F) = !![0, 1, 0; 1, 0, 0; 0, 0, 1] := rfl
  rw [hsl]
  have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, h2]

theorem psi_dC_one
    (ψ : adjointGroup .G2 F →* cayleyGroup F)
    (hψ : ∀ γ, IsRoot .G2 γ → ∀ c : F, ψ (xPar (rootOperatorFamily .G2) γ c) = zPsi γ c)
    (t : Fˣ) : ψ (dC .G2 F iR t) = g2A (dR t) := by
  rw [psi_dC ψ hψ iR t, zPsi_r, zPsi_negr]
  change g2X _ * g2Y _ * g2X _ * gW = _
  refine cayley_ext_Q fun w => ?_
  rw [q6_eta w]
  have ht0 : (t : F) ≠ 0 := t.ne_zero
  simp only [gW, g2Act_mul_apply', g2Act_x0q, g2Act_y0q, dR, g2Act_diag3,
    Units.val_inv_eq_inv_val]
  apply q6_congr <;> field_simp <;> ring_nf <;> reduce_mod_char!

end Psi

end CFSG.Quasithin.H13.Ch9.KGFF.G2M
