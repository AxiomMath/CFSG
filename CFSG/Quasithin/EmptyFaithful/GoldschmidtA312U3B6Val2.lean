module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312U3B6Val1
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGammaL2

public section

namespace CFSG.Quasithin.A312U3

open Matrix CFSG.GorensteinWalter
open scoped MatrixGroups

theorem not_conj_of_field_part {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9)
    (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F) {l : F}
    (hl : l ^ 2 + l - 1 = 0) (γ : PGammaL2 F) (hγ : γ.right ≠ 1) (y : PSL2 F) :
    pGammaL2ToMulAutPSL2 F hK hcard γ (xPSL2 l) ≠ y * xPSL2 l * y⁻¹ := by
  intro h
  have hγ' : γ = SemidirectProduct.inl γ.left * SemidirectProduct.inr γ.right :=
    (SemidirectProduct.inl_left_mul_inr_right γ).symm
  have h1 : pGammaL2ToMulAutPSL2 F hK hcard γ (xPSL2 l) =
      pgl2InnerAutPSL2 F hK hcard γ.left (psl2FieldAut F γ.right (xPSL2 l)) := by
    rw [hγ', map_mul, pGammaL2ToMulAutPSL2_inl, pGammaL2ToMulAutPSL2_inr]
    simp
  rw [h1] at h
  have h2 := congrArg Matrix.ProjectiveSpecialLinearGroup.toPGL h
  rw [toPGL_pgl2InnerAutPSL2_apply, psl2FieldAut_toPGL, map_mul, map_mul, map_inv] at h2
  obtain ⟨A₀, hA₀⟩ := Matrix.ProjGenLinGroup.mk_surjective (n := Fin 2) (R := F) γ.left
  obtain ⟨Y, hY⟩ := QuotientGroup.mk_surjective y
  set X₀ : GL (Fin 2) F := Matrix.SpecialLinearGroup.toGL (xSL2 l) with hX₀
  have hx : Matrix.ProjectiveSpecialLinearGroup.toPGL (xPSL2 l) = Matrix.ProjGenLinGroup.mk X₀ :=
    rfl
  have hy : Matrix.ProjectiveSpecialLinearGroup.toPGL y =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL Y) := by
    rw [← hY]; rfl
  have hσ : (pgl2FieldAut F) γ.right (Matrix.ProjGenLinGroup.mk X₀) =
      Matrix.ProjGenLinGroup.mk (Matrix.GeneralLinearGroup.map γ.right.toRingHom X₀) :=
    pgl2RingEquiv_mk _ _
  rw [hx, hσ, ← hA₀, hy] at h2
  have h3 : Matrix.ProjGenLinGroup.mk
      (A₀ * Matrix.GeneralLinearGroup.map γ.right.toRingHom X₀ * A₀⁻¹) =
      Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL Y * X₀ *
        (Matrix.SpecialLinearGroup.toGL Y)⁻¹) := by
    simpa [map_mul, map_inv] using h2
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp h3
  have hu' := congrArg (fun g : GL (Fin 2) F => (g : Matrix (Fin 2) (Fin 2) F)) hu
  simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at hu'
  have hsc : ∀ c : F, Matrix.scalar (Fin 2) c = c • (1 : Matrix (Fin 2) (Fin 2) F) := fun c => by
    ext i j
    simp [Matrix.one_apply, Matrix.diagonal_apply]
  have hX₀m : ((X₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, l] := rfl
  have hmap0 : ((Matrix.GeneralLinearGroup.map γ.right.toRingHom X₀ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = ((X₀ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map γ.right :=
    rfl
  have hmap : ((Matrix.GeneralLinearGroup.map γ.right.toRingHom X₀ : GL (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = !![0, -1; 1, γ.right l] := by
    rw [hmap0, hX₀m]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hmap, hsc, Matrix.mul_smul, Matrix.mul_one, hX₀m] at hu'
  have hdet := congrArg Matrix.det hu'
  have htr := congrArg Matrix.trace hu'
  rw [Matrix.det_smul, det_conj_gl, det_conj_gl] at hdet
  rw [Matrix.trace_smul, trace_conj_gl, trace_conj_gl] at htr
  simp [Matrix.det_fin_two, Matrix.trace_fin_two] at hdet htr
  apply aut_sq_ne hF hl hγ
  rcases hdet with rfl | rfl
  · simpa using congrArg (· ^ 2) htr
  · have h' : γ.right l = -l := by simpa using (neg_eq_iff_eq_neg.mp (by simpa using htr))
    rw [h']
    ring

theorem exists_inner_of_conj {F : Type} [Field F] [Finite F] (hF : Nat.card F = 9)
    (hK : IsOddPrimePower (Nat.card F)) (hcard : 3 < Nat.card F) {l : F}
    (hl : l ^ 2 + l - 1 = 0) (β : MulAut (PSL2 F)) (y : PSL2 F)
    (hβ : β (xPSL2 l) = y * xPSL2 l * y⁻¹) :
    ∃ A : PGL2 F, pgl2InnerAutPSL2 F hK hcard A = β := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨γ, hγ⟩ := pGammaL2ToMulAutPSL2_surjective F (p := 3) (f := 2) (by rw [hF]; norm_num) hK
    hcard β
  have hr : γ.right = 1 := by
    by_contra hne
    exact not_conj_of_field_part hF hK hcard hl γ hne y (by rw [hγ]; exact hβ)
  obtain ⟨A, hA⟩ : ∃ A : PGL2 F, γ = SemidirectProduct.inl A :=
    ⟨γ.left, calc γ = SemidirectProduct.inl γ.left * SemidirectProduct.inr γ.right :=
          (SemidirectProduct.inl_left_mul_inr_right γ).symm
      _ = SemidirectProduct.inl γ.left := by rw [hr, map_one, mul_one]⟩
  refine ⟨A, ?_⟩
  rw [← hγ, hA, pGammaL2ToMulAutPSL2_inl]

end CFSG.Quasithin.A312U3
