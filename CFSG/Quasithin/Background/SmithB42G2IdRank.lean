module

public import CFSG.LinearAlgebra.LinearGroups.Generation
public import CFSG.Quasithin.Vol2.Ch11G2Q8Comm

public section

namespace CFSG.Quasithin.B42G2Id

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Vol2.Ch11.G2Q8 Matrix

variable {F : Type} [Field F]

@[expose] def shortFun (A : Matrix (Fin 2) (Fin 2) F) (x : quasithinZorn F) : quasithinZorn F :=
  zmk (A 0 0 * A 1 1 * x.1 + A 0 1 * A 1 1 * x.2.2.1 0 - A 0 0 * A 1 0 * x.2.1 0 -
      A 0 1 * A 1 0 * x.2.2.2)
    (-(A 0 0 * A 0 1 * x.1) - A 0 1 ^ 2 * x.2.2.1 0 + A 0 0 ^ 2 * x.2.1 0 +
      A 0 0 * A 0 1 * x.2.2.2)
    (A 1 0 * x.2.2.1 2 + A 1 1 * x.2.1 1) (A 1 0 * x.2.2.1 1 + A 1 1 * x.2.1 2)
    (A 1 0 * A 1 1 * x.1 + A 1 1 ^ 2 * x.2.2.1 0 - A 1 0 ^ 2 * x.2.1 0 -
      A 1 0 * A 1 1 * x.2.2.2)
    (A 0 0 * x.2.2.1 1 + A 0 1 * x.2.1 2) (A 0 0 * x.2.2.1 2 + A 0 1 * x.2.1 1)
    (-(A 0 1 * A 1 0 * x.1) - A 0 1 * A 1 1 * x.2.2.1 0 + A 0 0 * A 1 0 * x.2.1 0 +
      A 0 0 * A 1 1 * x.2.2.2)

theorem shortFun_zmk (A : Matrix (Fin 2) (Fin 2) F) (r u₀ u₁ u₂ v₀ v₁ v₂ s : F) :
    shortFun A (zmk r u₀ u₁ u₂ v₀ v₁ v₂ s) =
      zmk (A 0 0 * A 1 1 * r + A 0 1 * A 1 1 * v₀ - A 0 0 * A 1 0 * u₀ - A 0 1 * A 1 0 * s)
        (-(A 0 0 * A 0 1 * r) - A 0 1 ^ 2 * v₀ + A 0 0 ^ 2 * u₀ + A 0 0 * A 0 1 * s)
        (A 1 0 * v₂ + A 1 1 * u₁) (A 1 0 * v₁ + A 1 1 * u₂)
        (A 1 0 * A 1 1 * r + A 1 1 ^ 2 * v₀ - A 1 0 ^ 2 * u₀ - A 1 0 * A 1 1 * s)
        (A 0 0 * v₁ + A 0 1 * u₂) (A 0 0 * v₂ + A 0 1 * u₁)
        (-(A 0 1 * A 1 0 * r) - A 0 1 * A 1 1 * v₀ + A 0 0 * A 1 0 * u₀ + A 0 0 * A 1 1 * s) :=
  rfl

theorem shortFun_mul (A B : Matrix (Fin 2) (Fin 2) F) (x : quasithinZorn F) :
    shortFun (A * B) x = shortFun A (shortFun B x) := by
  rw [zorn_eta x, shortFun_zmk, shortFun_zmk, shortFun_zmk]
  simp only [mul_apply, Fin.sum_univ_two]
  apply zmk_congr <;> ring

theorem shortFun_one (x : quasithinZorn F) : shortFun 1 x = x := by
  rw [zorn_eta x, shortFun_zmk]
  apply zmk_congr <;> simp

@[expose] def shortLin (A : Matrix (Fin 2) (Fin 2) F) : quasithinZorn F →ₗ[F] quasithinZorn F where
  toFun := shortFun A
  map_add' x y := by
    rw [zorn_eta x, zorn_eta y, zmk_add, shortFun_zmk, shortFun_zmk, shortFun_zmk, zmk_add]
    apply zmk_congr <;> ring
  map_smul' c x := by
    rw [zorn_eta x, zmk_smul, shortFun_zmk, shortFun_zmk, RingHom.id_apply, zmk_smul]
    apply zmk_congr <;> ring

theorem sl2_mul_inv_coe (A : SpecialLinearGroup (Fin 2) F) :
    (A : Matrix (Fin 2) (Fin 2) F) * ((A⁻¹ : SpecialLinearGroup (Fin 2) F) :
      Matrix (Fin 2) (Fin 2) F) = 1 := by
  change ((A * A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  rw [mul_inv_cancel]

theorem sl2_inv_mul_coe (A : SpecialLinearGroup (Fin 2) F) :
    ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
  change ((A⁻¹ * A : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
    ((1 : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  rw [inv_mul_cancel]

@[expose] def shortEquiv (A : SpecialLinearGroup (Fin 2) F) :
    quasithinZorn F ≃ₗ[F] quasithinZorn F :=
  { shortLin (A : Matrix (Fin 2) (Fin 2) F) with
    invFun := shortFun ((A⁻¹ : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
    left_inv := fun x => by
      change shortFun _ (shortFun _ x) = x
      rw [← shortFun_mul, sl2_inv_mul_coe, shortFun_one]
    right_inv := fun x => by
      change shortFun _ (shortFun _ x) = x
      rw [← shortFun_mul, sl2_mul_inv_coe, shortFun_one] }

@[expose] def shortHomL : SpecialLinearGroup (Fin 2) F →* (quasithinZorn F ≃ₗ[F] quasithinZorn F)
    where
  toFun := shortEquiv
  map_one' := LinearEquiv.ext fun x => shortFun_one x
  map_mul' A B := LinearEquiv.ext fun x => by
    change shortFun ((A * B : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) x =
      shortFun (A : Matrix (Fin 2) (Fin 2) F) (shortFun (B : Matrix (Fin 2) (Fin 2) F) x)
    exact shortFun_mul _ _ x

theorem shortHomL_apply (A : SpecialLinearGroup (Fin 2) F) (x : quasithinZorn F) :
    shortHomL A x = shortFun (A : Matrix (Fin 2) (Fin 2) F) x := rfl

theorem transvection01_eq_sl2Upper (h : (0 : Fin 2) ≠ 1) (c : F) :
    SpecialLinearGroup.transvection h c = CFSG.LieType.Steinberg.sl2Upper c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection, CFSG.LieType.Steinberg.sl2Upper, transvection]

theorem transvection10_eq_sl2Lower (h : (1 : Fin 2) ≠ 0) (c : F) :
    SpecialLinearGroup.transvection h c = CFSG.LieType.Steinberg.sl2Lower c := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.transvection, CFSG.LieType.Steinberg.sl2Lower, transvection]

section Char2

variable [CharP F 2]

theorem shortHomL_sl2Upper (c : F) :
    shortHomL (CFSG.LieType.Steinberg.sl2Upper c) =
      ((g2X ![c, 0, 0] : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) := by
  refine LinearEquiv.ext fun x => ?_
  rw [shortHomL_apply, g2X_apply, zorn_eta x, shortFun_zmk, xaFun_zmk]
  apply zmk_congr <;>
    simp [CFSG.LieType.Steinberg.sl2Upper, CharTwo.neg_eq, CharTwo.sub_eq_add] <;> ring

theorem shortHomL_sl2Lower (c : F) :
    shortHomL (CFSG.LieType.Steinberg.sl2Lower c) =
      ((g2Y ![c, 0, 0] : ↥(cayleyGroup F)) : quasithinZorn F ≃ₗ[F] quasithinZorn F) := by
  refine LinearEquiv.ext fun x => ?_
  rw [shortHomL_apply, g2Y_apply, zorn_eta x, shortFun_zmk, ybFun_zmk]
  apply zmk_congr <;>
    simp [CFSG.LieType.Steinberg.sl2Lower, CharTwo.neg_eq, CharTwo.sub_eq_add] <;> ring

theorem shortHomL_mem (A : SpecialLinearGroup (Fin 2) F) : shortHomL A ∈ cayleyGroup F := by
  have htop : (cayleyGroup F).comap shortHomL = ⊤ := by
    rw [eq_top_iff, ← CFSG.LinearGroups.special_linear_elementary_generation (n := 2) (K := F),
      Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · change shortHomL _ ∈ cayleyGroup F
      rw [transvection01_eq_sl2Upper, shortHomL_sl2Upper]
      exact (g2X ![c, 0, 0]).2
    · change shortHomL _ ∈ cayleyGroup F
      rw [transvection10_eq_sl2Lower, shortHomL_sl2Lower]
      exact (g2Y ![c, 0, 0]).2
    · exact absurd rfl hij
  have : A ∈ (cayleyGroup F).comap shortHomL := by rw [htop]; exact Subgroup.mem_top A
  exact this

@[expose] noncomputable def g2Short : SpecialLinearGroup (Fin 2) F →* ↥(cayleyGroup F) :=
  shortHomL.codRestrict (cayleyGroup F) shortHomL_mem

theorem g2Short_sl2Upper (c : F) :
    g2Short (CFSG.LieType.Steinberg.sl2Upper c) = g2X ![c, 0, 0] :=
  Subtype.ext (shortHomL_sl2Upper c)

theorem g2Short_sl2Lower (c : F) :
    g2Short (CFSG.LieType.Steinberg.sl2Lower c) = g2Y ![c, 0, 0] :=
  Subtype.ext (shortHomL_sl2Lower c)

end Char2

@[expose] def longMat (A : Matrix (Fin 2) (Fin 2) F) : Matrix (Fin 3) (Fin 3) F :=
  !![A 1 1, A 1 0, 0; A 0 1, A 0 0, 0; 0, 0, 1]

theorem det_longMat (A : Matrix (Fin 2) (Fin 2) F) : (longMat A).det = A.det := by
  simp [longMat, det_fin_three, det_fin_two]
  ring

theorem longMat_mul (A B : Matrix (Fin 2) (Fin 2) F) :
    longMat (A * B) = longMat A * longMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longMat, mul_apply, Fin.sum_univ_two, Fin.sum_univ_three] <;> ring

theorem longMat_one : longMat (1 : Matrix (Fin 2) (Fin 2) F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [longMat]

@[expose] def longSL : SpecialLinearGroup (Fin 2) F →* SL3 F where
  toFun A := ⟨longMat (A : Matrix (Fin 2) (Fin 2) F), by rw [det_longMat]; exact A.2⟩
  map_one' := Subtype.ext longMat_one
  map_mul' A B := Subtype.ext (longMat_mul _ _)

theorem longSL_coe (A : SpecialLinearGroup (Fin 2) F) :
    ((longSL A : SL3 F) : Matrix (Fin 3) (Fin 3) F) = longMat (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

@[expose] noncomputable def g2Long : SpecialLinearGroup (Fin 2) F →* ↥(cayleyGroup F) :=
  g2A.comp longSL

theorem g2Long_sl2Upper (c : F) :
    g2Long (CFSG.LieType.Steinberg.sl2Upper c) = g2A (tv 1 0 (by decide) c) := by
  change g2A (longSL _) = _
  congr 1
  apply Subtype.ext
  rw [longSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longMat, CFSG.LieType.Steinberg.sl2Upper, tv, transvection]

theorem g2Long_sl2Lower (c : F) :
    g2Long (CFSG.LieType.Steinberg.sl2Lower c) = g2A (tv 0 1 (by decide) c) := by
  change g2A (longSL _) = _
  congr 1
  apply Subtype.ext
  rw [longSL_coe]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [longMat, CFSG.LieType.Steinberg.sl2Lower, tv, transvection]

end CFSG.Quasithin.B42G2Id
