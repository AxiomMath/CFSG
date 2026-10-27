module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_7FinL3Torus
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aResidualLin
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.F431.L3.P3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.QuasithinUnique.Fin257
  CFSG.QuasithinUnique.Fin257.L3 CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.LocalAnalysis.ComponentInitial.LinearCover CFSG.QuasithinUnique.Setup.X7a

variable {F : Type} [Field F]

theorem dMat_mul_xMat (t₁ t₂ : Fˣ) (a : F) :
    (dMat t₁ t₂ : Matrix.SpecialLinearGroup (Fin 3) F) * xMat a =
      xMat ((t₁ : F) * (t₂ : F)⁻¹ * a) * dMat t₁ t₂ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dMat]
  change Matrix.diagonal _ * xM a = xM _ * Matrix.diagonal _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [xM, Matrix.mul_apply, Matrix.diagonal_apply]
  field_simp

theorem dMat_mul_yMat (t₁ t₂ : Fˣ) (b : F) :
    (dMat t₁ t₂ : Matrix.SpecialLinearGroup (Fin 3) F) * yMat b =
      yMat ((t₁ : F) * t₂ * t₂ * b) * dMat t₁ t₂ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dMat]
  change Matrix.diagonal _ * yM b = yM _ * Matrix.diagonal _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [yM, Matrix.mul_apply, Matrix.diagonal_apply]
  field_simp

theorem dP_conj_xP [CharP F 2] (t₁ t₂ : Fˣ) (a : F) :
    proj 3 F (dMat t₁ t₂) * xP a * (proj 3 F (dMat t₁ t₂))⁻¹ =
      xP ((t₁ : F) * (t₂ : F)⁻¹ * a) := by
  have h : proj 3 F (dMat t₁ t₂) * xP a =
      xP ((t₁ : F) * (t₂ : F)⁻¹ * a) * proj 3 F (dMat t₁ t₂) := by
    have := congrArg (proj 3 F) (dMat_mul_xMat t₁ t₂ a)
    rwa [map_mul, map_mul] at this
  rw [h]
  group

theorem dP_conj_yP [CharP F 2] (t₁ t₂ : Fˣ) (b : F) :
    proj 3 F (dMat t₁ t₂) * yP b * (proj 3 F (dMat t₁ t₂))⁻¹ =
      yP ((t₁ : F) * t₂ * t₂ * b) := by
  have h : proj 3 F (dMat t₁ t₂) * yP b =
      yP ((t₁ : F) * t₂ * t₂ * b) * proj 3 F (dMat t₁ t₂) := by
    have := congrArg (proj 3 F) (dMat_mul_yMat t₁ t₂ b)
    rwa [map_mul, map_mul] at this
  rw [h]
  group

@[expose] def dHom (F : Type) [Field F] : Fˣ × Fˣ →* projectiveSL 3 F where
  toFun p := proj 3 F (dMat p.1 p.2)
  map_one' := by rw [Prod.fst_one, Prod.snd_one, dMat_one, map_one]
  map_mul' p q := by rw [Prod.fst_mul, Prod.snd_mul, ← map_mul, dMat_mul]

@[expose] def torus3 (F : Type) [Field F] : Subgroup (projectiveSL 3 F) := (dHom F).range

theorem mem_torus3 {g : projectiveSL 3 F} :
    g ∈ torus3 F ↔ ∃ t₁ t₂ : Fˣ, g = proj 3 F (dMat t₁ t₂) := by
  constructor
  · rintro ⟨p, rfl⟩
    exact ⟨p.1, p.2, rfl⟩
  · rintro ⟨t₁, t₂, rfl⟩
    exact ⟨(t₁, t₂), rfl⟩

theorem dP_mem_torus3 (t₁ t₂ : Fˣ) : proj 3 F (dMat t₁ t₂) ∈ torus3 F :=
  mem_torus3.mpr ⟨t₁, t₂, rfl⟩

variable [CharP F 2]

theorem normalizer_U_eq [Finite F] :
    Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) = projUpperTriangular 3 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (sylow_normalizers (K := F) (n := 3) 2 (by norm_num)).2.1

theorem torus3_le_normalizer [Finite F] :
    torus3 F ≤ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F)) := by
  rw [normalizer_U_eq]
  intro g hg
  obtain ⟨t₁, t₂, rfl⟩ := mem_torus3.mp hg
  refine ⟨dMat t₁ t₂, ?_, rfl⟩
  intro i j hij
  exact isDiag_dMat (F := F) t₁ t₂ (ne_of_gt hij)

theorem torus3_odd [Finite F] : Odd (Nat.card (torus3 F)) := by
  have hsurj : Function.Surjective (dHom F).rangeRestrict := (dHom F).rangeRestrict_surjective
  have hdvd : Nat.card (torus3 F) ∣ Nat.card (Fˣ × Fˣ) := Subgroup.card_dvd_of_surjective hsurj
  rw [Nat.card_prod] at hdvd
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units F
  have h2 : 2 ∣ Nat.card F := by
    have := Fintype.ofFinite F
    obtain ⟨n, -, hn⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self 2 (PNat.ne_zero n)
  have hpos : 0 < Nat.card F := Nat.card_pos
  have hodd : Odd (Nat.card Fˣ) := by
    rw [hcard]
    obtain ⟨k, hk⟩ := h2
    exact ⟨k - 1, by omega⟩
  exact (hodd.mul hodd).of_dvd_nat hdvd

theorem exists_sq_eq_field [Finite F] (x : F) : ∃ y : F, y ^ 2 = x := by
  have hinj : Function.Injective (frobenius F 2) := frobenius_inj F 2
  obtain ⟨y, hy⟩ := Finite.injective_iff_surjective.mp hinj x
  exact ⟨y, by simpa [frobenius_def] using hy⟩

omit [CharP F 2] in
theorem U_ext {c a b c' a' b' : F} (h : wP c * xP a * yP b = wP c' * xP a' * yP b') :
    c = c' ∧ a = a' ∧ b = b' := by
  have hU1 : wMat c * xMat a * yMat b ∈ unitriangular 3 F :=
    mul_mem (mul_mem (wMat_mem_unitriangular c) (xMat_mem_unitriangular a))
      (yMat_mem_unitriangular b)
  have hU2 : wMat c' * xMat a' * yMat b' ∈ unitriangular 3 F :=
    mul_mem (mul_mem (wMat_mem_unitriangular c') (xMat_mem_unitriangular a'))
      (yMat_mem_unitriangular b')
  have hh : proj 3 F (wMat c * xMat a * yMat b) = proj 3 F (wMat c' * xMat a' * yMat b') := by
    rw [map_mul, map_mul, map_mul, map_mul]
    exact h
  have h' := LinearFlag.proj_injOn_unitriangular 3 hU1 hU2 hh
  have hm : wM c * xM a * yM b = wM c' * xM a' * yM b' := by
    have := congrArg (fun X : Matrix.SpecialLinearGroup (Fin 3) F =>
      (X : Matrix (Fin 3) (Fin 3) F)) h'
    simp only [Matrix.SpecialLinearGroup.coe_mul] at this
    exact this
  have e01 := congrFun (congrFun hm 0) 1
  have e12 := congrFun (congrFun hm 1) 2
  have e02 := congrFun (congrFun hm 0) 2
  simp [xM, wM, yM, Matrix.mul_apply, Fin.sum_univ_three] at e01 e12 e02
  refine ⟨?_, e01, e12⟩
  rw [e01, e12] at e02
  simpa using e02

theorem dP_conj_nf (t₁ t₂ : Fˣ) (c a b : F) :
    proj 3 F (dMat t₁ t₂) * (wP c * xP a * yP b) * (proj 3 F (dMat t₁ t₂))⁻¹ =
      wP ((t₁ : F) * t₁ * t₂ * c) * xP ((t₁ : F) * (t₂ : F)⁻¹ * a) *
        yP ((t₁ : F) * t₂ * t₂ * b) := by
  rw [← dP_conj_wP t₁ t₂ c, ← dP_conj_xP t₁ t₂ a, ← dP_conj_yP t₁ t₂ b]
  group

theorem torus3_trans [Finite F] {x y : projectiveSL 3 F}
    (hx : x ∈ (Wg : Subgroup (projectiveSL 3 F))) (hy : y ∈ (Wg : Subgroup (projectiveSL 3 F)))
    (hx1 : x ≠ 1) (hy1 : y ≠ 1) : ∃ b ∈ torus3 F, b * x * b⁻¹ = y := by
  obtain ⟨c, rfl⟩ := mem_Wg.mp hx
  obtain ⟨c', rfl⟩ := mem_Wg.mp hy
  have hc : c ≠ 0 := fun h => hx1 (by rw [h, wP_zero])
  have hc' : c' ≠ 0 := fun h => hy1 (by rw [h, wP_zero])
  obtain ⟨r, hr⟩ := exists_sq_eq_field (c' * c⁻¹)
  have hr0 : r ≠ 0 := by
    rintro rfl
    have : c' * c⁻¹ = 0 := by rw [← hr]; ring
    exact mul_ne_zero hc' (inv_ne_zero hc) this
  refine ⟨proj 3 F (dMat (Units.mk0 r hr0) 1), dP_mem_torus3 _ _, ?_⟩
  rw [dP_conj_wP]
  congr 1
  simp only [Units.val_mk0, Units.val_one, mul_one]
  rw [← sq, hr]
  field_simp

omit [CharP F 2] in
theorem exists_unit_ne_one [Finite F] (hq : 2 < Nat.card F) : ∃ ω : Fˣ, ω ≠ 1 := by
  have h : 1 < Nat.card Fˣ := by rw [Nat.card_units F]; omega
  have := Finite.one_lt_card_iff_nontrivial.mp h
  exact exists_ne 1

theorem unit_ne_one_sq {ω : Fˣ} (h : ω ≠ 1) : (ω : F) ^ 2 ≠ 1 := by
  intro h2
  apply h
  have h3 : ((ω : F) - 1) ^ 2 = 0 := by
    linear_combination h2 + (1 - (ω : F)) * (CharP.cast_eq_zero F 2)
  exact Units.ext (sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h3))

theorem torus3_centS [Finite F] (hq : 2 < Nat.card F) {x : projectiveSL 3 F}
    (hx : x ∈ projUnitriangular 3 F) (hc : ∀ b ∈ torus3 F, x * b = b * x) : x = 1 := by
  obtain ⟨c, a, b, rfl⟩ := mem_Ubar.mp hx
  obtain ⟨ω, hω⟩ := exists_unit_ne_one hq
  have hω2 : (ω : F) ^ 2 ≠ 1 := unit_ne_one_sq hω
  have hω1 : (ω : F) ≠ 1 := fun h => hω (Units.ext h)
  have hconj : ∀ t₁ t₂ : Fˣ, proj 3 F (dMat t₁ t₂) * (wP c * xP a * yP b) *
      (proj 3 F (dMat t₁ t₂))⁻¹ = wP c * xP a * yP b := by
    intro t₁ t₂
    have h1 := hc _ (dP_mem_torus3 t₁ t₂)
    calc proj 3 F (dMat t₁ t₂) * (wP c * xP a * yP b) * (proj 3 F (dMat t₁ t₂))⁻¹
        = ((wP c * xP a * yP b) * proj 3 F (dMat t₁ t₂)) * (proj 3 F (dMat t₁ t₂))⁻¹ := by
          rw [← h1]
      _ = wP c * xP a * yP b := by group
  have e1 := hconj ω 1
  have e2 := hconj 1 ω
  rw [dP_conj_nf] at e1 e2
  obtain ⟨hc1, ha1, -⟩ := U_ext e1
  obtain ⟨-, -, hb2⟩ := U_ext e2
  simp only [Units.val_one, inv_one, mul_one, one_mul] at hc1 ha1 hb2
  have hc0 : c = 0 := by
    have : ((ω : F) ^ 2 - 1) * c = 0 := by linear_combination hc1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω2)
  have ha0 : a = 0 := by
    have : ((ω : F) - 1) * a = 0 := by linear_combination ha1
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω1)
  have hb0 : b = 0 := by
    have : ((ω : F) ^ 2 - 1) * b = 0 := by linear_combination hb2
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hω2)
  rw [hc0, ha0, hb0, wP_zero, xP_zero, yP_zero]
  group

omit [CharP F 2] in
theorem dMat_inv (t₁ t₂ : Fˣ) :
    (dMat t₁ t₂ : Matrix.SpecialLinearGroup (Fin 3) F)⁻¹ = dMat t₁⁻¹ t₂⁻¹ := by
  apply inv_eq_of_mul_eq_one_right
  rw [dMat_mul, mul_inv_cancel, mul_inv_cancel, dMat_one]

theorem torus3_mul [Finite F] {h : projectiveSL 3 F}
    (hh : h ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F))) :
    ∃ u ∈ projUnitriangular 3 F, ∃ b ∈ torus3 F, h = u * b := by
  rw [normalizer_U_eq] at hh
  obtain ⟨A, hA, rfl⟩ := hh
  have hA' : (A : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun _ _ h => hA _ _ h
  have h0 := diag_ne_zero_of_upperTriangular hA 0
  have h1 := diag_ne_zero_of_upperTriangular hA 1
  have h2 := diag_ne_zero_of_upperTriangular hA 2
  have hdet : (A : Matrix (Fin 3) (Fin 3) F) 0 0 * (A : Matrix (Fin 3) (Fin 3) F) 1 1 *
      (A : Matrix (Fin 3) (Fin 3) F) 2 2 = 1 := by
    have := A.2
    rw [Matrix.det_of_isUpperTriangular hA'] at this
    simpa [Fin.prod_univ_three] using this
  set t₁ : Fˣ := Units.mk0 _ h0 with ht₁
  set t₂ : Fˣ := Units.mk0 _ h1 with ht₂
  have hU : A * (dMat t₁ t₂)⁻¹ ∈ unitriangular 3 F := by
    rw [dMat_inv]
    have hmat : ((A * dMat t₁⁻¹ t₂⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) *
        Matrix.diagonal ![((t₁⁻¹ : Fˣ) : F), ((t₂⁻¹ : Fˣ) : F),
          (((t₁⁻¹ * t₂⁻¹)⁻¹ : Fˣ) : F)] := by
      rw [Matrix.SpecialLinearGroup.coe_mul, coe_dMat]
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hmat, Matrix.mul_diagonal, hA i j hij, zero_mul]
    · rw [hmat, Matrix.mul_diagonal]
      fin_cases i
      · simp [ht₁]
        field_simp
      · simp [ht₂]
        field_simp
      · simp
        have e1 : (t₁ : F) = (A : Matrix (Fin 3) (Fin 3) F) 0 0 := rfl
        have e2 : (t₂ : F) = (A : Matrix (Fin 3) (Fin 3) F) 1 1 := rfl
        rw [e1, e2]
        linear_combination hdet
  refine ⟨proj 3 F (A * (dMat t₁ t₂)⁻¹), ⟨A * (dMat t₁ t₂)⁻¹, hU, rfl⟩,
    proj 3 F (dMat t₁ t₂), dP_mem_torus3 _ _, ?_⟩
  rw [← map_mul]
  congr 1
  group

theorem centralizer_wP_one_le [Finite F] :
    Subgroup.centralizer ({wP (1 : F)} : Set (projectiveSL 3 F)) ≤
      Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) := by
  intro g hg
  rw [normalizer_U_eq]
  obtain ⟨A, rfl⟩ := proj_surjective 3 F g
  have hc : proj 3 F A * wP (1 : F) = wP 1 * proj 3 F A :=
    Subgroup.mem_centralizer_singleton_iff.mp hg
  have hAw := comm_of_proj_comm_of_sq wMat_one_mul_self hc
  obtain ⟨h20, h21, h10, -⟩ := entries_comm_w hAw
  refine ⟨A, ?_, rfl⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

theorem centralizer_wP_le [Finite F] {x : projectiveSL 3 F}
    (hx : x ∈ (Wg : Subgroup (projectiveSL 3 F))) (hx1 : x ≠ 1) :
    Subgroup.centralizer ({x} : Set (projectiveSL 3 F)) ≤
      Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
        Set (projectiveSL 3 F)) := by
  have h1 : wP (1 : F) ∈ (Wg : Subgroup (projectiveSL 3 F)) := mem_Wg.mpr ⟨1, rfl⟩
  have h11 : wP (1 : F) ≠ 1 := fun h => one_ne_zero ((wP_eq_one_iff _).mp h)
  obtain ⟨d, hd, hdx⟩ := torus3_trans h1 hx h11 hx1
  intro g hg
  have hdN := torus3_le_normalizer hd
  have hg' : d⁻¹ * g * d ∈ Subgroup.centralizer ({wP (1 : F)} : Set (projectiveSL 3 F)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hgx : g * x = x * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    rw [← hdx] at hgx
    calc d⁻¹ * g * d * wP 1 = d⁻¹ * (g * (d * wP 1 * d⁻¹)) * d := by group
      _ = d⁻¹ * ((d * wP 1 * d⁻¹) * g) * d := by rw [hgx]
      _ = wP 1 * (d⁻¹ * g * d) := by group
  have := centralizer_wP_one_le hg'
  have h2 := (Subgroup.normalizer _).mul_mem (Subgroup.normalizer _ |>.mul_mem hdN this)
    ((Subgroup.normalizer _).inv_mem hdN)
  simpa [mul_assoc] using h2

theorem s₂₃Mat_mul_dMat (t₁ t₂ : Fˣ) :
    (s₂₃Mat : Matrix.SpecialLinearGroup (Fin 3) F) * dMat t₁ t₂ =
      dMat t₁ (t₁ * t₂)⁻¹ * s₂₃Mat := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dMat]
  change s₂₃M * Matrix.diagonal _ = Matrix.diagonal _ * s₂₃M
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s₂₃M, Matrix.mul_apply, Matrix.diagonal_apply]

theorem s₁₂Mat_mul_dMat (t₁ t₂ : Fˣ) :
    (s₁₂Mat : Matrix.SpecialLinearGroup (Fin 3) F) * dMat t₁ t₂ = dMat t₂ t₁ * s₁₂Mat := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_dMat]
  change s₁₂M * Matrix.diagonal _ = Matrix.diagonal _ * s₁₂M
  ext i j
  fin_cases i <;> fin_cases j <;> simp [s₁₂M, Matrix.mul_apply, Matrix.diagonal_apply]
  exact mul_comm _ _

theorem s₂₃P_conj_torus (t₁ t₂ : Fˣ) :
    s₂₃P * proj 3 F (dMat t₁ t₂) * s₂₃P⁻¹ = proj 3 F (dMat t₁ (t₁ * t₂)⁻¹) := by
  have h := congrArg (proj 3 F) (s₂₃Mat_mul_dMat (F := F) t₁ t₂)
  rw [map_mul, map_mul] at h
  have h' : s₂₃P * proj 3 F (dMat t₁ t₂) = proj 3 F (dMat t₁ (t₁ * t₂)⁻¹) * s₂₃P := h
  rw [h']
  group

theorem s₁₂P_conj_torus (t₁ t₂ : Fˣ) :
    s₁₂P * proj 3 F (dMat t₁ t₂) * s₁₂P⁻¹ = proj 3 F (dMat t₂ t₁) := by
  have h := congrArg (proj 3 F) (s₁₂Mat_mul_dMat (F := F) t₁ t₂)
  rw [map_mul, map_mul] at h
  have h' : s₁₂P * proj 3 F (dMat t₁ t₂) = proj 3 F (dMat t₂ t₁) * s₁₂P := h
  rw [h']
  group

theorem s₂₃_mul_s₁₂_cube : (s₂₃P * s₁₂P : projectiveSL 3 F) ^ 3 = 1 := by
  have : ((s₂₃Mat : Matrix.SpecialLinearGroup (Fin 3) F) * s₁₂Mat) ^ 3 = 1 := by
    apply Subtype.ext
    rw [pow_three']
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    change ((s₂₃M : Matrix (Fin 3) (Fin 3) F) * s₁₂M) * (s₂₃M * s₁₂M) * (s₂₃M * s₁₂M) = 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [s₂₃M, s₁₂M, Matrix.mul_apply, Fin.sum_univ_three]
  have h := congrArg (proj 3 F) this
  rwa [map_pow, map_mul, map_one] at h

end CFSG.Quasithin.H13.F431.L3.P3
