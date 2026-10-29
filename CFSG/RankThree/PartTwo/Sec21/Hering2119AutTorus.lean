module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismGeneration
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDiag

public section

namespace CFSG.RankThree.PartTwo.Sec21.Hering2119

open Matrix CFSG.LocalAnalysis.ComponentInitial LinearFlag

section Arithmetic

variable {F : Type*} [Field F]

theorem eq_one_of_pow_eq_one_of_pow_eq_one {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {c : F}
    (hcp : c ^ p = 1) (hc3 : c ^ 3 = 1) : c = 1 := by
  have h := pow_gcd_eq_one.mpr ⟨hcp, hc3⟩
  have hg : Nat.gcd p 3 = 1 := (Nat.coprime_primes hp Nat.prime_three).mpr hp3
  rwa [hg, pow_one] at h

end Arithmetic

section Matrices

variable {F : Type*} [Field F]

theorem entry_of_intertwine {d d' : Fin 3 → F} {A : Matrix (Fin 3) (Fin 3) F} {c : F}
    (h : A * diagonal d' = c • (diagonal d * A)) {i j : Fin 3} (hij : A i j ≠ 0) :
    d' j = c * d i := by
  have e := congrFun (congrFun h i) j
  rw [Matrix.mul_diagonal, Matrix.smul_apply, Matrix.diagonal_mul, smul_eq_mul] at e
  apply mul_left_cancel₀ hij
  linear_combination e

theorem exists_ne_zero_col {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det ≠ 0) (j : Fin 3) :
    ∃ i, A i j ≠ 0 := by
  by_contra h
  push Not at h
  exact hA (Matrix.det_eq_zero_of_column_eq_zero j h)

theorem eq_diag_of_intertwine {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) {ζ ζ' : F}
    (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) (hζ' : ζ' ^ p = 1) (hζ'1 : ζ' ≠ 1)
    {A : Matrix (Fin 3) (Fin 3) F} (hA : A.det ≠ 0) {c₁ c₂ : F} (hc₁ : c₁ ^ 3 = 1)
    (hc₂ : c₂ ^ 3 = 1)
    (h₁ : A * diagonal ![ζ', ζ'⁻¹, 1] = c₁ • (diagonal ![ζ, ζ⁻¹, 1] * A))
    (h₂ : A * diagonal ![ζ', 1, ζ'⁻¹] = c₂ • (diagonal ![ζ, 1, ζ⁻¹] * A)) :
    ζ' = ζ ∧ ∀ i j, i ≠ j → A i j = 0 := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  have hζ'0 : ζ' ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ'
    exact zero_ne_one hζ'
  have hinvp : (ζ⁻¹) ^ p = 1 := by rw [inv_pow, hζ, inv_one]
  have hinv1 : ζ⁻¹ ≠ 1 := fun h => hζ1 (inv_eq_one.mp h)
  have hinv'1 : ζ'⁻¹ ≠ 1 := fun h => hζ'1 (inv_eq_one.mp h)
  have hS₁p : ∀ i : Fin 3, (![ζ, ζ⁻¹, 1] i) ^ p = 1 := by
    intro i
    fin_cases i <;> simp [hζ, hinvp]
  have hS₂p : ∀ i : Fin 3, (![ζ, 1, ζ⁻¹] i) ^ p = 1 := by
    intro i
    fin_cases i <;> simp [hζ, hinvp]
  obtain ⟨i₀, hi₀⟩ := exists_ne_zero_col hA 0
  have hc₁1 : c₁ = 1 := by
    have e : ζ' = c₁ * ![ζ, ζ⁻¹, 1] i₀ := by simpa using entry_of_intertwine h₁ hi₀
    refine eq_one_of_pow_eq_one_of_pow_eq_one hp hp3 ?_ hc₁
    have h1 : (c₁ * ![ζ, ζ⁻¹, 1] i₀) ^ p = 1 := by rw [← e]; exact hζ'
    rw [mul_pow, hS₁p i₀, mul_one] at h1
    exact h1
  have hc₂1 : c₂ = 1 := by
    have e : ζ' = c₂ * ![ζ, 1, ζ⁻¹] i₀ := by simpa using entry_of_intertwine h₂ hi₀
    refine eq_one_of_pow_eq_one_of_pow_eq_one hp hp3 ?_ hc₂
    have h1 : (c₂ * ![ζ, 1, ζ⁻¹] i₀) ^ p = 1 := by rw [← e]; exact hζ'
    rw [mul_pow, hS₂p i₀, mul_one] at h1
    exact h1
  subst hc₁1
  subst hc₂1
  have key : ∀ i j : Fin 3, A i j ≠ 0 →
      ![ζ', ζ'⁻¹, 1] j = ![ζ, ζ⁻¹, 1] i ∧ ![ζ', 1, ζ'⁻¹] j = ![ζ, 1, ζ⁻¹] i := by
    intro i j hij
    have e1 := entry_of_intertwine h₁ hij
    have e2 := entry_of_intertwine h₂ hij
    rw [one_mul] at e1 e2
    exact ⟨e1, e2⟩
  have hζζ : ζ' = ζ := by
    have k := key i₀ 0 hi₀
    fin_cases i₀
    · simpa using k.1
    · exfalso
      simp at k
      first
        | exact hζ'1 k
        | exact hζ'1 k.1
        | exact hζ'1 k.2
        | exact hζ'1 k.1.symm
        | exact hζ'1 k.2.symm
    · exfalso
      simp at k
      first
        | exact hζ'1 k
        | exact hζ'1 k.1
        | exact hζ'1 k.2
        | exact hζ'1 k.1.symm
        | exact hζ'1 k.2.symm
  refine ⟨hζζ, fun i j hij => ?_⟩
  by_contra hne
  have k := key i j hne
  subst hζζ
  fin_cases i <;> fin_cases j <;> simp at k hij
  all_goals
    first
      | exact hζ'1 k
      | exact hζ'1 k.1
      | exact hζ'1 k.2
      | exact hζ'1 k.1.symm
      | exact hζ'1 k.2.symm

end Matrices




section Model

variable {F : Type} [Field F]

@[expose] def diagSL (a b c : F) (h : a * b * c = 1) : SpecialLinearGroup (Fin 3) F :=
  ⟨diagonal ![a, b, c], by rw [det_diagonal, Fin.prod_univ_three]; simpa using h⟩

@[simp]
theorem coe_diagSL (a b c : F) (h : a * b * c = 1) :
    ((diagSL a b c h : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![a, b, c] :=
  rfl

theorem fieldAut_proj_diagSL (σ : F ≃+* F) (a b c : F) (h : a * b * c = 1)
    (h' : σ a * σ b * σ c = 1) :
    fieldAut 3 F σ (proj 3 F (diagSL a b c h)) = proj 3 F (diagSL (σ a) (σ b) (σ c) h') := by
  rw [fieldAut_proj]
  congr 1
  ext i j
  have := SpecialLinearGroup.map_apply_coe σ.toRingHom (diagSL a b c h)
  rw [this]
  fin_cases i <;> fin_cases j <;> simp [diagSL, diagonal_apply]

theorem prod_erase_diag (a b c : F) (h : a * b * c = 1) (i : Fin 3) :
    ∏ x ∈ Finset.univ.erase i, ![a, b, c] x = (![a, b, c] i)⁻¹ := by
  have h1 := Finset.prod_erase_mul Finset.univ ![a, b, c] (Finset.mem_univ i)
  rw [Fin.prod_univ_three] at h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at h1
  exact eq_inv_of_mul_eq_one_left (h1.trans h)

theorem dualAut_proj_diagSL (a b c : F) (h : a * b * c = 1) (h' : a⁻¹ * b⁻¹ * c⁻¹ = 1) :
    dualAut 3 F (proj 3 F (diagSL a b c h)) = proj 3 F (diagSL a⁻¹ b⁻¹ c⁻¹ h') := by
  rw [dualAut_proj]
  congr 1
  ext i j
  have h1 := Matrix.SpecialLinearGroup.coe_transpose ((diagSL a b c h)⁻¹)
  have h2 := Matrix.SpecialLinearGroup.coe_inv (diagSL a b c h)
  rw [h1, h2]
  simp only [coe_diagSL]
  rw [adjugate_diagonal]
  simp only [prod_erase_diag a b c h]
  fin_cases i <;> fin_cases j <;> simp [diagonal_apply]

@[expose] noncomputable def stdAut (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool) :
    MulAut (projectiveSL 3 F) :=
  conjAut 3 F A * fieldAut 3 F σ * (if ε then dualAut 3 F else 1)

@[expose] def twist (σ : F ≃+* F) (ε : Bool) (x : F) : F := if ε then (σ x)⁻¹ else σ x

theorem twist_mul_mul (σ : F ≃+* F) (ε : Bool) {a b c : F} (h : a * b * c = 1) :
    twist σ ε a * twist σ ε b * twist σ ε c = 1 := by
  cases ε
  · simp only [twist, Bool.false_eq_true, if_false]
    rw [← map_mul, ← map_mul, h, map_one]
  · simp only [twist, if_true]
    rw [← mul_inv, ← mul_inv, ← map_mul, ← map_mul, h, map_one, inv_one]

theorem intertwine_of_fix (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool) (a b c : F)
    (h : a * b * c = 1)
    (hfix : stdAut A σ ε (proj 3 F (diagSL a b c h)) = proj 3 F (diagSL a b c h)) :
    ∃ d : F, d ^ 3 = 1 ∧
      (A : Matrix (Fin 3) (Fin 3) F) *
        diagonal ![twist σ ε a, twist σ ε b, twist σ ε c] =
      d • (diagonal ![a, b, c] * (A : Matrix (Fin 3) (Fin 3) F)) := by
  have h' := twist_mul_mul σ ε h
  have himg : (fieldAut 3 F σ * (if ε then dualAut 3 F else 1)) (proj 3 F (diagSL a b c h)) =
      proj 3 F (diagSL (twist σ ε a) (twist σ ε b) (twist σ ε c) h') := by
    cases ε
    · simp only [twist, Bool.false_eq_true, if_false, MulAut.mul_apply, MulAut.one_apply]
      exact fieldAut_proj_diagSL σ a b c h h'
    · simp only [twist, if_true, MulAut.mul_apply]
      have hinv : a⁻¹ * b⁻¹ * c⁻¹ = 1 := by rw [← mul_inv, ← mul_inv, h, inv_one]
      rw [dualAut_proj_diagSL a b c h hinv]
      have h3 : σ a⁻¹ * σ b⁻¹ * σ c⁻¹ = 1 := by
        rw [map_inv₀, map_inv₀, map_inv₀]
        simpa [twist] using twist_mul_mul σ true h
      rw [fieldAut_proj_diagSL σ a⁻¹ b⁻¹ c⁻¹ hinv h3]
      congr 2 <;> simp [map_inv₀]
  rw [stdAut, mul_assoc, MulAut.mul_apply, himg, conjAut_proj] at hfix
  obtain ⟨u, hu3, hum⟩ := mem_scalars.mp (proj_eq_proj_iff.mp hfix)
  set X := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 F A
    (diagSL (twist σ ε a) (twist σ ε b) (twist σ ε c) h') with hX
  have hXm : (X : Matrix (Fin 3) (Fin 3) F) = (A : Matrix (Fin 3) (Fin 3) F) *
      diagonal ![twist σ ε a, twist σ ε b, twist σ ε c] *
      ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := coe_slConjugation A _
  have hs : (diagonal ![a, b, c] : Matrix (Fin 3) (Fin 3) F) =
      (X : Matrix (Fin 3) (Fin 3) F) * scalar (Fin 3) (u : F) := by
    have h1 : ((X * (X⁻¹ * diagSL a b c h) : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) = diagonal ![a, b, c] := by
      rw [mul_inv_cancel_left]
      rfl
    rw [← h1, Matrix.SpecialLinearGroup.coe_mul, hum]
  have hMi : ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  refine ⟨(u : F)⁻¹, ?_, ?_⟩
  · rw [inv_pow, ← Units.val_pow_eq_pow_val, hu3, Units.val_one, inv_one]
  · have hsc : scalar (Fin 3) (u : F) = (u : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
      rw [Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]
    have e1 : (diagonal ![a, b, c] : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) =
        (u : F) • ((A : Matrix (Fin 3) (Fin 3) F) *
          diagonal ![twist σ ε a, twist σ ε b, twist σ ε c]) := by
      rw [hs, hXm, hsc]
      calc (A : Matrix (Fin 3) (Fin 3) F) * diagonal ![twist σ ε a, twist σ ε b, twist σ ε c] *
            ((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
            ((u : F) • (1 : Matrix (Fin 3) (Fin 3) F)) * (A : Matrix (Fin 3) (Fin 3) F)
          = (u : F) • ((A : Matrix (Fin 3) (Fin 3) F) *
              diagonal ![twist σ ε a, twist σ ε b, twist σ ε c] *
              (((A⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
                (A : Matrix (Fin 3) (Fin 3) F))) := by
            simp [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
        _ = _ := by rw [hMi, Matrix.mul_one]
    rw [e1, smul_smul, inv_mul_cancel₀ hu0, one_smul]


open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)

theorem map_diagUnits (σ : F ≃+* F) (a b c : Fˣ) :
    GeneralLinearGroup.map (σ : F →+* F) (diagUnits a b c) =
      diagUnits (Units.map (σ : F →* F) a) (Units.map (σ : F →* F) b)
        (Units.map (σ : F →* F) c) := by
  apply Units.ext
  rw [coe_diagUnits]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [diagonal_apply, GeneralLinearGroup.map, coe_diagUnits]

theorem inverseTranspose_diagUnits (a b c : Fˣ) :
    GeneralLinearGroup.inverseTranspose (diagUnits a b c) = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
  apply Units.ext
  rw [GeneralLinearGroup.coe_inverseTranspose]
  have h : ((diagUnits a b c : GL (Fin 3) F)⁻¹ : GL (Fin 3) F) = diagUnits a⁻¹ b⁻¹ c⁻¹ := by
    rw [inv_eq_iff_mul_eq_one, diagUnits_mul]
    apply Units.ext
    rw [Units.val_one, coe_diagUnits, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp
  rw [h, coe_diagUnits]
  exact diagonal_transpose _


theorem commute_of_isDiag {A : Matrix (Fin 3) (Fin 3) F} (hA : ∀ i j, i ≠ j → A i j = 0)
    (d : Fin 3 → F) : A * diagonal d = diagonal d * A := by
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hij : i = j
  · subst hij
    ring
  · rw [hA i j hij]
    simp

theorem conj_diag_eq {A : GL (Fin 3) F} (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) F) i j = 0)
    (y : GL (Fin 3) F) (d : Fin 3 → F) (hy : (y : Matrix (Fin 3) (Fin 3) F) = diagonal d) :
    A * y * A⁻¹ = y := by
  have h : A * y = y * A := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, hy]
    exact commute_of_isDiag hA d
  rw [h, mul_assoc, mul_inv_cancel, mul_one]

theorem stdAut_conj (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool) (y : GL (Fin 3) F) :
    stdAut A σ ε * conjAut 3 F y * (stdAut A σ ε)⁻¹ =
      conjAut 3 F (A * (if ε then GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose y) else GeneralLinearGroup.map (σ : F →+* F) y) *
          A⁻¹) := by
  obtain ⟨hcc, -, hfc, hdd, hdc, -, -⟩ := standard_automorphism_transport (n := 3) (K := F)
  have hδinv : (dualAut 3 F)⁻¹ = dualAut 3 F := inv_eq_of_mul_eq_one_right hdd
  cases ε
  · simp only [stdAut, Bool.false_eq_true, if_false, mul_one]
    rw [map_mul, map_mul, map_inv, ← hfc σ y]
    group
  · simp only [stdAut, if_true]
    rw [map_mul, map_mul, map_inv, ← hfc σ, ← hdc y]
    simp only [_root_.mul_inv_rev, hδinv]
    group


theorem exists_exp_of_ringEquiv (σ : F ≃+* F) :
    ∃ m : ℕ, (m = 1 ∨ m = 2) ∧ ∀ u : Fˣ, u ^ 3 = 1 → Units.map (σ : F →* F) u = u ^ m := by
  by_cases h : ∃ ω : Fˣ, ω ^ 3 = 1 ∧ ω ≠ 1
  · obtain ⟨ω, hω3, hω1⟩ := h
    have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
    have hprim : IsPrimitiveRoot ω 3 := hord ▸ IsPrimitiveRoot.orderOf ω
    have hprim0 : IsPrimitiveRoot (ω : F) 3 := IsPrimitiveRoot.coe_units_iff.mpr hprim
    have hσ3 : (σ (ω : F)) ^ 3 = 1 := by rw [← map_pow, ← Units.val_pow_eq_pow_val, hω3]; simp
    have hσ1 : σ (ω : F) ≠ 1 := by
      intro h1
      apply hω1
      apply Units.ext
      apply σ.injective
      rw [h1, Units.val_one, map_one]
    obtain ⟨i, hi, hωi⟩ := hprim0.eq_pow_of_pow_eq_one hσ3
    have hi0 : i ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hωi
      exact hσ1 hωi.symm
    refine ⟨i, by omega, fun u hu => ?_⟩
    have hu0 : IsPrimitiveRoot (ω : F) 3 := hprim0
    have hu3 : ((u : Fˣ) : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hu]; simp
    obtain ⟨j, hj, hju⟩ := hprim0.eq_pow_of_pow_eq_one hu3
    apply Units.ext
    rw [Units.coe_map, MonoidHom.coe_coe, Units.val_pow_eq_pow_val, ← hju, map_pow, ← hωi,
      ← pow_mul, ← pow_mul, mul_comm]
  · push Not at h
    refine ⟨1, Or.inl rfl, fun u hu => ?_⟩
    rw [h u hu, map_one, one_pow]


@[expose] def tor₁ (ζ : F) (h : ζ ≠ 0) : SpecialLinearGroup (Fin 3) F :=
  diagSL ζ ζ⁻¹ 1 (by field_simp)

@[expose] def tor₂ (ζ : F) (h : ζ ≠ 0) : SpecialLinearGroup (Fin 3) F :=
  diagSL ζ 1 ζ⁻¹ (by field_simp)

theorem twist_inv (σ : F ≃+* F) (ε : Bool) (x : F) : twist σ ε x⁻¹ = (twist σ ε x)⁻¹ := by
  cases ε <;> simp [twist]

theorem twist_one (σ : F ≃+* F) (ε : Bool) : twist σ ε 1 = 1 := by
  cases ε <;> simp [twist]

theorem twist_pow (σ : F ≃+* F) (ε : Bool) {x : F} {p : ℕ} (hx : x ^ p = 1) :
    twist σ ε x ^ p = 1 := by
  cases ε
  · simp only [twist, Bool.false_eq_true, if_false]
    rw [← map_pow, hx, map_one]
  · simp only [twist, if_true]
    rw [inv_pow, ← map_pow, hx, map_one, inv_one]

theorem twist_ne_one (σ : F ≃+* F) (ε : Bool) {x : F} (hx : x ≠ 1) : twist σ ε x ≠ 1 := by
  cases ε
  · simp only [twist, Bool.false_eq_true, if_false]
    intro h
    apply hx
    apply σ.injective
    rw [h, map_one]
  · simp only [twist, if_true]
    intro h
    apply hx
    apply σ.injective
    rw [inv_eq_one.mp h, map_one]

theorem det_ne_zero_gl (A : GL (Fin 3) F) : (A : Matrix (Fin 3) (Fin 3) F).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).mp A.isUnit).ne_zero

theorem isDiag_of_fix {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (A : GL (Fin 3) F) (σ : F ≃+* F)
    (ε : Bool) {ζ : F} (hζ0 : ζ ≠ 0) (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (h₁ : stdAut A σ ε (proj 3 F (tor₁ ζ hζ0)) = proj 3 F (tor₁ ζ hζ0))
    (h₂ : stdAut A σ ε (proj 3 F (tor₂ ζ hζ0)) = proj 3 F (tor₂ ζ hζ0)) :
    ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  obtain ⟨d₁, hd₁, e₁⟩ := intertwine_of_fix A σ ε ζ ζ⁻¹ 1 (by field_simp) h₁
  obtain ⟨d₂, hd₂, e₂⟩ := intertwine_of_fix A σ ε ζ 1 ζ⁻¹ (by field_simp) h₂
  rw [twist_inv, twist_one] at e₁ e₂
  exact (eq_diag_of_intertwine hp hp3 hζ hζ1 (twist_pow σ ε hζ) (twist_ne_one σ ε hζ1)
    (det_ne_zero_gl A) hd₁ hd₂ e₁ e₂).2


@[expose] def twU (σ : F ≃+* F) (ε : Bool) (u : Fˣ) : Fˣ :=
  if ε then (Units.map (σ : F →* F) u)⁻¹ else Units.map (σ : F →* F) u

theorem exists_exp_twU (σ : F ≃+* F) (ε : Bool) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ ∀ u : Fˣ, u ^ 3 = 1 → twU σ ε u = u ^ e := by
  obtain ⟨m, hm, hmu⟩ := exists_exp_of_ringEquiv σ
  cases ε
  · exact ⟨m, hm, fun u hu => by simpa [twU] using hmu u hu⟩
  · refine ⟨3 - m, by omega, fun u hu => ?_⟩
    simp only [twU, if_true]
    rw [hmu u hu]
    have h3 : u ^ m * u ^ (3 - m) = 1 := by
      rw [← pow_add, show m + (3 - m) = 3 by omega, hu]
    exact inv_eq_of_mul_eq_one_right h3

theorem stdAut_conj_diagUnits (A : GL (Fin 3) F) (σ : F ≃+* F) (ε : Bool)
    (hA : ∀ i j, i ≠ j → (A : Matrix (Fin 3) (Fin 3) F) i j = 0) (s t : Fˣ) :
    stdAut A σ ε * conjAut 3 F (diagUnits 1 s t) * (stdAut A σ ε)⁻¹ =
      conjAut 3 F (diagUnits 1 (twU σ ε s) (twU σ ε t)) := by
  rw [stdAut_conj]
  have hy : (if ε then GeneralLinearGroup.map (σ : F →+* F)
        (GeneralLinearGroup.inverseTranspose (diagUnits 1 s t))
      else GeneralLinearGroup.map (σ : F →+* F) (diagUnits 1 s t)) =
      diagUnits 1 (twU σ ε s) (twU σ ε t) := by
    cases ε
    · simp only [Bool.false_eq_true, if_false, twU]
      rw [map_diagUnits]
      simp
    · simp only [if_true, twU]
      rw [inverseTranspose_diagUnits, map_diagUnits]
      simp
  rw [hy, conj_diag_eq hA _ ![((1 : Fˣ) : F), twU σ ε s, twU σ ε t] rfl]


theorem conj_of_fix [Finite F] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (α : MulAut (projectiveSL 3 F))
    {ζ : F} (hζ0 : ζ ≠ 0) (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (h₁ : α (proj 3 F (tor₁ ζ hζ0)) = proj 3 F (tor₁ ζ hζ0))
    (h₂ : α (proj 3 F (tor₂ ζ hζ0)) = proj 3 F (tor₂ ζ hζ0)) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ ∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 →
      α * conjAut 3 F (diagUnits 1 s t) * α⁻¹ = conjAut 3 F (diagUnits 1 (s ^ e) (t ^ e)) := by
  obtain ⟨-, hgen⟩ := automorphism_generation (K := F) (n := 3) (by norm_num)
  obtain ⟨A, σ, n, hn, hα⟩ := hgen α
  have hαs : ∃ ε : Bool, α = stdAut A σ ε := by
    interval_cases n
    · exact ⟨false, by simpa [stdAut] using hα⟩
    · exact ⟨true, by simpa [stdAut] using hα⟩
  obtain ⟨ε, rfl⟩ := hαs
  have hA := isDiag_of_fix hp hp3 A σ ε hζ0 hζ hζ1 h₁ h₂
  obtain ⟨e, he, hexp⟩ := exists_exp_twU σ ε
  refine ⟨e, he, fun s t hs ht => ?_⟩
  rw [stdAut_conj_diagUnits A σ ε hA s t, hexp s hs, hexp t ht]


open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)

theorem slConjugation_of_mem_scalars (y : GL (Fin 3) F) {w : SpecialLinearGroup (Fin 3) F}
    (hw : w ∈ scalars 3 F) : slConjugation 3 F y w = w := by
  obtain ⟨c, -, hc⟩ := mem_scalars.mp hw
  apply Matrix.SpecialLinearGroup.toGL_injective
  rw [CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation]
  have : Matrix.SpecialLinearGroup.toGL w = GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    exact hc
  rw [this, ← Matrix.GeneralLinearGroup.scalar_commute]
  group

theorem slConjugation_eq_self {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) (y : GL (Fin 3) F)
    (s : SpecialLinearGroup (Fin 3) F) (hs : (proj 3 F s) ^ p = 1)
    (hy : conjAut 3 F y (proj 3 F s) = proj 3 F s) : slConjugation 3 F y s = s := by
  set X := slConjugation 3 F y s with hX
  rw [conjAut_proj] at hy
  have hz : X⁻¹ * s ∈ scalars 3 F := proj_eq_proj_iff.mp hy
  set z := X⁻¹ * s with hzdef
  have hsX : s = X * z := by rw [hzdef]; group
  have hzc : ∀ g : SpecialLinearGroup (Fin 3) F, z * g = g * z := fun g =>
    (Subgroup.mem_center_iff.mp (scalars_le_center 3 F hz) g).symm
  have hsp : s ^ p ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_pow]
    exact hs
  have hXs : X = s * z⁻¹ := by rw [hsX]; group
  have hzinv : ∀ g : SpecialLinearGroup (Fin 3) F, z⁻¹ * g = g * z⁻¹ := fun g => by
    calc z⁻¹ * g = z⁻¹ * (g * z) * z⁻¹ := by group
      _ = z⁻¹ * (z * g) * z⁻¹ := by rw [hzc g]
      _ = g * z⁻¹ := by group
  have hcomm : Commute s z⁻¹ := (hzinv s).symm
  have h1 : slConjugation 3 F y (s ^ p) = s ^ p := slConjugation_of_mem_scalars y hsp
  rw [map_pow, ← hX, hXs, hcomm.mul_pow] at h1
  have h2 : (z⁻¹) ^ p = 1 := by
    have := h1
    rw [mul_eq_left] at this
    exact this
  have hzp : z ^ p = 1 := by
    rw [← inv_inv z, inv_pow, h2, inv_one]
  obtain ⟨c, hc3, hc⟩ := mem_scalars.mp hz
  have hcp : (c : F) ^ p = 1 := by
    have h3 : ((z ^ p : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
      rw [hzp]; rfl
    rw [Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow] at h3
    have := congrFun (congrFun h3 0) 0
    simpa using this
  have hc1 : c = 1 := by
    apply Units.ext
    have hc3' : (c : F) ^ 3 = 1 := by
      rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
    simpa using eq_one_of_pow_eq_one_of_pow_eq_one hp hp3 hcp hc3'
  have hz1 : z = 1 := by
    apply Subtype.ext
    rw [hc, hc1]
    simp
  rw [hXs, hz1, inv_one, mul_one]


open CFSG.RankThree.PartTwo.Sec4 (entry_eq_zero_of_commute_diagonal)

theorem isDiag_of_slConjugation_eq {τ : Fˣ} (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    {s : SpecialLinearGroup (Fin 3) F}
    (h : slConjugation 3 F (diagUnits 1 τ (τ ^ 2)) s = s) :
    ∀ i j, i ≠ j → (s : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have hm := CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_matrix 3 F
    (diagUnits 1 τ (τ ^ 2)) s
  rw [h] at hm
  have hMi : ((diagUnits 1 τ (τ ^ 2))⁻¹ : GL (Fin 3) F).val *
      (diagUnits 1 τ (τ ^ 2) : GL (Fin 3) F).val = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hc : (s : Matrix (Fin 3) (Fin 3) F) *
        diagonal ![((1 : Fˣ) : F), (τ : F), ((τ ^ 2 : Fˣ) : F)] =
      diagonal ![((1 : Fˣ) : F), (τ : F), ((τ ^ 2 : Fˣ) : F)] *
        (s : Matrix (Fin 3) (Fin 3) F) := by
    have e1 : (diagUnits 1 τ (τ ^ 2) : GL (Fin 3) F).val * (s : Matrix (Fin 3) (Fin 3) F) =
        (s : Matrix (Fin 3) (Fin 3) F) * (diagUnits 1 τ (τ ^ 2) : GL (Fin 3) F).val := by
      calc (diagUnits 1 τ (τ ^ 2) : GL (Fin 3) F).val * (s : Matrix (Fin 3) (Fin 3) F)
          = ((diagUnits 1 τ (τ ^ 2) : GL (Fin 3) F).val * (s : Matrix (Fin 3) (Fin 3) F) *
              ((diagUnits 1 τ (τ ^ 2))⁻¹ : GL (Fin 3) F).val) *
              (diagUnits 1 τ (τ ^ 2) : GL (Fin 3) F).val := by
            rw [Matrix.mul_assoc _ _ (diagUnits 1 τ (τ ^ 2) : GL (Fin 3) F).val, hMi,
              Matrix.mul_one]
        _ = _ := by rw [← hm]
    rw [coe_diagUnits] at e1
    exact e1.symm
  have hτ0 : (τ : F) ≠ 0 := τ.ne_zero
  have h01 : ((1 : Fˣ) : F) ≠ (τ : F) := fun h' => hτ1 (Units.ext h').symm
  have h02 : ((1 : Fˣ) : F) ≠ ((τ ^ 2 : Fˣ) : F) := by
    intro h'
    apply hτ1
    have h2 : τ ^ 2 = 1 := (Units.ext h').symm
    calc τ = τ ^ 3 * (τ ^ 2)⁻¹ := by group
      _ = 1 := by rw [hτ3, h2]; simp
  have h12 : (τ : F) ≠ ((τ ^ 2 : Fˣ) : F) := by
    intro h'
    apply hτ1
    have h2 : τ = τ ^ 2 := Units.ext h'
    calc τ = τ ^ 2 * τ⁻¹ := by group
      _ = τ * τ⁻¹ := by rw [← h2]
      _ = 1 := by simp
  intro i j hij
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact entry_eq_zero_of_commute_diagonal hc (by simpa using h01)
  · exact entry_eq_zero_of_commute_diagonal hc (by simpa using h02)
  · exact entry_eq_zero_of_commute_diagonal hc (by simpa using h01.symm)
  · exact absurd rfl hij
  · exact entry_eq_zero_of_commute_diagonal hc (by simpa using h12)
  · exact entry_eq_zero_of_commute_diagonal hc (by simpa using h02.symm)
  · exact entry_eq_zero_of_commute_diagonal hc (by simpa using h12.symm)
  · exact absurd rfl hij


theorem pow_three_eq_one_of_mem_scalars {w : SpecialLinearGroup (Fin 3) F}
    (hw : w ∈ scalars 3 F) : w ^ 3 = 1 := by
  obtain ⟨c, hc3, hc⟩ := mem_scalars.mp hw
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hc, ← map_pow, Matrix.SpecialLinearGroup.coe_one]
  have : (c : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  rw [this, map_one]

theorem eq_diagonal_of_isDiag {s : SpecialLinearGroup (Fin 3) F}
    (hdiag : ∀ i j, i ≠ j → (s : Matrix (Fin 3) (Fin 3) F) i j = 0) :
    (s : Matrix (Fin 3) (Fin 3) F) = diagonal ![(s : Matrix (Fin 3) (Fin 3) F) 0 0,
      (s : Matrix (Fin 3) (Fin 3) F) 1 1, (s : Matrix (Fin 3) (Fin 3) F) 2 2] := by
  ext i j
  by_cases hij : i = j
  · subst hij
    fin_cases i <;> simp
  · rw [hdiag i j hij, diagonal_apply_ne _ hij]

theorem exists_diag_pow_eq_one {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    {s : SpecialLinearGroup (Fin 3) F}
    (hdiag : ∀ i j, i ≠ j → (s : Matrix (Fin 3) (Fin 3) F) i j = 0)
    (hs : (proj 3 F s) ^ p = 1) :
    ∃ (a b c : F) (h : a * b * c = 1), a ^ p = 1 ∧ b ^ p = 1 ∧ c ^ p = 1 ∧
      proj 3 F s = proj 3 F (diagSL a b c h) := by
  have hcop : Nat.Coprime 3 p := (Nat.coprime_primes Nat.prime_three hp).mpr (Ne.symm hp3)
  obtain ⟨r, -, hr⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  set s' := s ^ (3 * r) with hs'
  have hsp : s ^ p ∈ scalars 3 F := by
    rw [← proj_eq_one_iff, map_pow]
    exact hs
  have hs'p : s' ^ p = 1 := by
    rw [hs', ← pow_mul, mul_comm, pow_mul, pow_mul, pow_three_eq_one_of_mem_scalars hsp, one_pow]
  have hproj : proj 3 F s' = proj 3 F s := by
    rw [hs', map_pow]
    have : 3 * r = p * (3 * r / p) + 1 := by
      have := Nat.div_add_mod (3 * r) p
      omega
    rw [this, pow_succ, pow_mul, hs, one_pow, one_mul]
  have hs'diag : (s' : Matrix (Fin 3) (Fin 3) F) =
      diagonal ![(s : Matrix (Fin 3) (Fin 3) F) 0 0 ^ (3 * r),
        (s : Matrix (Fin 3) (Fin 3) F) 1 1 ^ (3 * r),
        (s : Matrix (Fin 3) (Fin 3) F) 2 2 ^ (3 * r)] := by
    rw [hs', Matrix.SpecialLinearGroup.coe_pow, eq_diagonal_of_isDiag hdiag, diagonal_pow]
    congr 1
    funext i
    fin_cases i <;> simp
  set a := (s : Matrix (Fin 3) (Fin 3) F) 0 0 ^ (3 * r) with ha
  set b := (s : Matrix (Fin 3) (Fin 3) F) 1 1 ^ (3 * r) with hb
  set c := (s : Matrix (Fin 3) (Fin 3) F) 2 2 ^ (3 * r) with hc
  have hdet : a * b * c = 1 := by
    have h1 := Matrix.SpecialLinearGroup.det_coe s'
    rw [hs'diag, det_diagonal, Fin.prod_univ_three] at h1
    simpa using h1
  have hs'eq : s' = diagSL a b c hdet := Subtype.ext hs'diag
  have hpow : ∀ i : Fin 3, (![a, b, c] i) ^ p = 1 := by
    intro i
    have h1 := congrArg (fun g : SpecialLinearGroup (Fin 3) F => (g : Matrix (Fin 3) (Fin 3) F) i i)
      hs'p
    simp only [Matrix.SpecialLinearGroup.coe_pow, hs'diag, diagonal_pow,
      Matrix.SpecialLinearGroup.coe_one, diagonal_apply_eq, Matrix.one_apply_eq] at h1
    simpa using h1
  refine ⟨a, b, c, hdet, hpow 0, hpow 1, hpow 2, ?_⟩
  rw [← hs'eq, hproj]


@[expose] noncomputable def torPhi (p : ℕ) (uv : rootsOfUnity p F × rootsOfUnity p F) :
    projectiveSL 3 F :=
  proj 3 F (diagSL (uv.1 : Fˣ) (uv.2 : Fˣ) (((uv.1 : Fˣ) * (uv.2 : Fˣ))⁻¹ : Fˣ)
    (by rw [← Units.val_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one]))

theorem mem_of_card_eq [Finite F] {p : ℕ} (hp : p.Prime) (Pbar : Subgroup (projectiveSL 3 F))
    (hcard : Nat.card Pbar = p ^ 2)
    (hT : ∀ z ∈ Pbar, ∃ (a b c : F) (h : a * b * c = 1), a ^ p = 1 ∧ b ^ p = 1 ∧ c ^ p = 1 ∧
      z = proj 3 F (diagSL a b c h))
    (a b c : F) (h : a * b * c = 1) (ha : a ^ p = 1) (hb : b ^ p = 1) (hc : c ^ p = 1) :
    proj 3 F (diagSL a b c h) ∈ Pbar := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hfin : (Set.range (torPhi (F := F) p)).Finite := Set.finite_range _
  have hsub : (Pbar : Set (projectiveSL 3 F)) ⊆ Set.range (torPhi (F := F) p) := by
    intro z hz
    obtain ⟨a, b, c, h, ha, hb, hc, rfl⟩ := hT z hz
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at ha
      exact zero_ne_one ha
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow hp.ne_zero] at hb
      exact zero_ne_one hb
    refine ⟨(⟨Units.mk0 a ha0, ?_⟩, ⟨Units.mk0 b hb0, ?_⟩), ?_⟩
    · rw [mem_rootsOfUnity]
      exact Units.ext (by simpa using ha)
    · rw [mem_rootsOfUnity]
      exact Units.ext (by simpa using hb)
    · unfold torPhi
      congr 1
      apply Subtype.ext
      have hc' : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h
      simp [diagSL, hc']
  have hle : (Set.range (torPhi (F := F) p)).ncard ≤ p ^ 2 := by
    have h1 : Nat.card (Set.range (torPhi (F := F) p)) ≤
        Nat.card (rootsOfUnity p F × rootsOfUnity p F) := Finite.card_range_le _
    rw [Nat.card_prod] at h1
    have h2 : Nat.card (rootsOfUnity p F) ≤ p := card_rootsOfUnity (k := p) (R := F)
    calc (Set.range (torPhi (F := F) p)).ncard = Nat.card (Set.range (torPhi (F := F) p)) :=
          (Nat.card_coe_set_eq _).symm
      _ ≤ p ^ 2 := by nlinarith
  have hcard' : (Pbar : Set (projectiveSL 3 F)).ncard = p ^ 2 := by
    rw [← Nat.card_coe_set_eq]
    exact hcard
  have heq := Set.eq_of_subset_of_ncard_le hsub (by rw [hcard']; exact hle) hfin
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at ha
    exact zero_ne_one ha
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hb
    exact zero_ne_one hb
  have hmem : proj 3 F (diagSL a b c h) ∈ Set.range (torPhi (F := F) p) := by
    refine ⟨(⟨Units.mk0 a ha0, ?_⟩, ⟨Units.mk0 b hb0, ?_⟩), ?_⟩
    · rw [mem_rootsOfUnity]
      exact Units.ext (by simpa using ha)
    · rw [mem_rootsOfUnity]
      exact Units.ext (by simpa using hb)
    · unfold torPhi
      congr 1
      apply Subtype.ext
      have hc' : c = (a * b)⁻¹ := eq_inv_of_mul_eq_one_right h
      simp [diagSL, hc']
  rw [← heq] at hmem
  exact hmem


theorem conj_of_fix_pbar [Finite F] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpF : p ∣ Nat.card F - 1) (τ : Fˣ) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (Pbar : Subgroup (projectiveSL 3 F)) (hcard : Nat.card Pbar = p ^ 2)
    (hexp : ∀ z ∈ Pbar, z ^ p = 1)
    (hcomm : ∀ z ∈ Pbar, conjAut 3 F (diagUnits 1 τ (τ ^ 2)) z = z)
    (α : MulAut (projectiveSL 3 F)) (hα : ∀ z ∈ Pbar, α z = z) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ ∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 →
      α * conjAut 3 F (diagUnits 1 s t) * α⁻¹ = conjAut 3 F (diagUnits 1 (s ^ e) (t ^ e)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hT : ∀ z ∈ Pbar, ∃ (a b c : F) (h : a * b * c = 1), a ^ p = 1 ∧ b ^ p = 1 ∧ c ^ p = 1 ∧
      z = proj 3 F (diagSL a b c h) := by
    intro z hz
    obtain ⟨s, rfl⟩ := proj_surjective 3 F z
    have hs := slConjugation_eq_self hp hp3 _ s (hexp _ hz) (hcomm _ hz)
    have hdiag := isDiag_of_slConjugation_eq hτ3 hτ1 hs
    obtain ⟨a, b, c, h, ha, hb, hc, hab⟩ := exists_diag_pow_eq_one hp hp3 hdiag (hexp _ hz)
    exact ⟨a, b, c, h, ha, hb, hc, hab⟩
  have hdvd : p ∣ Nat.card Fˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hζ0 : (x : F) ≠ 0 := x.ne_zero
  have hζ : (x : F) ^ p = 1 := by rw [← Units.val_pow_eq_pow_val, hxp, Units.val_one]
  have hζ1 : (x : F) ≠ 1 := fun h => hx1 (Units.ext h)
  have hinvp : ((x : F)⁻¹) ^ p = 1 := by rw [inv_pow, hζ, inv_one]
  have h1 : proj 3 F (tor₁ (x : F) hζ0) ∈ Pbar :=
    mem_of_card_eq hp Pbar hcard hT _ _ _ _ hζ hinvp (one_pow p)
  have h2 : proj 3 F (tor₂ (x : F) hζ0) ∈ Pbar :=
    mem_of_card_eq hp Pbar hcard hT _ _ _ _ hζ (one_pow p) hinvp
  exact conj_of_fix hp hp3 α hζ0 hζ hζ1 (hα _ h1) (hα _ h2)

end Model

section Embed

variable {F : Type} [Field F]

@[expose] noncomputable def pglEmb : projectiveSL 3 F →* ProjGenLinGroup (Fin 3) F :=
  QuotientGroup.lift (scalars 3 F) (Matrix.SpecialLinearGroup.toPGL)
    (by rw [Matrix.SpecialLinearGroup.toPGL_ker, scalars_eq_center])

theorem pglEmb_proj (s : SpecialLinearGroup (Fin 3) F) :
    pglEmb (proj 3 F s) = ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL s) := rfl

theorem pglEmb_injective : Function.Injective (pglEmb (F := F)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨s, rfl⟩ := proj_surjective 3 F z
  rw [pglEmb_proj, ProjGenLinGroup.mk_eq_one] at hz
  rw [proj_eq_one_iff, scalars_eq_center]
  exact (Matrix.SpecialLinearGroup.toGL_mem_center_iff s).mp hz

theorem pglEmb_conjAut (y : GL (Fin 3) F) (w : projectiveSL 3 F) :
    pglEmb (conjAut 3 F y w) =
      ProjGenLinGroup.mk y * pglEmb w * (ProjGenLinGroup.mk y)⁻¹ := by
  obtain ⟨s, rfl⟩ := proj_surjective 3 F w
  rw [conjAut_proj, pglEmb_proj, pglEmb_proj,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.toGL_slConjugation, map_mul,
    map_mul, map_inv]

end Embed


section Transport

variable {F : Type} [Field F]

open CFSG.RankThree.PartTwo.Sec4 (diagUnits coe_diagUnits diagUnits_mul)

theorem conjAut_scalar (l : Fˣ) :
    conjAut 3 F (GeneralLinearGroup.scalar (Fin 3) l) = 1 := by
  unfold conjAut
  rw [MonoidHom.comp_apply,
    CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar, map_one]

theorem conjAut_scalar_mul (l : Fˣ) (y : GL (Fin 3) F) :
    conjAut 3 F (GeneralLinearGroup.scalar (Fin 3) l * y) = conjAut 3 F y := by
  rw [map_mul, conjAut_scalar, one_mul]


theorem conj_of_fix_transport [Finite F] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (hpF : p ∣ Nat.card F - 1) (τ : Fˣ) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1) {Q : Type} [Group Q]
    (Φ : Q ≃* projectiveSL 3 F) (g : GL (Fin 3) F) (Pq : Subgroup Q)
    (hcard : Nat.card Pq = p ^ 2) (hexp : ∀ z ∈ Pq, z ^ p = 1)
    (hcomm : ∀ z ∈ Pq, conjAut 3 F (g * diagUnits 1 τ (τ ^ 2) * g⁻¹) (Φ z) = Φ z)
    (β : MulAut Q) (hβ : ∀ z ∈ Pq, β z = z) :
    ∃ e : ℕ, (e = 1 ∨ e = 2) ∧ ∀ s t : Fˣ, s ^ 3 = 1 → t ^ 3 = 1 →
      MulAut.congr Φ β * conjAut 3 F (g * diagUnits 1 s t * g⁻¹) * (MulAut.congr Φ β)⁻¹ =
        conjAut 3 F (g * diagUnits 1 (s ^ e) (t ^ e) * g⁻¹) := by
  set C : MulAut (projectiveSL 3 F) := conjAut 3 F g with hC
  have hCinv : conjAut 3 F g⁻¹ = C⁻¹ := by rw [hC, map_inv]
  set β' : MulAut (projectiveSL 3 F) := MulAut.congr Φ β with hβ'
  set α : MulAut (projectiveSL 3 F) := C⁻¹ * β' * C with hα
  set Pbar : Subgroup (projectiveSL 3 F) :=
    (Pq.map Φ.toMonoidHom).map (C⁻¹ : MulAut (projectiveSL 3 F)).toMonoidHom with hPbar
  have hmem : ∀ z : projectiveSL 3 F, z ∈ Pbar ↔ ∃ x ∈ Pq, z = C⁻¹ (Φ x) := by
    intro z
    simp only [hPbar, Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  have hPcard : Nat.card Pbar = p ^ 2 := by
    rw [hPbar, Subgroup.card_map_of_injective
      (f := (C⁻¹ : MulAut (projectiveSL 3 F)).toMonoidHom) (MulEquiv.injective _),
      Subgroup.card_map_of_injective (f := Φ.toMonoidHom) Φ.injective, hcard]
  have hPexp : ∀ z ∈ Pbar, z ^ p = 1 := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (hmem z).mp hz
    rw [← map_pow, ← map_pow, hexp x hx, map_one, map_one]
  have hy₀ : conjAut 3 F (diagUnits 1 τ (τ ^ 2)) =
      C⁻¹ * conjAut 3 F (g * diagUnits 1 τ (τ ^ 2) * g⁻¹) * C := by
    rw [map_mul, map_mul, map_inv, ← hC]
    group
  have hPcomm : ∀ z ∈ Pbar, conjAut 3 F (diagUnits 1 τ (τ ^ 2)) z = z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (hmem z).mp hz
    rw [hy₀]
    simp only [MulAut.mul_apply]
    rw [show C (C⁻¹ (Φ x)) = Φ x from MulAut.apply_inv_self _ C _, hcomm x hx]
  have hαfix : ∀ z ∈ Pbar, α z = z := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := (hmem z).mp hz
    simp only [hα, MulAut.mul_apply]
    rw [show C (C⁻¹ (Φ x)) = Φ x from MulAut.apply_inv_self _ C _]
    rw [hβ', MulAut.congr_apply]
    simp [hβ x hx]
  obtain ⟨e, he, hconj⟩ := conj_of_fix_pbar hp hp3 hpF τ hτ3 hτ1 Pbar hPcard hPexp hPcomm α hαfix
  refine ⟨e, he, fun s t hs ht => ?_⟩
  have h1 := hconj s t hs ht
  have hβeq : β' = C * α * C⁻¹ := by rw [hα]; group
  have e1 : conjAut 3 F (g * diagUnits 1 s t * g⁻¹) = C * conjAut 3 F (diagUnits 1 s t) * C⁻¹ := by
    rw [map_mul, map_mul, map_inv, ← hC]
  have e2 : conjAut 3 F (g * diagUnits 1 (s ^ e) (t ^ e) * g⁻¹) =
      C * conjAut 3 F (diagUnits 1 (s ^ e) (t ^ e)) * C⁻¹ := by
    rw [map_mul, map_mul, map_inv, ← hC]
  rw [e1, e2, ← h1, hβeq]
  group

end Transport

end CFSG.RankThree.PartTwo.Sec21.Hering2119
