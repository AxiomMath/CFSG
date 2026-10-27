module

public import CFSG.RankThree.PartOne.KF.K0Eigen

public section

namespace CFSG.RankThree.PartOne.KFK0

open Matrix

variable {F : Type} [Field F]

@[expose] def sl2Up (c : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, c; 0, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def sl2Lo (c : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; c, 1], by simp [Matrix.det_fin_two_of]⟩

@[expose] def sl2Diag (a : Fˣ) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![(a : F), 0; 0, ((a⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

theorem sl2Up_mul (c d : F) : sl2Up c * sl2Up d = sl2Up (c + d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Up, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2Lo_mul (c d : F) : sl2Lo c * sl2Lo d = sl2Lo (c + d) := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Lo, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem sl2Up_zero : sl2Up (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Up]

theorem sl2Lo_zero : sl2Lo (0 : F) = 1 := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Lo]

@[expose] def sl2UpHom (F : Type) [Field F] : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun c := sl2Up (Multiplicative.toAdd c)
  map_one' := sl2Up_zero
  map_mul' _ _ := (sl2Up_mul _ _).symm

@[expose] def sl2LoHom (F : Type) [Field F] : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun c := sl2Lo (Multiplicative.toAdd c)
  map_one' := sl2Lo_zero
  map_mul' _ _ := (sl2Lo_mul _ _).symm

@[expose] def sl2U (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  (sl2UpHom F).range

@[expose] def sl2L (F : Type) [Field F] : Subgroup (SpecialLinearGroup (Fin 2) F) :=
  (sl2LoHom F).range

theorem mem_sl2U {g : SpecialLinearGroup (Fin 2) F} : g ∈ sl2U F ↔ ∃ c : F, g = sl2Up c :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem mem_sl2L {g : SpecialLinearGroup (Fin 2) F} : g ∈ sl2L F ↔ ∃ c : F, g = sl2Lo c :=
  ⟨fun ⟨c, hc⟩ => ⟨Multiplicative.toAdd c, hc.symm⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc.symm⟩⟩

theorem sl2Up_injective : Function.Injective (sl2Up : F → SpecialLinearGroup (Fin 2) F) := by
  intro c d h
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [sl2Up] using this

theorem sl2Lo_injective : Function.Injective (sl2Lo : F → SpecialLinearGroup (Fin 2) F) := by
  intro c d h
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 1 0) h
  simpa [sl2Lo] using this

theorem sl2UpHom_injective : Function.Injective (sl2UpHom F) := fun _ _ h =>
  Multiplicative.toAdd.injective (sl2Up_injective h)

theorem sl2LoHom_injective : Function.Injective (sl2LoHom F) := fun _ _ h =>
  Multiplicative.toAdd.injective (sl2Lo_injective h)

theorem card_sl2U : Nat.card (sl2U F) = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective (sl2UpHom_injective (F := F))).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem card_sl2L : Nat.card (sl2L F) = Nat.card F :=
  (Nat.card_congr (MonoidHom.ofInjective (sl2LoHom_injective (F := F))).toEquiv).symm.trans
    (Nat.card_congr Multiplicative.toAdd)

theorem sq_sl2Up [CharP F 2] (c : F) : sl2Up c * sl2Up c = 1 := by
  rw [sl2Up_mul, CharTwo.add_self_eq_zero, sl2Up_zero]

theorem sq_sl2Lo [CharP F 2] (c : F) : sl2Lo c * sl2Lo c = 1 := by
  rw [sl2Lo_mul, CharTwo.add_self_eq_zero, sl2Lo_zero]

theorem sl2Diag_mul_sl2Up_mul_inv (a : Fˣ) (c : F) :
    sl2Diag a * sl2Up c * (sl2Diag a)⁻¹ = sl2Up ((a : F) ^ 2 * c) := by
  apply Subtype.ext
  have hinv : ((sl2Diag a)⁻¹ : SpecialLinearGroup (Fin 2) F) = sl2Diag a⁻¹ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Diag, Matrix.adjugate_fin_two]
  rw [hinv]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [sl2Diag, sl2Up, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp

theorem sl2Diag_mul_sl2Lo_mul_inv (a : Fˣ) (c : F) :
    sl2Diag a * sl2Lo c * (sl2Diag a)⁻¹ = sl2Lo (((a⁻¹ : Fˣ) : F) ^ 2 * c) := by
  apply Subtype.ext
  have hinv : ((sl2Diag a)⁻¹ : SpecialLinearGroup (Fin 2) F) = sl2Diag a⁻¹ := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Diag, Matrix.adjugate_fin_two]
  rw [hinv]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals simp [sl2Diag, sl2Lo, Matrix.mul_apply, Fin.sum_univ_two]
  all_goals field_simp

theorem sl2Diag_conj_mem_sl2U (a : Fˣ) {g : SpecialLinearGroup (Fin 2) F} (hg : g ∈ sl2U F) :
    sl2Diag a * g * (sl2Diag a)⁻¹ ∈ sl2U F := by
  obtain ⟨c, rfl⟩ := mem_sl2U.1 hg
  rw [sl2Diag_mul_sl2Up_mul_inv]
  exact mem_sl2U.2 ⟨_, rfl⟩

theorem sl2Diag_conj_mem_sl2L (a : Fˣ) {g : SpecialLinearGroup (Fin 2) F} (hg : g ∈ sl2L F) :
    sl2Diag a * g * (sl2Diag a)⁻¹ ∈ sl2L F := by
  obtain ⟨c, rfl⟩ := mem_sl2L.1 hg
  rw [sl2Diag_mul_sl2Lo_mul_inv]
  exact mem_sl2L.2 ⟨_, rfl⟩

theorem sl2U_ne_sl2L : sl2U F ≠ sl2L F := by
  intro h
  have h1 : sl2Up (1 : F) ∈ sl2U F := mem_sl2U.2 ⟨1, rfl⟩
  rw [h] at h1
  obtain ⟨c, hc⟩ := mem_sl2L.1 h1
  have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F) 0 1) hc
  simp [sl2Up, sl2Lo] at this

theorem sl2U_sup_sl2L : sl2U F ⊔ sl2L F = ⊤ := by
  rw [eq_top_iff]
  intro A _
  set S := sl2U F ⊔ sl2L F with hS
  have key : ∀ B : SpecialLinearGroup (Fin 2) F, (B : Matrix (Fin 2) (Fin 2) F) 1 0 ≠ 0 → B ∈ S := by
    intro B hc
    set a := (B : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
    set b := (B : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
    set c := (B : Matrix (Fin 2) (Fin 2) F) 1 0 with hc'
    set d := (B : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
    have hdet : a * d - b * c = 1 := by
      have := B.2
      rwa [Matrix.det_fin_two] at this
    have hBeq : B = sl2Up ((a - 1) / c) * sl2Lo c * sl2Up ((d - 1) / c) := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2Up, sl2Lo, Matrix.mul_apply, Fin.sum_univ_two, ← ha, ← hb, ← hc', ← hd] <;>
        field_simp <;> first | ring1 | linear_combination (-1 : F) * hdet
    rw [hBeq]
    exact S.mul_mem (S.mul_mem (Subgroup.mem_sup_left (mem_sl2U.2 ⟨_, rfl⟩))
      (Subgroup.mem_sup_right (mem_sl2L.2 ⟨_, rfl⟩)))
      (Subgroup.mem_sup_left (mem_sl2U.2 ⟨_, rfl⟩))
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) F) 1 0 = 0
  · have hdet : (A : Matrix (Fin 2) (Fin 2) F) 0 0 * (A : Matrix (Fin 2) (Fin 2) F) 1 1 = 1 := by
      have := A.2
      rw [Matrix.det_fin_two, hc] at this
      simpa using this
    have ha0 : (A : Matrix (Fin 2) (Fin 2) F) 0 0 ≠ 0 := left_ne_zero_of_mul_eq_one hdet
    have h' : sl2Lo (1 : F) * A ∈ S := by
      apply key
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simp [sl2Lo, Matrix.mul_apply, Fin.sum_univ_two, hc, ha0]
    have : A = (sl2Lo (1 : F))⁻¹ * (sl2Lo (1 : F) * A) := by group
    rw [this]
    exact S.mul_mem (S.inv_mem (Subgroup.mem_sup_right (mem_sl2L.2 ⟨_, rfl⟩))) h'
  · exact key A hc

theorem coe_inv_mul_coe (P : GL (Fin 2) F) :
    ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (P : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

theorem coe_mul_coe_inv (P : GL (Fin 2) F) :
    (P : Matrix (Fin 2) (Fin 2) F) * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

@[expose] def conjSLFun (P : GL (Fin 2) F) (A : SpecialLinearGroup (Fin 2) F) :
    SpecialLinearGroup (Fin 2) F :=
  ⟨((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) *
      (P : Matrix (Fin 2) (Fin 2) F), by
    rw [Matrix.det_mul, Matrix.det_mul, A.2, mul_one]
    have h := congrArg Matrix.det (coe_inv_mul_coe P)
    rwa [Matrix.det_mul, Matrix.det_one] at h⟩

theorem coe_conjSLFun (P : GL (Fin 2) F) (A : SpecialLinearGroup (Fin 2) F) :
    (conjSLFun P A : Matrix (Fin 2) (Fin 2) F) =
      ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) *
        (P : Matrix (Fin 2) (Fin 2) F) := rfl

@[expose] def conjSL (P : GL (Fin 2) F) :
    SpecialLinearGroup (Fin 2) F →* SpecialLinearGroup (Fin 2) F where
  toFun := conjSLFun P
  map_one' := by
    apply Subtype.ext
    rw [coe_conjSLFun, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one, coe_inv_mul_coe]
  map_mul' A B := by
    apply Subtype.ext
    rw [coe_conjSLFun, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      coe_conjSLFun, coe_conjSLFun]
    calc ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * ((A : Matrix (Fin 2) (Fin 2) F) *
          (B : Matrix (Fin 2) (Fin 2) F)) * (P : Matrix (Fin 2) (Fin 2) F)
        = ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) *
            ((P : Matrix (Fin 2) (Fin 2) F) * ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)) *
            (B : Matrix (Fin 2) (Fin 2) F) * (P : Matrix (Fin 2) (Fin 2) F) := by
          rw [coe_mul_coe_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem conjSLFun_conjSLFun_inv (P : GL (Fin 2) F) (A : SpecialLinearGroup (Fin 2) F) :
    conjSLFun P (conjSLFun P⁻¹ A) = A := by
  apply Subtype.ext
  rw [coe_conjSLFun, coe_conjSLFun, inv_inv]
  calc _ = ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (P : Matrix (Fin 2) (Fin 2) F) *
        (A : Matrix (Fin 2) (Fin 2) F) *
        (((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * (P : Matrix (Fin 2) (Fin 2) F)) := by
          simp only [Matrix.mul_assoc]
    _ = A := by rw [coe_inv_mul_coe, Matrix.one_mul, Matrix.mul_one]

@[expose] def conjSLEquiv (P : GL (Fin 2) F) :
    SpecialLinearGroup (Fin 2) F ≃* SpecialLinearGroup (Fin 2) F :=
  MulEquiv.mk' ⟨conjSLFun P, conjSLFun P⁻¹, fun A => by
      simpa using conjSLFun_conjSLFun_inv P⁻¹ A, conjSLFun_conjSLFun_inv P⟩ (conjSL P).map_mul

theorem conjSLEquiv_apply (P : GL (Fin 2) F) (A : SpecialLinearGroup (Fin 2) F) :
    conjSLEquiv P A = conjSLFun P A := rfl

theorem exists_diag_conj {p : ℕ} (hp : 0 < p) (hpodd : Odd p) {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {g : SpecialLinearGroup (Fin 2) F} (hg : g ^ p = 1) (hg1 : g ≠ 1) :
    ∃ (P : GL (Fin 2) F) (a : Fˣ), a ^ p = 1 ∧ a ≠ 1 ∧ conjSLFun P g = sl2Diag a := by
  classical
  set M : Matrix (Fin 2) (Fin 2) F := (g : Matrix (Fin 2) (Fin 2) F) with hM
  have hMp : M ^ p = 1 := by
    have := congrArg (fun A : SpecialLinearGroup (Fin 2) F => (A : Matrix (Fin 2) (Fin 2) F)) hg
    simpa [Matrix.SpecialLinearGroup.coe_pow] using this
  have hM1 : M ≠ 1 := fun h => hg1 (Subtype.ext (by simpa using h))
  obtain ⟨ν, hνp, hν1, v, hv0, hv⟩ := exists_eigenvector_of_pow_eq_one hp hζ hMp hM1
  have hdetM : M.det = 1 := g.2
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne'] at hνp
    exact zero_ne_one hνp
  have hνsq : ν ^ 2 ≠ 1 := by
    intro h2
    obtain ⟨k, hk⟩ := hpodd
    have h3 : ν ^ p = ν := by rw [hk, pow_succ, pow_mul, h2, one_pow, one_mul]
    exact hν1 (h3.symm.trans hνp)
  have hνne : ν ≠ ν⁻¹ := by
    intro h
    apply hνsq
    calc ν ^ 2 = ν * ν⁻¹ := by rw [sq]; exact congrArg (ν * ·) h
      _ = 1 := mul_inv_cancel₀ hν0
  have hdetf : ∀ t : F, (M - t • (1 : Matrix (Fin 2) (Fin 2) F)).det =
      t ^ 2 - (M 0 0 + M 1 1) * t + 1 := by
    intro t
    have h := hdetM
    rw [Matrix.det_fin_two] at h ⊢
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, Matrix.one_apply_ne,
      smul_eq_mul, mul_one, mul_zero, sub_zero, ne_eq, Fin.zero_eq_one_iff,
      not_false_eq_true, Fin.one_eq_zero_iff, OfNat.ofNat_ne_one]
    linear_combination h
  have hdet1 : (M - ν • (1 : Matrix (Fin 2) (Fin 2) F)).det = 0 :=
    Matrix.exists_mulVec_eq_zero_iff.1 ⟨v, hv0, by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, hv, sub_self]⟩
  have hdet2 : (M - ν⁻¹ • (1 : Matrix (Fin 2) (Fin 2) F)).det = 0 := by
    rw [hdetf] at hdet1 ⊢
    field_simp
    linear_combination hdet1
  obtain ⟨w, hw0, hw⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet2
  have hw' : M.mulVec w = ν⁻¹ • w := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hw
    exact hw
  set Pm : Matrix (Fin 2) (Fin 2) F := !![v 0, w 0; v 1, w 1] with hPm
  have hMP : M * Pm = Pm * Matrix.diagonal ![ν, ν⁻¹] := by
    ext i j
    fin_cases j
    · have := congrFun hv i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
      simp [hPm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, this]
      fin_cases i <;> simp [mul_comm]
    · have := congrFun hw' i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul] at this
      simp [hPm, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply, this]
      fin_cases i <;> simp [mul_comm]
  have hPdet : Pm.det ≠ 0 := by
    intro h0
    obtain ⟨z, hz0, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have hzv : z 0 • v + z 1 • w = 0 := by
      ext i
      have := congrFun hz i
      fin_cases i <;> simp [hPm, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this ⊢ <;>
        linear_combination this
    have hz2 := congrArg M.mulVec hzv
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hv, hw', Matrix.mulVec_zero] at hz2
    have hz3 : (z 0 * (ν - ν⁻¹)) • v = 0 := by
      have e : (z 0 * (ν - ν⁻¹)) • v =
          (z 0 • ν • v + z 1 • ν⁻¹ • w) - ν⁻¹ • (z 0 • v + z 1 • w) := by
        ext i; simp; ring
      rw [e, hz2, hzv]; simp
    have hz0' : z 0 = 0 := by
      by_contra hne
      have : z 0 * (ν - ν⁻¹) ≠ 0 := mul_ne_zero hne (sub_ne_zero.2 hνne)
      exact hv0 ((smul_eq_zero.1 hz3).resolve_left this)
    rw [hz0', zero_smul, zero_add] at hzv
    have hz1' : z 1 = 0 := (smul_eq_zero.1 hzv).resolve_right hw0
    exact hz0 (by ext i; fin_cases i <;> simp [hz0', hz1'])
  set P : GL (Fin 2) F := Matrix.GeneralLinearGroup.mkOfDetNeZero Pm hPdet with hP
  refine ⟨P, Units.mk0 ν hν0, Units.ext (by simpa using hνp), fun h => hν1 (congrArg Units.val h),
    ?_⟩
  apply Subtype.ext
  have hPval : (P : Matrix (Fin 2) (Fin 2) F) = Pm := rfl
  have hinv : ((P⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Pm = 1 := by
    rw [← hPval]; exact coe_inv_mul_coe P
  rw [coe_conjSLFun, hPval, ← hM, Matrix.mul_assoc, hMP, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Diag]

theorem exists_two_roots {K : Type} [Group K] [CharP F 2] (ψ : SpecialLinearGroup (Fin 2) F ≃* K)
    {p : ℕ} (hp : 0 < p) (hpodd : Odd p) {ζ : F} (hζ : IsPrimitiveRoot ζ p) {u : K} (hu : u ^ p = 1)
    (hu1 : u ≠ 1) :
    ∃ R₁ R₂ : Subgroup K, Nat.card R₁ = Nat.card F ∧ Nat.card R₂ = Nat.card F ∧
      (∀ x ∈ R₁, x ^ 2 = 1) ∧ (∀ x ∈ R₂, x ^ 2 = 1) ∧ (∀ x ∈ R₁, u * x * u⁻¹ ∈ R₁) ∧
      (∀ x ∈ R₂, u * x * u⁻¹ ∈ R₂) ∧ R₁ ≠ R₂ ∧ R₁ ⊔ R₂ = ⊤ := by
  have hg : (ψ.symm u) ^ p = 1 := by rw [← map_pow, hu, map_one]
  have hg1 : ψ.symm u ≠ 1 := fun h => hu1 (by simpa using congrArg ψ h)
  obtain ⟨P, a, -, -, hPa⟩ := exists_diag_conj hp hpodd hζ hg hg1
  let ψ' : SpecialLinearGroup (Fin 2) F ≃* K := (conjSLEquiv P).symm.trans ψ
  have hψ'a : ψ' (sl2Diag a) = u := by
    have h1 : (conjSLEquiv P).symm (sl2Diag a) = ψ.symm u := by
      rw [MulEquiv.symm_apply_eq, conjSLEquiv_apply]
      exact hPa.symm
    simp only [ψ', MulEquiv.trans_apply, h1, MulEquiv.apply_symm_apply]
  refine ⟨(sl2U F).map ψ'.toMonoidHom, (sl2L F).map ψ'.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective ψ'.injective, card_sl2U]
  · rw [Subgroup.card_map_of_injective ψ'.injective, card_sl2L]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_sl2U.1 hy
    show ψ' (sl2Up c) ^ 2 = 1
    rw [sq, ← map_mul, sq_sl2Up, map_one]
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_sl2L.1 hy
    show ψ' (sl2Lo c) ^ 2 = 1
    rw [sq, ← map_mul, sq_sl2Lo, map_one]
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨sl2Diag a * y * (sl2Diag a)⁻¹, sl2Diag_conj_mem_sl2U a hy, ?_⟩
    show ψ' (sl2Diag a * y * (sl2Diag a)⁻¹) = u * ψ' y * u⁻¹
    rw [map_mul, map_mul, map_inv, hψ'a]
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨sl2Diag a * y * (sl2Diag a)⁻¹, sl2Diag_conj_mem_sl2L a hy, ?_⟩
    show ψ' (sl2Diag a * y * (sl2Diag a)⁻¹) = u * ψ' y * u⁻¹
    rw [map_mul, map_mul, map_inv, hψ'a]
  · intro h
    apply sl2U_ne_sl2L (F := F)
    have := congrArg (Subgroup.comap ψ'.toMonoidHom) h
    rwa [Subgroup.comap_map_eq_self_of_injective ψ'.injective,
      Subgroup.comap_map_eq_self_of_injective ψ'.injective] at this
  · rw [← Subgroup.map_sup, sl2U_sup_sl2L, ← MonoidHom.range_eq_map]
    exact MonoidHom.range_eq_top.2 ψ'.surjective

end CFSG.RankThree.PartOne.KFK0
