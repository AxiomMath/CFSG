module

public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.CharacterTheory.Semidihedral.FixedFieldData
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldFullAutomorphism

public section

namespace CFSG.RankThree.PartTwo.Sec20

open scoped MatrixGroups

section Helpers

variable {F : Type} [Field F]

private theorem map_map_eq (σ τ : F ≃+* F) (g : SL(2, F)) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (Matrix.SpecialLinearGroup.map τ.toRingHom g) =
      Matrix.SpecialLinearGroup.map (σ * τ).toRingHom g := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

private theorem map_one_eq (g : SL(2, F)) :
    Matrix.SpecialLinearGroup.map (1 : F ≃+* F).toRingHom g = g := by
  ext i j
  simp [Matrix.SpecialLinearGroup.map_apply_coe]

open CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField in
private theorem exists_semilinear_decomposition {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (α : MulAut SL(2, F)) (hα : α * α = 1) (hinner : ∀ g : SL(2, F), α ≠ MulAut.conj g) :
    ∃ (p : SL(2, F)) (σ : F ≃+* F),
      (∀ g, α g = p * Matrix.SpecialLinearGroup.map σ.toRingHom g * p⁻¹) ∧
      p * Matrix.SpecialLinearGroup.map σ.toRingHom p = 1 ∧ σ * σ = 1 ∧ σ ≠ 1 := by
  have hmodel := (even_SL2_full_automorphism_semilinear_model hn hF).2.2.2.2
  obtain ⟨⟨p, σ⟩, hpσ, -⟩ := hmodel α
  obtain ⟨q₀, -, hq₀⟩ := hmodel 1
  have hg : ∀ g, α (α g) = g := fun g => by
    have := congrArg (fun β : MulAut SL(2, F) => β g) hα
    simpa using this
  have h1 : (p * Matrix.SpecialLinearGroup.map σ.toRingHom p, σ * σ) = q₀ := by
    apply hq₀
    intro g
    show g = (p * Matrix.SpecialLinearGroup.map σ.toRingHom p) *
      Matrix.SpecialLinearGroup.map (σ * σ).toRingHom g *
        (p * Matrix.SpecialLinearGroup.map σ.toRingHom p)⁻¹
    rw [← map_map_eq]
    conv_lhs => rw [← hg g, hpσ (α g), hpσ g]
    simp only [map_mul, map_inv]
    group
  have h2 : ((1 : SL(2, F)), (1 : F ≃+* F)) = q₀ := by
    apply hq₀
    intro g
    show (1 : MulAut SL(2, F)) g = 1 * Matrix.SpecialLinearGroup.map (1 : F ≃+* F).toRingHom g *
      (1 : SL(2, F))⁻¹
    rw [map_one_eq, MulAut.one_apply, inv_one, one_mul, mul_one]
  have h3 := h1.trans h2.symm
  have hpp : p * Matrix.SpecialLinearGroup.map σ.toRingHom p = 1 := congrArg Prod.fst h3
  have hσσ : σ * σ = 1 := congrArg Prod.snd h3
  refine ⟨p, σ, hpσ, hpp, hσσ, ?_⟩
  rintro rfl
  apply hinner p
  ext g : 1
  rw [hpσ g, MulAut.conj_apply, map_one_eq]

private theorem exists_fixed_vector [CharP F 2] {σ : F ≃+* F} {p : SL(2, F)}
    (hpp : p * Matrix.SpecialLinearGroup.map σ.toRingHom p = 1) :
    ∃ w : Fin 2 → F, w ≠ 0 ∧
      (p : Matrix (Fin 2) (Fin 2) F).mulVec (fun i => σ (w i)) = w := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have e : ∀ i j, ((p : Matrix (Fin 2) (Fin 2) F) *
      (Matrix.SpecialLinearGroup.map σ.toRingHom p : Matrix (Fin 2) (Fin 2) F)) i j =
        (1 : Matrix (Fin 2) (Fin 2) F) i j := fun i j => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, hpp, Matrix.SpecialLinearGroup.coe_one]
  have e00 := e 0 0
  have e10 := e 1 0
  simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.SpecialLinearGroup.map_apply_coe] at e00 e10
  by_cases h : (1 : F) + p.1 0 0 = 0 ∧ p.1 1 0 = 0
  · have ha : p.1 0 0 = 1 := by linear_combination h.1 - h2
    refine ⟨![1, 0], fun h0 => by simpa using congrFun h0 0, ?_⟩
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, ha]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, h.2]
  · refine ⟨![1 + p.1 0 0, p.1 1 0], fun h0 => h ⟨by simpa using congrFun h0 0,
      by simpa using congrFun h0 1⟩, ?_⟩
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination e00
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
      linear_combination e10

private theorem exists_sl_first_column {w : Fin 2 → F} (hw : w ≠ 0) :
    ∃ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = w := by
  by_cases h0 : w 0 = 0
  · have h1 : w 1 ≠ 0 := fun h1 => hw (by
      funext i
      fin_cases i
      · exact h0
      · exact h1)
    refine ⟨⟨!![0, -(w 1)⁻¹; w 1, 0], by simp [Matrix.det_fin_two_of, h1]⟩, ?_⟩
    ext i
    fin_cases i
    · simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using h0.symm
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![w 0, 0; w 1, (w 0)⁻¹], by simp [Matrix.det_fin_two_of, h0]⟩, ?_⟩
    ext i
    fin_cases i
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
    · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem exists_sl_eigen {w : Fin 2 → F} (hw : w ≠ 0) (u : Fˣ) :
    ∃ x : SL(2, F), (x : Matrix (Fin 2) (Fin 2) F).mulVec w = (u : F) • w := by
  obtain ⟨g, hg⟩ := exists_sl_first_column hw
  let T : SL(2, F) := ⟨!![(u : F), 0; 0, ((u⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩
  refine ⟨g * T * g⁻¹, ?_⟩
  have hginv : ((g⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = ![1, 0] := by
    rw [← hg, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hT : (T : Matrix (Fin 2) (Fin 2) F).mulVec ![1, 0] = (u : F) • ![1, 0] := by
    ext i
    fin_cases i <;> simp [T, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hginv, hT, Matrix.mulVec_smul, hg]

private theorem mulVec_mul_inv_eq {σ : F ≃+* F} {p : SL(2, F)} {w : Fin 2 → F}
    (hw : (p : Matrix (Fin 2) (Fin 2) F).mulVec (fun i => σ (w i)) = w)
    (α : MulAut SL(2, F))
    (hα : ∀ g, α g = p * Matrix.SpecialLinearGroup.map σ.toRingHom g * p⁻¹)
    {x : SL(2, F)} {u : F} (hu : u ≠ 0)
    (hx : (x : Matrix (Fin 2) (Fin 2) F).mulVec w = u • w) :
    ((α x * x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = (σ u * u⁻¹) • w := by
  have h1 : ((p⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = fun i => σ (w i) := by
    conv_lhs => rw [← hw]
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have h2 : ((Matrix.SpecialLinearGroup.map σ.toRingHom x : SL(2, F)) :
      Matrix (Fin 2) (Fin 2) F).mulVec (fun i => σ (w i)) =
        fun i => σ ((x : Matrix (Fin 2) (Fin 2) F).mulVec w i) := by
    funext i
    rw [Matrix.SpecialLinearGroup.map_apply_coe]
    exact (σ.toRingHom.map_mulVec (x : Matrix (Fin 2) (Fin 2) F) w i).symm
  have h3 : ((α x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = σ u • w := by
    rw [hα x, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, hx]
    have : (fun i => σ ((u • w) i)) = σ u • (fun i => σ (w i)) := by
      funext i
      simp
    rw [this, Matrix.mulVec_smul, hw]
  have h4 : u • ((α x * x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = σ u • w := by
    rw [← Matrix.mulVec_smul, ← hx, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right, h3]
  calc ((α x * x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w =
      u⁻¹ • (u • ((α x * x⁻¹ : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w) := by
        rw [smul_smul, inv_mul_cancel₀ hu, one_smul]
    _ = (σ u * u⁻¹) • w := by rw [h4, smul_smul, mul_comm]

private theorem pow_eq_one_of_mulVec_eq {y : SL(2, F)} {w : Fin 2 → F} (hw : w ≠ 0) {c : F}
    (h : (y : Matrix (Fin 2) (Fin 2) F).mulVec w = c • w) {k : ℕ} (hk : y ^ k = 1) :
    c ^ k = 1 := by
  have hpow : ∀ k : ℕ, ((y ^ k : SL(2, F)) : Matrix (Fin 2) (Fin 2) F).mulVec w = c ^ k • w := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, h,
        Matrix.mulVec_smul, ih, smul_smul, pow_succ']
  have h1 := hpow k
  rw [hk, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h1
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hw
  have h2 := congrFun h1 i
  simp only [Pi.smul_apply, smul_eq_mul] at h2
  exact mul_right_cancel₀ (by simpa using hi) (by rw [one_mul]; exact h2.symm)

private theorem zpow_apply_eq_self {σ : F ≃+* F} {x : F} (h : σ x = x) (j : ℤ) :
    (σ ^ j) x = x := by
  induction j using Int.induction_on with
  | zero => simp
  | succ j ih => rw [_root_.zpow_add_one, RingAut.mul_apply, h, ih]
  | pred j ih =>
    rw [_root_.zpow_sub_one]
    have : σ⁻¹ x = x := σ.symm_apply_eq.mpr h.symm
    rw [RingAut.mul_apply, this, ih]

open CFSG.Semidihedral.FixedFieldData in
private theorem exists_generator_pow_dvd [Finite F] [CharP F 2] {n : ℕ} (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) {σ : F ≃+* F} (hσ2 : σ * σ = 1) (hσ1 : σ ≠ 1) :
    Even n ∧ ∃ u : Fˣ, ∀ k : ℕ, (σ (u : F) * (u : F)⁻¹) ^ k = 1 → 2 ^ (n / 2) + 1 ∣ k := by
  have hord : orderOf σ = 2 := orderOf_eq_prime (by rw [pow_two]; exact hσ2) hσ1
  have hAcard : Nat.card (Subgroup.zpowers σ) = 2 := by rw [Nat.card_zpowers, hord]
  have h0 : Nat.card (FixedPoints.subfield (Subgroup.zpowers σ) F) = 2 ^ (n / 2) := by
    rw [fixedSubfield_card 2 n F hF, hAcard]
  have hsq : 2 ^ n = (2 ^ (n / 2)) ^ 2 := by
    rw [← hF, nat_card_eq_fixedSubfield_card_pow F (Subgroup.zpowers σ), h0, hAcard]
  have hev : n = n / 2 * 2 := by
    apply Nat.pow_right_injective (le_refl 2)
    simpa only [← pow_mul] using hsq
  have hr2 : 2 ≤ 2 ^ (n / 2) :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (n / 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨u, hu⟩ := IsCyclic.exists_generator (α := Fˣ)
  refine ⟨⟨n / 2, by omega⟩, u, fun k hk => ?_⟩
  have hu0 : (u : F) ≠ 0 := u.ne_zero
  have hσk : σ ((u : F) ^ k) = (u : F) ^ k := by
    rw [mul_pow, inv_pow] at hk
    rw [map_pow]
    exact (mul_inv_eq_one₀ (pow_ne_zero k hu0)).1 hk
  have hmem : (u : F) ^ k ∈ FixedPoints.subfield (Subgroup.zpowers σ) F := by
    rw [mem_fixedSubfield_iff]
    rintro ⟨a, ha⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    exact zpow_apply_eq_self hσk j
  have hz0 : (⟨(u : F) ^ k, hmem⟩ : FixedPoints.subfield (Subgroup.zpowers σ) F) ≠ 0 :=
    fun h => pow_ne_zero k hu0 (congrArg Subtype.val h)
  have : Fintype (FixedPoints.subfield (Subgroup.zpowers σ) F) := Fintype.ofFinite _
  have hpow := FiniteField.pow_card_sub_one_eq_one _ hz0
  rw [← Nat.card_eq_fintype_card, h0] at hpow
  have hpowF : ((u : F) ^ k) ^ (2 ^ (n / 2) - 1) = 1 := by
    simpa using congrArg Subtype.val hpow
  have hunit : u ^ (k * (2 ^ (n / 2) - 1)) = 1 :=
    Units.ext (by simpa [pow_mul] using hpowF)
  have hou : orderOf u = 2 ^ n - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hu, Nat.card_units, hF]
  have hdvd : 2 ^ n - 1 ∣ k * (2 ^ (n / 2) - 1) := hou ▸ orderOf_dvd_of_pow_eq_one hunit
  have hfac : 2 ^ n - 1 = (2 ^ (n / 2) + 1) * (2 ^ (n / 2) - 1) := by
    have h := Nat.sq_sub_sq (2 ^ (n / 2)) 1
    rwa [one_pow, ← hsq] at h
  rw [hfac] at hdvd
  exact Nat.dvd_of_mul_dvd_mul_right (by omega) hdvd

end Helpers

theorem exists_dvd_orderOf_mul_inv_SL2_even_of_card {F : Type} [Field F] [Finite F] {m : ℕ}
    (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ m) (α : MulAut SL(2, F)) (hα : α * α = 1)
    (hinner : ∀ g : SL(2, F), α ≠ MulAut.conj g) :
    Even m ∧ ∃ x : SL(2, F), 2 ^ (m / 2) + 1 ∣ orderOf (α x * x⁻¹) := by
  have : CharP F 2 :=
    CFSG.Semidihedral.FixedFieldData.characteristic_of_prime_power_card F Nat.prime_two hF
  obtain ⟨p, σ, hpσ, hpp, hσ2, hσ1⟩ := exists_semilinear_decomposition hm hF α hα hinner
  obtain ⟨hev, u, hu⟩ := exists_generator_pow_dvd hm hF hσ2 hσ1
  obtain ⟨w, hw0, hw⟩ := exists_fixed_vector hpp
  obtain ⟨x, hx⟩ := exists_sl_eigen hw0 u
  exact ⟨hev, x, hu _ (pow_eq_one_of_mulVec_eq hw0
    (mulVec_mul_inv_eq hw α hpσ u.ne_zero hx) (pow_orderOf_eq_one _))⟩

private theorem projSL_eq_range (F : Type) [Field F] :
    CFSG.Assembly.RankThreeEven.projSL 2 F =
      (Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* Matrix.ProjGenLinGroup (Fin 2) F).range := by
  rw [CFSG.Assembly.RankThreeEven.projSL, CFSG.Assembly.RankThreeEven.projImage,
    Matrix.SpecialLinearGroup.toPGL, MonoidHom.range_comp,
    Matrix.SpecialLinearGroup.range_toGL_eq_ker_det]

noncomputable def slTwoEquivProjSL (F : Type) [Field F] [CharP F 2] :
    SL(2, F) ≃* CFSG.Assembly.RankThreeEven.projSL 2 F :=
  MulEquiv.ofBijective
    ((Matrix.SpecialLinearGroup.toPGL : SL(2, F) →* Matrix.ProjGenLinGroup (Fin 2) F).codRestrict
      (CFSG.Assembly.RankThreeEven.projSL 2 F) (fun A => by
        rw [projSL_eq_range]
        exact ⟨A, rfl⟩))
    ⟨by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro A hA
      have h : A ∈ (Matrix.SpecialLinearGroup.toPGL :
          SL(2, F) →* Matrix.ProjGenLinGroup (Fin 2) F).ker := by
        rw [MonoidHom.mem_ker] at hA ⊢
        exact congrArg Subtype.val hA
      rw [Matrix.SpecialLinearGroup.toPGL_ker,
        CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField.sl2_center_eq_bot] at h
      exact h,
     by
      rintro ⟨x, hx⟩
      rw [projSL_eq_range] at hx
      obtain ⟨A, rfl⟩ := hx
      exact ⟨A, rfl⟩⟩

end CFSG.RankThree.PartTwo.Sec20
