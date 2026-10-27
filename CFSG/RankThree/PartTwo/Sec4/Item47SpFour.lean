module

public import CFSG.RankThree.PartTwo.Sec4.Item47Witness

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open Matrix

theorem ringAut_fix_of_cube_root {K : Type} [Field K] {σ : K ≃+* K} (hσ : σ ^ 3 = 1) {ω : K}
    (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) : σ ω = ω := by
  have hω0 : ω ≠ 0 := by
    rintro rfl
    norm_num at hω3
  have hωω : ω * ω + ω + 1 = 0 := by
    have h : (ω - 1) * (ω * ω + ω + 1) = 0 := by linear_combination hω3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hω1
    · exact h
  have hσ3 : ∀ x : K, σ (σ (σ x)) = x := fun x => iterate_three_apply_of_pow hσ x
  have hroot : σ ω ^ 3 = 1 := by rw [← map_pow, hω3, map_one]
  have hσω1 : σ ω ≠ 1 := fun h => hω1 (σ.injective (h.trans (map_one σ).symm))
  have hfac : (σ ω - 1) * ((σ ω - ω) * (σ ω - ω * ω)) = 0 := by
    linear_combination hroot - (σ ω - 1) * σ ω * hωω + (σ ω - 1) * hω3
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd (sub_eq_zero.mp h) hσω1
  rcases mul_eq_zero.mp h with h | h
  · exact sub_eq_zero.mp h
  · have h2 : σ ω = ω * ω := sub_eq_zero.mp h
    have h3 : σ (σ ω) = ω := by
      rw [h2, map_mul, h2]
      linear_combination ω * hω3
    have h4 := hσ3 ω
    rw [h3, h2] at h4
    have : ω * (ω - 1) = 0 := by linear_combination h4
    rcases mul_eq_zero.mp this with h5 | h5
    · exact absurd h5 hω0
    · exact absurd (sub_eq_zero.mp h5) hω1

section Elements

variable {F : Type} [Field F]

@[expose] def upper2 (F : Type) [Field F] : Multiplicative F →* SpecialLinearGroup (Fin 2) F where
  toFun t := ⟨!![1, Multiplicative.toAdd t; 0, 1], by simp [Matrix.det_fin_two_of]⟩
  map_one' := by
    apply Subtype.ext
    change !![(1 : F), Multiplicative.toAdd (1 : Multiplicative F); 0, 1] = 1
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  map_mul' s t := by
    apply Subtype.ext
    change !![(1 : F), Multiplicative.toAdd (s * t); 0, 1] =
      !![(1 : F), Multiplicative.toAdd s; 0, 1] * !![(1 : F), Multiplicative.toAdd t; 0, 1]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, add_comm]

theorem coe_upper2 (t : Multiplicative F) :
    ((upper2 F t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) =
      !![1, Multiplicative.toAdd t; 0, 1] :=
  rfl

@[expose] noncomputable def spRoot (F : Type) [Field F] : Multiplicative F →* StatedSp 2 F :=
  (lam 0).comp (upper2 F)

theorem coe_spRoot_apply (t : F) (x y : Fin 2 ⊕ Fin 2) :
    (((spRoot F (Multiplicative.ofAdd t) : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) x y =
      (1 : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) x y +
        if x = Sum.inl 0 ∧ y = Sum.inr 0 then t else 0 := by
  rw [spRoot, MonoidHom.comp_apply, coe_lam, coe_upper2]
  have hab : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0 := Sum.inl_ne_inr
  by_cases hx : x = Sum.inl 0
  · subst hx
    rw [pairMat_apply_fst]
    by_cases hy : y = Sum.inl 0
    · subst hy
      simp
    · by_cases hy' : y = Sum.inr 0
      · subst hy'
        simp [hab]
      · simp [hy, hy', Matrix.one_apply_ne (Ne.symm hy)]
  · by_cases hx' : x = Sum.inr 0
    · subst hx'
      rw [pairMat_apply_snd hab]
      by_cases hy : y = Sum.inl 0
      · subst hy
        simp [Matrix.one_apply_ne hab.symm]
      · by_cases hy' : y = Sum.inr 0
        · subst hy'
          simp [hab.symm]
        · simp [hy, hy', Matrix.one_apply_ne (Ne.symm hy')]
    · rw [pairMat_apply_of_ne hx hx']
      simp [hx]

theorem torusHom_mul_spRoot (τ : Fin 2 → Fˣ) (s : F) :
    SymplecticTorusWeyl.torusHom τ * spRoot F (Multiplicative.ofAdd s) =
      spRoot F (Multiplicative.ofAdd ((τ 0 : F) ^ 2 * s)) * SymplecticTorusWeyl.torusHom τ := by
  apply statedSp_ext
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [SymplecticTorusWeyl.coe_torusHom]
  ext x y
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal, coe_spRoot_apply, coe_spRoot_apply]
  by_cases hxy : x = Sum.inl 0 ∧ y = Sum.inr 0
  · obtain ⟨rfl, rfl⟩ := hxy
    have h0 : ((τ 0 : Fˣ) : F) ≠ 0 := Units.ne_zero _
    simp only [Sum.elim_inl, Sum.elim_inr, and_self, ↓reduceIte,
      Matrix.one_apply_ne (Sum.inl_ne_inr : (Sum.inl 0 : Fin 2 ⊕ Fin 2) ≠ Sum.inr 0), zero_add,
      Units.val_inv_eq_inv_val]
    field_simp
  · simp only [hxy, ↓reduceIte, add_zero]
    by_cases h : x = y
    · subst h
      simp
    · rw [Matrix.one_apply_ne h, mul_zero, zero_mul]

theorem fieldSp_spRoot (σ : F ≃+* F) (t : F) :
    fieldSp 2 F σ (spRoot F (Multiplicative.ofAdd t)) = spRoot F (Multiplicative.ofAdd (σ t)) := by
  apply statedSp_ext
  rw [coe_fieldSp]
  ext x y
  rw [Matrix.map_apply, coe_spRoot_apply, coe_spRoot_apply, map_add]
  congr 1
  · by_cases h : x = y
    · subst h
      simp
    · simp [Matrix.one_apply_ne h]
  · split_ifs <;> simp

theorem fieldSp_torusHom (σ : F ≃+* F) (τ : Fin 2 → Fˣ) :
    fieldSp 2 F σ (SymplecticTorusWeyl.torusHom τ) =
      SymplecticTorusWeyl.torusHom fun i => Units.map (σ : F →* F) (τ i) := by
  apply statedSp_ext
  rw [coe_fieldSp, SymplecticTorusWeyl.coe_torusHom, SymplecticTorusWeyl.coe_torusHom]
  ext x y
  rw [Matrix.map_apply]
  by_cases h : x = y
  · subst h
    rcases x with i | i <;> simp [Matrix.diagonal_apply_eq]
  · simp [Matrix.diagonal_apply_ne _ h]

theorem exists_eq_scalar_of_mem_spScalars {z : StatedSp 2 F} (hz : z ∈ spScalars 2 F) :
    ∃ c : F, ((z : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) =
      Matrix.scalar (Fin 2 ⊕ Fin 2) c := by
  rw [Subgroup.mem_subgroupOf, StatedScalars, MonoidHom.mem_range] at hz
  obtain ⟨c, hc⟩ := hz
  exact ⟨c, by rw [← hc, GeneralLinearGroup.coe_scalar]⟩

theorem eq_zero_of_spRoot_mem_spScalars {t : F}
    (h : spRoot F (Multiplicative.ofAdd t) ∈ spScalars 2 F) : t = 0 := by
  obtain ⟨c, hc⟩ := exists_eq_scalar_of_mem_spScalars h
  have h1 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inr 0)
  rw [coe_spRoot_apply] at h1
  simpa [Matrix.scalar_apply, Matrix.one_apply_ne Sum.inl_ne_inr] using h1

end Elements

section Witness

variable {F : Type} [Field F]

theorem eq_one_of_fieldAut_two_eq_one {τ : F ≃+* F} (h : fieldAut 2 F τ = 1) : τ = 1 := by
  apply RingEquiv.ext
  intro t
  have h1 := congrArg (fun φ : MulAut (StatedProj (StatedSp 2 F)) =>
    φ (proj 2 F (spRoot F (Multiplicative.ofAdd t)))) h
  simp only [MulAut.one_apply] at h1
  rw [fieldAut_proj, fieldSp_spRoot, proj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq] at h1
  rw [← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add] at h1
  have := eq_zero_of_spRoot_mem_spScalars h1
  show τ t = t
  linear_combination -this

theorem hasLocalWitness_fieldAut_sp4 [Finite F] [CharP F 2] (h3 : 3 ∣ Nat.card Fˣ)
    {σ : F ≃+* F} (hσ : σ ^ 3 = 1) : HasLocalWitness (fieldAut 2 F σ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ω, hωo⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 h3
  have hω3 : ω ^ 3 = 1 := by rw [← hωo, pow_orderOf_eq_one]
  have hω1 : ω ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hωo
    norm_num at hωo
  have hω3' : (ω : F) ^ 3 = 1 := by rw [← Units.val_pow_eq_pow_val, hω3, Units.val_one]
  have hω1' : (ω : F) ≠ 1 := fun h => hω1 (Units.ext h)
  have hσω : σ ω = ω := ringAut_fix_of_cube_root hσ hω3' hω1'
  have hσωu : Units.map (σ : F →* F) ω = ω := Units.ext hσω
  set τ₁ : Fin 2 → Fˣ := ![ω, 1] with hτ₁
  set τ₂ : Fin 2 → Fˣ := ![1, ω] with hτ₂
  have hστ₁ : (fun i => Units.map (σ : F →* F) (τ₁ i)) = τ₁ := by
    funext i
    fin_cases i
    · exact hσωu
    · exact map_one _
  have hστ₂ : (fun i => Units.map (σ : F →* F) (τ₂ i)) = τ₂ := by
    funext i
    fin_cases i
    · exact map_one _
    · exact hσωu
  set U : Subgroup (StatedProj (StatedSp 2 F)) := ((proj 2 F).comp (spRoot F)).range with hU
  have hmemU : ∀ t : F, proj 2 F (spRoot F (Multiplicative.ofAdd t)) ∈ U := fun t =>
    ⟨Multiplicative.ofAdd t, rfl⟩
  have hUform : ∀ u ∈ U, ∃ t : F, proj 2 F (spRoot F (Multiplicative.ofAdd t)) = u := by
    rintro _ ⟨t, rfl⟩
    exact ⟨Multiplicative.toAdd t, rfl⟩
  have hconjU : ∀ τ : Fin 2 → Fˣ, ∀ u ∈ U,
      proj 2 F (SymplecticTorusWeyl.torusHom τ) * u *
        (proj 2 F (SymplecticTorusWeyl.torusHom τ))⁻¹ ∈ U := by
    intro τ u hu
    obtain ⟨t, rfl⟩ := hUform u hu
    rw [← map_mul, ← map_inv, ← map_mul, torusHom_mul_spRoot, mul_inv_cancel_right]
    exact hmemU _
  have hscal : ∀ {τ : Fin 2 → Fˣ}, SymplecticTorusWeyl.torusHom τ ∈ spScalars 2 F →
      ((τ 0 : F) = τ 1 ∧ ((τ 1)⁻¹ : Fˣ) = (τ 1 : F)) := by
    intro τ hτ
    obtain ⟨c, hc⟩ := exists_eq_scalar_of_mem_spScalars hτ
    rw [SymplecticTorusWeyl.coe_torusHom] at hc
    have h0 := congrFun (congrFun hc (Sum.inl 0)) (Sum.inl 0)
    have h1 := congrFun (congrFun hc (Sum.inl 1)) (Sum.inl 1)
    have h2 := congrFun (congrFun hc (Sum.inr 1)) (Sum.inr 1)
    simp only [Matrix.diagonal_apply_eq, Matrix.scalar_apply, Sum.elim_inl,
      Sum.elim_inr] at h0 h1 h2
    exact ⟨h0.trans h1.symm, h2.trans h1.symm⟩
  refine ⟨proj 2 F (SymplecticTorusWeyl.torusHom τ₁), proj 2 F (SymplecticTorusWeyl.torusHom τ₂),
    U, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    hconjU τ₁, hconjU τ₂, ?_⟩
  · rw [fieldAut_proj, fieldSp_torusHom, hστ₁]
  · rw [fieldAut_proj, fieldSp_torusHom, hστ₂]
  · rw [← map_pow, ← map_pow]
    have : τ₁ ^ 3 = 1 := by
      funext i
      fin_cases i
      · exact hω3
      · exact one_pow 3
    rw [this, map_one, map_one]
  · rw [← map_pow, ← map_pow]
    have : τ₂ ^ 3 = 1 := by
      funext i
      fin_cases i
      · exact one_pow 3
      · exact hω3
    rw [this, map_one, map_one]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, mul_comm τ₁ τ₂]
  · intro h1
    have := hscal ((QuotientGroup.eq_one_iff _).mp h1)
    exact hω1' this.1
  · rintro ⟨k, hk⟩
    have hk' : proj 2 F (SymplecticTorusWeyl.torusHom (τ₁ ^ k)) =
        proj 2 F (SymplecticTorusWeyl.torusHom τ₂) := by
      rw [map_zpow, map_zpow]
      exact hk
    rw [proj, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, ← map_inv,
      ← map_mul] at hk'
    have h := hscal hk'
    have hτ1 : ((τ₁ ^ k)⁻¹ * τ₂) 1 = ω := by
      simp [hτ₁, hτ₂]
    rw [hτ1] at h
    apply hω1'
    have h2 : (ω : F) * ω = 1 :=
      calc (ω : F) * ω = ((ω⁻¹ : Fˣ) : F) * ω := by rw [h.2]
        _ = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    linear_combination hω3' - (ω : F) * h2
  · rintro ⟨u, hu⟩
    refine ⟨1, ?_⟩
    obtain ⟨t, rfl⟩ := hUform u hu
    apply Subtype.ext
    rw [pow_one, pow_two, Subgroup.coe_mul, ← map_mul (proj 2 F), ← map_mul (spRoot F),
      ← ofAdd_add, CharTwo.add_self_eq_zero, ofAdd_zero, map_one, map_one, Subgroup.coe_one]
  · intro hU1
    have h1 : proj 2 F (spRoot F (Multiplicative.ofAdd (1 : F))) = 1 := by
      have := hmemU (1 : F)
      rw [hU1, Subgroup.mem_bot] at this
      exact this
    exact one_ne_zero (eq_zero_of_spRoot_mem_spScalars ((QuotientGroup.eq_one_iff _).mp h1))
  · intro u hu
    obtain ⟨t, rfl⟩ := hUform u hu
    rw [fieldAut_proj, fieldSp_spRoot]
    exact hmemU _

end Witness

section Exclusion

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem false_of_inducesKindPSp4Even_field_even (hG : SectionFourHyp G)
    (h3 : 3 ∣ Nat.card (Subgroup.center G)) {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : Even n) {a : G} (ha3 : a ^ 3 = 1)
    (hout : InducesOuterTheta a L) (hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥)
    {e : L ⧸ aschbacherSolvableCore 3 L ≃* StatedProj (StatedSp 2 F)}
    (h : InducesKind L (stdPinnedPSp4Even F) e a .field) : False := by
  obtain ⟨ha, hf⟩ := id h
  have hτ3 := inducedAutHom_pow_eq_one L e ha ha3
  obtain ⟨φ, ⟨σ, rfl⟩, -, d, -, hτ⟩ := hf
  have hφ3 : fieldAut 2 F σ ^ 3 = 1 := by
    have h1 : (d * fieldAut 2 F σ * d⁻¹) ^ 3 = d * fieldAut 2 F σ ^ 3 * d⁻¹ := conj_pow
    rw [← hτ, hτ3] at h1
    calc fieldAut 2 F σ ^ 3 = d⁻¹ * (d * fieldAut 2 F σ ^ 3 * d⁻¹) * d := by group
      _ = 1 := by rw [← h1]; group
  have hσ3 : σ ^ 3 = 1 := by
    rw [← map_pow] at hφ3
    exact eq_one_of_fieldAut_two_eq_one hφ3
  have h3F : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    obtain ⟨k, rfl⟩ := hn
    have h4 : (2 : ℕ) ^ (k + k) = 4 ^ k := by rw [← two_mul, pow_mul]; norm_num
    rw [h4]
    have h := Nat.ModEq.pow k (show 4 ≡ 1 [MOD 3] by decide)
    rw [one_pow] at h
    exact (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by norm_num))).mp h.symm
  have hw : HasLocalWitness (inducedAutHom L e ⟨a, ha⟩) := by
    rw [hτ]
    exact (hasLocalWitness_fieldAut_sp4 h3F hσ3).conj d
  exact false_of_hasLocalWitness_inducedAutHom hG h3 ha3 hout hZ e fun _ => hw

end Exclusion

end CFSG.RankThree.PartTwo.Sec4
