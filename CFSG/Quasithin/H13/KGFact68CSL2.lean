module

public import CFSG.Quasithin.H13.KGFact68CSTrans
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115EvenL2
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.QuasithinUnique.Ch1 CFSG.ProperTwoGeneratedCore.LocalCriterionSquareField
open scoped MatrixGroups

section Matrices

variable {F : Type} [Field F]

@[expose] def sl2Diag (μ : Fˣ) : SL(2, F) :=
  ⟨!![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two_of]⟩

theorem sl2Diag_coe (μ : Fˣ) :
    (sl2Diag μ : Matrix (Fin 2) (Fin 2) F) = !![(μ : F), 0; 0, ((μ⁻¹ : Fˣ) : F)] :=
  rfl

@[expose] def sl2DiagHom : Fˣ →* SL(2, F) where
  toFun := sl2Diag
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [sl2Diag_coe]
  map_mul' μ ν := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [sl2Diag_coe, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem sl2DiagHom_apply (μ : Fˣ) : sl2DiagHom μ = sl2Diag μ :=
  rfl

theorem sl2DiagHom_injective : Function.Injective (sl2DiagHom (F := F)) := by
  intro μ ν h
  have h1 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 0) h
  simp only [sl2DiagHom_apply, sl2Diag_coe] at h1
  exact Units.ext (by simpa using h1)

theorem sl2Diag_mul_elation (μ : Fˣ) (t : F) :
    sl2Diag μ * sl2Elation t = sl2Elation ((μ : F) ^ 2 * t) * sl2Diag μ := by
  have hμ : (μ : F) * (μ : F)⁻¹ = 1 := mul_inv_cancel₀ μ.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diag_coe, sl2Elation_coe, Matrix.mul_apply, Fin.sum_univ_two,
      Units.val_inv_eq_inv_val]
  linear_combination (-((μ : F) * t)) * hμ

theorem upper_mul_elation {h : SL(2, F)} (h10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (s : F) :
    h * sl2Elation s = sl2Elation ((h : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2 * s) * h := by
  have hdet := Matrix.det_fin_two (h : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.SpecialLinearGroup.det_coe, h10, mul_zero, sub_zero] at hdet
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Elation_coe, Matrix.mul_apply, Fin.sum_univ_two, h10]
  linear_combination ((h : Matrix (Fin 2) (Fin 2) F) 0 0 * s) * hdet

theorem upper_mul_diag {h : SL(2, F)} (h10 : (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0) (μ : Fˣ) :
    h * sl2Diag μ = sl2Elation ((h : Matrix (Fin 2) (Fin 2) F) 0 0 *
      (h : Matrix (Fin 2) (Fin 2) F) 0 1 * (1 - (μ : F) ^ 2)) * sl2Diag μ * h := by
  have hdet := Matrix.det_fin_two (h : Matrix (Fin 2) (Fin 2) F)
  rw [Matrix.SpecialLinearGroup.det_coe, h10, mul_zero, sub_zero] at hdet
  have hμ : (μ : F) * (μ : F)⁻¹ = 1 := mul_inv_cancel₀ μ.ne_zero
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2Diag_coe, sl2Elation_coe, Matrix.mul_apply, Fin.sum_univ_two, h10,
      Units.val_inv_eq_inv_val]
  · ring
  · linear_combination ((h : Matrix (Fin 2) (Fin 2) F) 0 1 * (1 - (μ : F) ^ 2) * (μ : F)⁻¹) * hdet +
      ((h : Matrix (Fin 2) (Fin 2) F) 0 1 * (μ : F)) * hμ
  · ring

theorem sl2Diag_map (σ : RingAut F) (μ : Fˣ) :
    Matrix.SpecialLinearGroup.map σ.toRingHom (sl2Diag μ) =
      sl2Diag (Units.map σ.toRingHom.toMonoidHom μ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Diag_coe, Matrix.SpecialLinearGroup.map_apply_coe]

theorem sl2Elation_injective : Function.Injective (sl2Elation (F := F)) := by
  intro s t h
  have h1 := congrArg (fun g : SL(2, F) => (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
  simpa [sl2Elation_coe] using h1

theorem sl2Elation_zero : sl2Elation (0 : F) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2Elation_coe]

end Matrices

section Main

variable {F : Type} [Field F] [Finite F]

@[expose] def sl2U : Subgroup SL(2, F) := (elationHom (F := F)).range

omit [Finite F] in
theorem mem_sl2U {g : SL(2, F)} : g ∈ (sl2U : Subgroup SL(2, F)) ↔ ∃ t : F, sl2Elation t = g := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.toAdd t, rfl⟩
  · rintro ⟨t, rfl⟩
    exact ⟨Multiplicative.ofAdd t, rfl⟩

omit [Finite F] in
theorem sl2Elation_mem (t : F) : sl2Elation t ∈ (sl2U : Subgroup SL(2, F)) :=
  mem_sl2U.mpr ⟨t, rfl⟩

omit [Finite F] in
theorem card_sl2U : Nat.card (sl2U : Subgroup SL(2, F)) = Nat.card F := by
  have hinj : Function.Injective (elationHom (F := F)) := fun s t h =>
    Multiplicative.toAdd.injective (sl2Elation_injective h)
  rw [sl2U, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  exact Nat.card_congr Multiplicative.toAdd

variable {n : ℕ}

theorem card_sl2U_eq (hcard : Nat.card F = 2 ^ n) :
    Nat.card (sl2U : Subgroup SL(2, F)) = 2 ^ (Nat.card SL(2, F)).factorization 2 := by
  rw [card_sl2U, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hcard]
  have hn : 1 ≤ n := by
    rcases n with _ | n
    · have := Finite.one_lt_card (α := F)
      rw [hcard] at this
      simp at this
    · omega
  set m := (2 ^ n) ^ 2 with hm
  have h2m : 2 ∣ m := dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hodd : ¬ 2 ∣ m - 1 := by omega
  rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, Nat.Prime.factorization_self Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd hodd]
  simp

@[expose] noncomputable def sl2USylow (hcard : Nat.card F = 2 ^ n) : Sylow 2 SL(2, F) :=
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  Sylow.ofCard sl2U (card_sl2U_eq hcard)

theorem sl2USylow_coe (hcard : Nat.card F = 2 ^ n) :
    ((sl2USylow hcard : Sylow 2 SL(2, F)) : Subgroup SL(2, F)) = sl2U :=
  Sylow.coe_ofCard _ _

theorem cartanSingerCover_sl2 (hcard : Nat.card F = 2 ^ n) : CartanSingerCover SL(2, F) := by
  classical
  have : CharP F 2 := char_two_of_card hcard
  refine cartanSingerCover_of_sylow (sl2USylow hcard) fun 𝓡 G hG => ?_
  rw [sl2USylow_coe] at hG ⊢
  have hdesc : ∀ ρ ∈ 𝓡, ∃ h : SL(2, F), (h : Matrix (Fin 2) (Fin 2) F) 1 0 = 0 ∧
      ∀ g, ρ g = h * Matrix.SpecialLinearGroup.map (mulAutToRingAut hcard ρ).toRingHom g * h⁻¹ := by
    intro ρ hρ
    obtain ⟨a, rfl⟩ := (gammaToMulAut_bijective_of_card hcard).2 ρ
    refine ⟨a.left, ?_, fun g => by rw [gammaToMulAut_apply, mulAutToRingAut_gammaToMulAut]⟩
    have h1 := hG.normalizes _ hρ _ (sl2Elation_mem (a.right.symm 1))
    rw [gammaToMulAut_apply, sl2Elation_map, RingEquiv.apply_symm_apply, mem_sl2U] at h1
    obtain ⟨t, ht⟩ := h1
    have h2 : a.left * sl2Elation 1 = sl2Elation t * a.left := by
      rw [ht]
      group
    have := (elation_commute_entries a.left 1 t h2).2.2
    simpa using this
  have hU : ∀ ρ ∈ 𝓡, ∃ c : F, c ≠ 0 ∧ ∀ t, ρ (sl2Elation t) =
      sl2Elation (c * mulAutToRingAut hcard ρ t) := by
    intro ρ hρ
    obtain ⟨h, h10, hρg⟩ := hdesc ρ hρ
    have hdet := Matrix.det_fin_two (h : Matrix (Fin 2) (Fin 2) F)
    rw [Matrix.SpecialLinearGroup.det_coe, h10, mul_zero, sub_zero] at hdet
    refine ⟨(h : Matrix (Fin 2) (Fin 2) F) 0 0 ^ 2, pow_ne_zero 2 fun h0 => ?_, fun t => ?_⟩
    · rw [h0, zero_mul] at hdet
      exact one_ne_zero hdet
    · rw [hρg, sl2Elation_map, upper_mul_elation h10, mul_inv_cancel_right]
  let F0 : Subgroup Fˣ :=
    { carrier := {μ | ∀ ρ ∈ 𝓡, mulAutToRingAut hcard ρ (μ : F) = μ}
      mul_mem' := fun ha hb ρ hρ => by simp [ha ρ hρ, hb ρ hρ]
      one_mem' := fun ρ hρ => by simp
      inv_mem' := fun ha ρ hρ => by simp [ha ρ hρ] }
  obtain ⟨μ₀, hμ₀⟩ := IsCyclic.exists_generator (α := F0)
  have hcardF0 : orderOf μ₀ = Nat.card F0 := orderOf_eq_card_of_forall_mem_zpowers hμ₀
  have hord : orderOf (sl2Diag (μ₀ : Fˣ)) = orderOf μ₀ := by
    rw [← sl2DiagHom_apply, orderOf_injective _ sl2DiagHom_injective, Subgroup.orderOf_coe]
  have hodd : Odd (orderOf μ₀) := by
    have h1 : orderOf (μ₀ : Fˣ) ∣ Nat.card Fˣ := orderOf_dvd_natCard _
    rw [Subgroup.orderOf_coe] at h1
    have h2 : Nat.card F = Nat.card Fˣ + 1 := Nat.card_eq_card_units_add_one F
    have h3 : Odd (Nat.card Fˣ) := by
      have hn : n ≠ 0 := by
        rintro rfl
        have := Finite.one_lt_card (α := F)
        rw [hcard] at this
        simp at this
      have h4 : Even (Nat.card F) := by
        rw [hcard]
        exact (Nat.even_pow' hn).mpr even_two
      rw [h2] at h4
      exact Nat.odd_iff.mpr (by rcases h4 with ⟨k, hk⟩; omega)
    exact h3.of_dvd_nat h1
  have hμ₀fix : ∀ ρ ∈ 𝓡, mulAutToRingAut hcard ρ ((μ₀ : Fˣ) : F) = ((μ₀ : Fˣ) : F) :=
    fun ρ hρ => μ₀.2 ρ hρ
  refine ⟨sl2Diag (μ₀ : Fˣ), ?_, by rw [hord]; exact hodd, ?_, ?_⟩
  ·
    refine CFSG.Quasithin.A4.mem_normalizer_of_conj_mem fun g hg => ?_
    obtain ⟨t, rfl⟩ := mem_sl2U.mp hg
    rw [sl2Diag_mul_elation, mul_inv_cancel_right]
    exact sl2Elation_mem _
  ·
    intro ρ hρ
    obtain ⟨h, h10, hρg⟩ := hdesc ρ hρ
    have hσ : Units.map (mulAutToRingAut hcard ρ).toRingHom.toMonoidHom (μ₀ : Fˣ) = μ₀ :=
      Units.ext (by simpa using hμ₀fix ρ hρ)
    rw [hρg, sl2Diag_map, hσ]
    have h2 : h * sl2Diag (μ₀ : Fˣ) * h⁻¹ * (sl2Diag (μ₀ : Fˣ))⁻¹ =
        sl2Elation ((h : Matrix (Fin 2) (Fin 2) F) 0 0 * (h : Matrix (Fin 2) (Fin 2) F) 0 1 *
          (1 - ((μ₀ : Fˣ) : F) ^ 2)) := by
      rw [upper_mul_diag h10]
      group
    rw [h2]
    exact sl2Elation_mem _
  ·
    intro hxG j
    have hGU : ∀ g ∈ G, ∃ t, sl2Elation t = g := fun g hg => mem_sl2U.mp (hG.le g hg).1
    obtain ⟨t₀, ht₀G, ht₀⟩ : ∃ t₀ : F, sl2Elation t₀ ∈ G ∧ t₀ ≠ 0 := by
      have h1 : 1 < Nat.card G := by have := hG.four_le; omega
      have := Finite.one_lt_card_iff_nontrivial.mp h1
      obtain ⟨g, hg1⟩ := exists_ne (1 : ↥G)
      obtain ⟨t, ht⟩ := hGU g g.2
      refine ⟨t, ht ▸ g.2, fun h0 => hg1 (Subtype.ext ?_)⟩
      rw [← ht, h0, sl2Elation_zero]
      rfl
    have hquot : ∀ t, sl2Elation t ∈ G → ∀ ρ ∈ 𝓡,
        mulAutToRingAut hcard ρ (t / t₀) = t / t₀ := by
      intro t ht ρ hρ
      obtain ⟨c, hc, hρU⟩ := hU ρ hρ
      have e1 := hG.fixed ρ hρ _ ht
      have e2 := hG.fixed ρ hρ _ ht₀G
      rw [hρU] at e1 e2
      have e1' := sl2Elation_injective e1
      have e2' := sl2Elation_injective e2
      rw [map_div₀]
      have hσ0 : mulAutToRingAut hcard ρ t₀ ≠ 0 := by
        intro h0
        rw [h0, mul_zero] at e2'
        exact ht₀ e2'.symm
      field_simp
      linear_combination (mulAutToRingAut hcard ρ t₀) * e1' - (mulAutToRingAut hcard ρ t) * e2'
    have hxpow : ∀ (k : ℕ) (t : F), sl2Diag (μ₀ : Fˣ) ^ k * sl2Elation t =
        sl2Elation ((((μ₀ : Fˣ) : F) ^ 2) ^ k * t) * sl2Diag (μ₀ : Fˣ) ^ k := by
      intro k t
      rw [← sl2DiagHom_apply, ← map_pow, sl2DiagHom_apply, sl2Diag_mul_elation,
        Units.val_pow_eq_pow_val, ← pow_mul, ← pow_mul, mul_comm 2 k]
    have hstab : ∀ (k : ℕ) (t : F), sl2Elation t ∈ G →
        sl2Elation ((((μ₀ : Fˣ) : F) ^ 2) ^ k * t) ∈ G := by
      intro k t ht
      induction k with
      | zero => simpa using ht
      | succ k ih =>
        have h1 := hxG _ ih
        rw [sl2Diag_mul_elation, mul_inv_cancel_right] at h1
        convert h1 using 2
        ring
    have hgen : ∀ ν : F0, ∃ k : ℕ, ν = (μ₀ ^ 2) ^ k := by
      intro ν
      obtain ⟨k, hk⟩ := mem_powers_iff_mem_zpowers.mpr (hμ₀ ν)
      dsimp only at hk
      obtain ⟨m, hm⟩ := id hodd
      refine ⟨k * (m + 1), ?_⟩
      rw [← hk, ← pow_mul, show 2 * (k * (m + 1)) = (orderOf μ₀ + 1) * k by rw [hm]; ring,
        pow_mul, pow_succ, pow_orderOf_eq_one, one_mul]
    have hGcard : Nat.card G = Nat.card F0 + 1 := by
      let φ : Option F0 → G := fun o => match o with
        | none => 1
        | some ν => ⟨sl2Elation (t₀ * ((ν : Fˣ) : F)), by
            obtain ⟨k, rfl⟩ := hgen ν
            have := hstab k t₀ ht₀G
            convert this using 2
            simp [mul_comm]⟩
      have hφ : Function.Bijective φ := by
        constructor
        · rintro (_ | ν) (_ | ν') h
          · rfl
          · exfalso
            have h1 := congrArg Subtype.val h
            simp only [φ, OneMemClass.coe_one] at h1
            have h2 := sl2Elation_injective (sl2Elation_zero.trans h1)
            exact (mul_ne_zero ht₀ (ν' : Fˣ).ne_zero) h2.symm
          · exfalso
            have h1 := congrArg Subtype.val h
            simp only [φ, OneMemClass.coe_one] at h1
            have h2 := sl2Elation_injective (h1.trans sl2Elation_zero.symm)
            exact (mul_ne_zero ht₀ (ν : Fˣ).ne_zero) h2
          · have h1 := sl2Elation_injective (congrArg Subtype.val h)
            have h2 := mul_left_cancel₀ ht₀ h1
            exact congrArg some (Subtype.ext (Units.ext h2))
        · rintro ⟨g, hg⟩
          obtain ⟨t, rfl⟩ := hGU g hg
          by_cases ht : t = 0
          · refine ⟨none, Subtype.ext ?_⟩
            simp [φ, ht, sl2Elation_zero]
          · refine ⟨some ⟨Units.mk0 (t / t₀) (div_ne_zero ht ht₀), fun ρ hρ => ?_⟩, ?_⟩
            · simpa using hquot t hg ρ hρ
            · apply Subtype.ext
              simp only [φ]
              congr 1
              simp
              field_simp
      rw [← Nat.card_congr (Equiv.ofBijective φ hφ), Finite.card_option]
    have hcomm : (∀ g ∈ G, sl2Diag (μ₀ : Fˣ) ^ j * g = g * sl2Diag (μ₀ : Fˣ) ^ j) ↔
        (((μ₀ : Fˣ) : F) ^ 2) ^ j = 1 := by
      constructor
      · intro h1
        have h2 := h1 _ ht₀G
        rw [hxpow] at h2
        have h3 := mul_right_cancel h2
        have h4 := sl2Elation_injective h3
        have h5 : ((((μ₀ : Fˣ) : F) ^ 2) ^ j - 1) * t₀ = 0 := by linear_combination h4
        exact sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right ht₀)
      · intro h1 g hg
        obtain ⟨t, rfl⟩ := hGU g hg
        rw [hxpow, h1, one_mul]
    rw [hcomm, hGcard, Nat.add_sub_cancel, ← hcardF0]
    have h1 : ((((μ₀ : Fˣ) : F) ^ 2) ^ j = 1) ↔ (μ₀ ^ (2 * j) = 1) := by
      rw [pow_mul]
      constructor
      · intro h
        apply Subtype.ext
        apply Units.ext
        simpa using h
      · intro h
        have := congrArg (fun ν : F0 => ((ν : Fˣ) : F)) h
        simpa using this
    rw [h1, orderOf_dvd_iff_pow_eq_one.symm]
    exact (Nat.Coprime.dvd_mul_left (Nat.coprime_comm.mp (Nat.coprime_two_left.mpr hodd)))

end Main

theorem cartanSingerCover_of_stated_psl_two {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 2 f) : CartanSingerCover X := by
  obtain ⟨-, K, _, hfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := char_two_of_card hcard
  exact CartanSingerCover.of_mulEquiv
    ((e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm).trans
      sl2EquivPSL2.symm) (cartanSingerCover_sl2 hcard)

end CFSG.Quasithin.H13.KG68
