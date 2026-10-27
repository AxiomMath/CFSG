module

public import CFSG.Quasithin.Background.F918P0

public section

namespace CFSG.Quasithin.H13.L1233

open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped Matrix Pointwise

section Model

variable {F : Type} [Field F]

@[expose] def uMat (F : Type) [Field F] : Matrix (Fin 2) (Fin 2) F := !![1, 1; 0, 1]

theorem uMat_mul_self (h2 : (2 : F) = 0) : uMat F * uMat F = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two, one_add_one_eq_two, h2]

@[expose] def uGL (h2 : (2 : F) = 0) : GL (Fin 2) F :=
  ⟨uMat F, uMat F, uMat_mul_self h2, uMat_mul_self h2⟩

theorem uGL_sq (h2 : (2 : F) = 0) : uGL h2 * uGL h2 = 1 :=
  Units.ext (uMat_mul_self h2)

theorem det_uGL (h2 : (2 : F) = 0) :
    ((uGL h2 : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).det = 1 := by
  simp [uGL, uMat, Matrix.det_fin_two]

theorem eq_of_fix {X Y : Matrix (Fin 2) (Fin 2) F} (hX1 : uMat F * X = X) (hX2 : X * (uMat F)ᵀ = X)
    (hY1 : uMat F * Y = Y) (hY2 : Y * (uMat F)ᵀ = Y) (h : X 0 0 = Y 0 0) : X = Y := by
  have key : ∀ Z : Matrix (Fin 2) (Fin 2) F, uMat F * Z = Z → Z * (uMat F)ᵀ = Z →
      Z 1 0 = 0 ∧ Z 1 1 = 0 ∧ Z 0 1 = 0 := by
    intro Z h1 h2
    have e1 := congrFun (congrFun h1 0) 0
    have e2 := congrFun (congrFun h1 0) 1
    have e3 := congrFun (congrFun h2 0) 0
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
    refine ⟨e1, e2, ?_⟩
    have e4 := congrFun (congrFun h2 1) 0
    simp [uMat, Matrix.mul_apply, Fin.sum_univ_two] at e4
    exact e3
  obtain ⟨x1, x2, x3⟩ := key X hX1 hX2
  obtain ⟨y1, y2, y3⟩ := key Y hY1 hY2
  ext i j
  fin_cases i <;> fin_cases j
  · exact h
  · simp [x3, y3]
  · simp [x1, y1]
  · simp [x2, y2]

abbrev tMat (x : (FFModel.tensorNat 2 F).Amb) : Matrix (Fin 2) (Fin 2) F :=
  Multiplicative.toAdd x

theorem tMat_act (g h : ↥(StatedSL 2 F)) (x : (FFModel.tensorNat 2 F).Amb) :
    tMat ((FFModel.tensorNat 2 F).act (g, h) x) =
      ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * tMat x *
        ((h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)ᵀ :=
  rfl

theorem tMat_injective : Function.Injective (tMat (F := F)) :=
  Multiplicative.toAdd.injective

end Model

section Omega

variable {W : Type*} [CommGroup W]

theorem card_fix_le_of_omega4 {X S : Subgroup (MulAut W)} (hX : Nat.card X = 3600)
    (hO : Omega4PlusModule X 2) (hSX : S ≤ X) (hS : Nat.card S = 16) :
    Nat.card {w : W // ∀ f ∈ S, f w = w} ≤ 4 := by
  obtain ⟨F, _, _, hF4, π, hπs, -, -, -, -, -, -, β, hβs, hβk, hβi⟩ := hO
  have h2 : (2 : F) = 0 := by
    have : Fintype F := Fintype.ofFinite F
    have h := FiniteField.cast_card_eq_zero F
    rw [Fintype.card_eq_nat_card, hF4] at h
    have h4 : (2 : F) * 2 = 0 := by norm_num at h ⊢; exact h
    exact mul_self_eq_zero.1 h4
  set ut : ↥(StatedSL 2 F) := ⟨uGL h2, Subgroup.subset_closure (det_uGL h2)⟩ with hut
  have hut2 : ut * ut = 1 := Subtype.ext (uGL_sq h2)
  have hutM : ((ut : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) = uMat F := rfl
  have hpu : IsPGroup 2 ↥(Subgroup.zpowers ut) := by
    have h1 : orderOf ut ∣ 2 ^ 1 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_one, pow_two]; exact hut2)
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hk])
  let π' : ↥(StatedSL 2 F) × ↥(StatedSL 2 F) →* ↥X := π
  set E : Subgroup (↥(StatedSL 2 F) × ↥(StatedSL 2 F)) :=
    (Subgroup.zpowers ut).prod (Subgroup.zpowers ut) with hE
  have hEp : IsPGroup 2 ↥E := by
    obtain ⟨i, hi⟩ := hpu.exists_card_eq
    exact IsPGroup.of_card (n := i + i) (by
      rw [hE, Nat.card_congr (Subgroup.prodEquiv _ _).toEquiv, Nat.card_prod, hi, pow_add])
  have hγ₁ : ((ut, 1) : ↥(StatedSL 2 F) × ↥(StatedSL 2 F)) ∈ E :=
    Subgroup.mem_prod.2 ⟨Subgroup.mem_zpowers ut, Subgroup.one_mem _⟩
  have hγ₂ : ((1, ut) : ↥(StatedSL 2 F) × ↥(StatedSL 2 F)) ∈ E :=
    Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, Subgroup.mem_zpowers ut⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hS' : Nat.card ↥(S.subgroupOf X) = 2 ^ (Nat.card ↥X).factorization 2 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSX).toEquiv, hS, hX]
    have hne : (3600 : ℕ) ≠ 0 := by norm_num
    have h1 := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).1
      (show 2 ^ 4 ∣ 3600 by norm_num)
    have h2' : ¬ 5 ≤ (3600 : ℕ).factorization 2 := fun h5 => by
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hne).2 h5
      norm_num at this
    have : (3600 : ℕ).factorization 2 = 4 := by omega
    rw [this]
    norm_num
  set SS : Sylow 2 ↥X := Sylow.ofCard _ hS'
  obtain ⟨Q₀, hQ₀⟩ := (hEp.map π').exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥X SS Q₀
  have hconj : ∀ γ ∈ E, ((g⁻¹ * π' γ * g : ↥X) : MulAut W) ∈ S := by
    intro γ hγ
    have h1 : π' γ ∈ MulAut.conj g • (SS : Subgroup ↥X) := by
      rw [← Sylow.coe_subgroup_smul, hg]
      exact hQ₀ (Subgroup.mem_map_of_mem π' hγ)
    rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, MulAut.smul_def,
      MulAut.conj_inv_apply] at h1
    exact Subgroup.mem_subgroupOf.1 h1
  have hfix : ∀ γ ∈ E, ∀ w : W, (∀ f ∈ S, f w = w) →
      ((π' γ : ↥X) : MulAut W) ((g : MulAut W) w) = (g : MulAut W) w := by
    intro γ hγ w hw
    have h1 := hw _ (hconj γ hγ)
    have e : ((π' γ : ↥X) : MulAut W) = (g : MulAut W) * ((g⁻¹ * π' γ * g : ↥X) : MulAut W) *
        (g : MulAut W)⁻¹ := by
      simp [mul_assoc]
    rw [e, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, h1]
  have hmodel : ∀ γ : ↥(StatedSL 2 F) × ↥(StatedSL 2 F),
      ∀ (w : W) (m : ↥(FFModel.tensorNat 2 F).sec),
      ((π' γ : ↥X) : MulAut W) w = w → β ⟨w, Subgroup.mem_top w⟩ = QuotientGroup.mk m →
      (FFModel.tensorNat 2 F).act γ (m : (FFModel.tensorNat 2 F).Amb) = m := by
    intro γ w m hw hm
    have h1 := hβi γ ⟨w, Subgroup.mem_top w⟩ m (Subgroup.mem_top _) (Subgroup.mem_top _) hm
    have e : (⟨((π γ : ↥X) : MulAut W) w, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
        ⟨w, Subgroup.mem_top w⟩ := Subtype.ext hw
    rw [e, hm, QuotientGroup.eq] at h1
    have h3 := Subgroup.mem_bot.1 (Subgroup.mem_subgroupOf.1 h1)
    rw [Subgroup.coe_mul, Subgroup.coe_inv] at h3
    exact (inv_mul_eq_one.1 h3).symm
  classical
  let rep : W → ↥(FFModel.tensorNat 2 F).sec := fun w =>
    Classical.choose (QuotientGroup.mk_surjective (β ⟨(g : MulAut W) w, Subgroup.mem_top _⟩))
  have hrep : ∀ w, (QuotientGroup.mk (rep w) : _ ⧸ _) =
      β ⟨(g : MulAut W) w, Subgroup.mem_top _⟩ :=
    fun w => Classical.choose_spec (QuotientGroup.mk_surjective _)
  have hmat : ∀ w : W, (∀ f ∈ S, f w = w) →
      uMat F * tMat (rep w : (FFModel.tensorNat 2 F).Amb) =
        tMat (rep w : (FFModel.tensorNat 2 F).Amb) ∧
      tMat (rep w : (FFModel.tensorNat 2 F).Amb) * (uMat F)ᵀ =
        tMat (rep w : (FFModel.tensorNat 2 F).Amb) := by
    intro w hw
    have h1 := congrArg tMat (hmodel _ _ (rep w) (hfix _ hγ₁ w hw) (hrep w).symm)
    have h2 := congrArg tMat (hmodel _ _ (rep w) (hfix _ hγ₂ w hw) (hrep w).symm)
    rw [tMat_act, hutM] at h1 h2
    refine ⟨?_, ?_⟩
    · simpa using h1
    · simpa using h2
  have hinj : Function.Injective fun w : {w : W // ∀ f ∈ S, f w = w} =>
      tMat (rep w.1 : (FFModel.tensorNat 2 F).Amb) 0 0 := by
    rintro ⟨w₁, hw₁⟩ ⟨w₂, hw₂⟩ h
    obtain ⟨a1, a2⟩ := hmat w₁ hw₁
    obtain ⟨b1, b2⟩ := hmat w₂ hw₂
    have he := eq_of_fix a1 a2 b1 b2 h
    have hr : rep w₁ = rep w₂ := Subtype.ext (tMat_injective he)
    have hb : β ⟨(g : MulAut W) w₁, Subgroup.mem_top _⟩ =
        β ⟨(g : MulAut W) w₂, Subgroup.mem_top _⟩ := by
      rw [← hrep, ← hrep, hr]
    have hb' : β (⟨(g : MulAut W) w₁, Subgroup.mem_top _⟩⁻¹ *
        ⟨(g : MulAut W) w₂, Subgroup.mem_top _⟩) = 1 := by
      rw [map_mul, map_inv, hb, inv_mul_cancel]
    have h1 := (hβk _).1 hb'
    rw [Subgroup.mem_bot, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    exact Subtype.ext ((g : MulAut W).injective (inv_mul_eq_one.1 h1))
  calc Nat.card {w : W // ∀ f ∈ S, f w = w} ≤ Nat.card F := Nat.card_le_card_of_injective _ hinj
    _ = 4 := hF4

end Omega

end CFSG.Quasithin.H13.L1233
