module

public import CFSG.Quasithin.Vol2.Ch11SecS12Q

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Vol2.Ch11.SecS.C11P9A
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SteinbergBR.BlockPar
open Matrix
open scoped MatrixGroups

variable {F : Type} [Field F] [CharP F 2]

abbrev trM {i j : Fin 3} (hij : i ≠ j) : Matrix (Fin 3) (Fin 3) F :=
  ((tr3 hij (1 : F) : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)

theorem decomp_zero (M : Matrix (Fin 3) (Fin 3) F) (htr : M.trace = 0) (h10 : M 1 0 = 0)
    (h20 : M 2 0 = 0) :
    ∃ A B : Matrix (Fin 3) (Fin 3) F, A.trace = 0 ∧ B.trace = 0 ∧
      M = (trM (by decide : (0 : Fin 3) ≠ 1) * A * trM (by decide : (0 : Fin 3) ≠ 1) - A) +
        (trM (by decide : (0 : Fin 3) ≠ 2) * B * trM (by decide : (0 : Fin 3) ≠ 2) - B) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.trace_fin_three] at htr
  refine ⟨!![0, 0, 0; M 1 1, M 0 1 + M 1 1, 0; M 2 1, 0, M 0 1 + M 1 1],
    !![0, 0, 0; M 1 2, M 0 2 + M 2 2, 0; M 2 2, 0, M 0 2 + M 2 2], ?_, ?_, ?_⟩
  · simp [Matrix.trace_fin_three]
    linear_combination (M 0 1 + M 1 1) * h2
  · simp [Matrix.trace_fin_three]
    linear_combination (M 0 2 + M 2 2) * h2
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, tr3_apply, h10, h20]
    all_goals first
      | linear_combination htr - (M 1 1 + M 2 2) * h2
      | linear_combination -(M 1 1) * h2
      | linear_combination -(M 2 2) * h2

theorem decomp_one (M : Matrix (Fin 3) (Fin 3) F) (htr : M.trace = 0) (h20 : M 2 0 = 0)
    (h21 : M 2 1 = 0) :
    ∃ A B : Matrix (Fin 3) (Fin 3) F, A.trace = 0 ∧ B.trace = 0 ∧
      M = (trM (by decide : (0 : Fin 3) ≠ 2) * A * trM (by decide : (0 : Fin 3) ≠ 2) - A) +
        (trM (by decide : (1 : Fin 3) ≠ 2) * B * trM (by decide : (1 : Fin 3) ≠ 2) - B) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [Matrix.trace_fin_three] at htr
  refine ⟨!![0, 0, 0; 0, M 0 2 + M 0 0, 0; M 0 0, M 0 1, M 0 2 + M 0 0],
    !![M 1 2 + M 1 1, 0, 0; 0, 0, 0; M 1 0, M 1 1, M 1 2 + M 1 1], ?_, ?_, ?_⟩
  · simp [Matrix.trace_fin_three]
    linear_combination (M 0 2 + M 0 0) * h2
  · simp [Matrix.trace_fin_three]
    linear_combination (M 1 2 + M 1 1) * h2
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, tr3_apply, h20, h21]
    all_goals first
      | linear_combination -(M 0 0) * h2
      | linear_combination -(M 1 1) * h2
      | linear_combination htr - (M 0 0 + M 1 1) * h2

omit [CharP F 2] in
theorem conj_mul_self (g : GL (Fin 3) F) (M : Matrix (Fin 3) (Fin 3) F) :
    (g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
      (g : Matrix (Fin 3) (Fin 3) F) = (g : Matrix (Fin 3) (Fin 3) F) * M := by
  rw [Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.mul_one]

omit [CharP F 2] in
theorem head_zero {g : GL (Fin 3) F} (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h11 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 2)
    (M : Matrix (Fin 3) (Fin 3) F) {i : Fin 3} (hi : i ≠ 0) :
    ((g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i 0 =
      ((g : Matrix (Fin 3) (Fin 3) F) 1 1 / (g : Matrix (Fin 3) (Fin 3) F) 0 0) * M i 0 := by
  have h0 := g00_ne_zero h10 h20
  set X := (g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    with hX
  have e : (X * (g : Matrix (Fin 3) (Fin 3) F)) i 0 = ((g : Matrix (Fin 3) (Fin 3) F) * M) i 0 := by
    rw [hX, conj_mul_self]
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three, h10, h20] at e
  field_simp
  fin_cases i
  · exact absurd rfl hi
  · simp only [Fin.mk_one, Fin.isValue] at e ⊢
    rw [h10, h12] at e
    linear_combination e
  · simp only [Fin.reduceFinMk, Fin.isValue] at e ⊢
    rw [h20, h21, ← h11] at e
    linear_combination e

omit [CharP F 2] in
theorem head_one {g : GL (Fin 3) F} (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h01 : (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1)
    (M : Matrix (Fin 3) (Fin 3) F) {l : Fin 3} (hl : l ≠ 2) :
    ((g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) 2 l =
      ((g : Matrix (Fin 3) (Fin 3) F) 2 2 / (g : Matrix (Fin 3) (Fin 3) F) 0 0) * M 2 l := by
  have h0 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
    intro h
    have hdet : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
      rw [← GeneralLinearGroup.val_det_apply]
      exact Units.ne_zero _
    apply hdet
    rw [Matrix.det_fin_three, h, h20, h21, h10]
    ring
  set X := (g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
    with hX
  have e : (X * (g : Matrix (Fin 3) (Fin 3) F)) 2 l = ((g : Matrix (Fin 3) (Fin 3) F) * M) 2 l := by
    rw [hX, conj_mul_self]
  rw [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mul_apply, Fin.sum_univ_three, h20, h21] at e
  field_simp
  fin_cases l
  · simp only [Fin.zero_eta, Fin.isValue] at e ⊢
    rw [h10, h20] at e
    linear_combination e
  · simp only [Fin.mk_one, Fin.isValue] at e ⊢
    rw [h01, h21, ← h00] at e
    linear_combination e
  · exact absurd rfl hl

theorem sq_mk_eq_one_zero {g : GL (Fin 3) F} (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0) (h12 : (g : Matrix (Fin 3) (Fin 3) F) 1 2 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0)
    (h11 : (g : Matrix (Fin 3) (Fin 3) F) 1 1 = (g : Matrix (Fin 3) (Fin 3) F) 2 2)
    (h0 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1) :
    ProjGenLinGroup.mk g ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [← map_pow, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨(g : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 2, ?_⟩
  rw [show g ^ 2 = g * g from sq g, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, h10, h20, h12, h21]
  all_goals first
    | ring1
    | linear_combination (-(g : Matrix (Fin 3) (Fin 3) F) 0 1 *
        (g : Matrix (Fin 3) (Fin 3) F) 1 1) * h2 - (g : Matrix (Fin 3) (Fin 3) F) 0 1 * h0
    | linear_combination (-(g : Matrix (Fin 3) (Fin 3) F) 0 2 *
        (g : Matrix (Fin 3) (Fin 3) F) 2 2) * h2 - (g : Matrix (Fin 3) (Fin 3) F) 0 2 * h0 -
        (g : Matrix (Fin 3) (Fin 3) F) 0 2 * h11
    | linear_combination ((g : Matrix (Fin 3) (Fin 3) F) 0 0 +
        (g : Matrix (Fin 3) (Fin 3) F) 1 1) * h0
    | linear_combination ((g : Matrix (Fin 3) (Fin 3) F) 0 0 +
        (g : Matrix (Fin 3) (Fin 3) F) 2 2) * h0 + ((g : Matrix (Fin 3) (Fin 3) F) 0 0 +
        (g : Matrix (Fin 3) (Fin 3) F) 2 2) * h11

theorem sq_mk_eq_one_one {g : GL (Fin 3) F} (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h01 : (g : Matrix (Fin 3) (Fin 3) F) 0 1 = 0)
    (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0)
    (h00 : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1)
    (h22 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = (g : Matrix (Fin 3) (Fin 3) F) 0 0) :
    ProjGenLinGroup.mk g ^ 2 = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rw [← map_pow, ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.mem_center_iff_val_mem_range_scalar]
  refine ⟨(g : Matrix (Fin 3) (Fin 3) F) 0 0 ^ 2, ?_⟩
  rw [show g ^ 2 = g * g from sq g, Units.val_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, h20, h21, h01, h10]
  all_goals first
    | ring1
    | linear_combination (-(g : Matrix (Fin 3) (Fin 3) F) 0 2 *
        (g : Matrix (Fin 3) (Fin 3) F) 0 0) * h2 - (g : Matrix (Fin 3) (Fin 3) F) 0 2 * h22
    | linear_combination (-(g : Matrix (Fin 3) (Fin 3) F) 1 2 *
        (g : Matrix (Fin 3) (Fin 3) F) 1 1) * h2 - (g : Matrix (Fin 3) (Fin 3) F) 1 2 * h22 -
        (g : Matrix (Fin 3) (Fin 3) F) 1 2 * h00
    | linear_combination ((g : Matrix (Fin 3) (Fin 3) F) 0 0 +
        (g : Matrix (Fin 3) (Fin 3) F) 1 1) * h00
    | linear_combination (-((g : Matrix (Fin 3) (Fin 3) F) 0 0 +
        (g : Matrix (Fin 3) (Fin 3) F) 2 2)) * h22

section Head

variable {G : Type} [Group G] {V Z J Q : Subgroup G}
  (β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F))

theorem comm_mem_commutator {q a : G} (hq : q ∈ Q) (ha : a ∈ V) :
    q * a * q⁻¹ * a⁻¹ ∈ ⁅V, Q⁆ := by
  rw [Subgroup.commutator_comm, ← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hq ha

omit [CharP F 2] in
include β in
theorem mem_of_decomp (hβon : ∀ M : Matrix (Fin 3) (Fin 3) F, M.trace = 0 →
      ∃ v, Multiplicative.toAdd (β v) = M)
    (hβker : ∀ v, β v = 1 ↔ (v : G) ∈ Z) (hQV : Q ≤ Subgroup.normalizer (V : Set G))
    {U₁ U₂ : Matrix (Fin 3) (Fin 3) F}
    (hQ₁ : ∃ q ∈ Q, ∀ v w : ↥V, (w : G) = q * v * q⁻¹ →
      Multiplicative.toAdd (β w) = U₁ * Multiplicative.toAdd (β v) * U₁)
    (hQ₂ : ∃ q ∈ Q, ∀ v w : ↥V, (w : G) = q * v * q⁻¹ →
      Multiplicative.toAdd (β w) = U₂ * Multiplicative.toAdd (β v) * U₂)
    {v : ↥V} {A B : Matrix (Fin 3) (Fin 3) F} (hA : A.trace = 0) (hB : B.trace = 0)
    (hM : Multiplicative.toAdd (β v) = (U₁ * A * U₁ - A) + (U₂ * B * U₂ - B)) :
    (v : G) ∈ ⁅V, Q⁆ ⊔ Z := by
  obtain ⟨a, ha⟩ := hβon A hA
  obtain ⟨b, hb⟩ := hβon B hB
  obtain ⟨q₁, hq₁, h₁⟩ := hQ₁
  obtain ⟨q₂, hq₂, h₂⟩ := hQ₂
  have ha' : q₁ * (a : G) * q₁⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hQV hq₁) a).mp a.2
  have hb' : q₂ * (b : G) * q₂⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hQV hq₂) b).mp b.2
  have e₁ := h₁ a ⟨_, ha'⟩ rfl
  have e₂ := h₂ b ⟨_, hb'⟩ rfl
  set w : ↥V := (⟨_, ha'⟩ * a⁻¹) * (⟨_, hb'⟩ * b⁻¹) with hw
  have hwβ : Multiplicative.toAdd (β w) = Multiplicative.toAdd (β v) := by
    simp only [hw, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [e₁, e₂, ha, hb, hM]
    abel
  have hz : β (v * w⁻¹) = 1 := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, hwβ, add_neg_cancel, toAdd_one]
  have hvw : ((v * w⁻¹ : ↥V) : G) ∈ Z := (hβker _).mp hz
  have hwQ : (w : G) ∈ ⁅V, Q⁆ := by
    have e : (w : G) = (q₁ * (a : G) * q₁⁻¹ * (a : G)⁻¹) * (q₂ * (b : G) * q₂⁻¹ * (b : G)⁻¹) := by
      rw [hw]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [e]
    exact Subgroup.mul_mem _ (comm_mem_commutator hq₁ a.2) (comm_mem_commutator hq₂ b.2)
  have e2 : (v : G) = ((v * w⁻¹ : ↥V) : G) * (w : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [e2]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hvw) (Subgroup.mem_sup_left hwQ)

omit [CharP F 2] in
include β in
theorem eq_of_head (hβsl : ∀ v, (Multiplicative.toAdd (β v)).trace = 0)
    (hβon : ∀ M : Matrix (Fin 3) (Fin 3) F, M.trace = 0 → ∃ v, Multiplicative.toAdd (β v) = M)
    (hβker : ∀ v, β v = 1 ↔ (v : G) ∈ Z) (hQV : Q ≤ Subgroup.normalizer (V : Set G))
    {U₁ U₂ : Matrix (Fin 3) (Fin 3) F}
    (hQ₁ : ∃ q ∈ Q, ∀ v w : ↥V, (w : G) = q * v * q⁻¹ →
      Multiplicative.toAdd (β w) = U₁ * Multiplicative.toAdd (β v) * U₁)
    (hQ₂ : ∃ q ∈ Q, ∀ v w : ↥V, (w : G) = q * v * q⁻¹ →
      Multiplicative.toAdd (β w) = U₂ * Multiplicative.toAdd (β v) * U₂)
    {i₁ l₁ i₂ l₂ : Fin 3}
    (hdec : ∀ M : Matrix (Fin 3) (Fin 3) F, M.trace = 0 → M i₁ l₁ = 0 → M i₂ l₂ = 0 →
      ∃ A B : Matrix (Fin 3) (Fin 3) F, A.trace = 0 ∧ B.trace = 0 ∧
        M = (U₁ * A * U₁ - A) + (U₂ * B * U₂ - B))
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) {g : GL (Fin 3) F}
    (hx : ∀ v w : ↥V, (w : G) = x * v * x⁻¹ → Multiplicative.toAdd (β w) =
      (g : Matrix (Fin 3) (Fin 3) F) * Multiplicative.toAdd (β v) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    {κ : F} (hκ : κ ≠ 1)
    (hh : ∀ M : Matrix (Fin 3) (Fin 3) F,
      ((g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        i₁ l₁ = κ * M i₁ l₁ ∧
      ((g : Matrix (Fin 3) (Fin 3) F) * M * ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        i₂ l₂ = κ * M i₂ l₂)
    (hJ : ⁅V, Q⁆ ⊔ Z ≤ J) (hJV : J ≤ V) (hxJ : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ J) : J = V := by
  refine le_antisymm hJV fun v hv => ?_
  have hc : κ - 1 ≠ 0 := sub_ne_zero.mpr hκ
  have hc' : (κ - 1) * (κ - 1)⁻¹ = 1 := mul_inv_cancel₀ hc
  set N := Multiplicative.toAdd (β ⟨v, hv⟩) with hN
  obtain ⟨w, hw⟩ := hβon ((κ - 1)⁻¹ • N) (by rw [Matrix.trace_smul, hN, hβsl, smul_zero])
  have hw' : x * (w : G) * x⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hxV _).mp w.2
  have e := hx w ⟨_, hw'⟩ rfl
  set c : ↥V := ⟨_, hw'⟩ * w⁻¹ with hc_def
  have hcJ : (c : G) ∈ J := hxJ w w.2
  set d : ↥V := ⟨v, hv⟩ * c⁻¹ with hd
  have hdβ : Multiplicative.toAdd (β d) = N - ((g : Matrix (Fin 3) (Fin 3) F) * ((κ - 1)⁻¹ • N) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) - (κ - 1)⁻¹ • N) := by
    simp only [hd, hc_def, map_mul, map_inv, toAdd_mul, toAdd_inv]
    rw [e, hw]
    abel
  have hhd : ∀ i l : Fin 3, ((g : Matrix (Fin 3) (Fin 3) F) * ((κ - 1)⁻¹ • N) *
      ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i l = κ * ((κ - 1)⁻¹ • N) i l →
      (Multiplicative.toAdd (β d)) i l = 0 := by
    intro i l h
    rw [hdβ, Matrix.sub_apply, Matrix.sub_apply, h, Matrix.smul_apply, smul_eq_mul]
    linear_combination (-(N i l)) * hc'
  obtain ⟨A, B, hA, hB, hAB⟩ := hdec _ (hβsl d) (hhd _ _ (hh _).1) (hhd _ _ (hh _).2)
  have hdJ : (d : G) ∈ J := hJ (mem_of_decomp β hβon hβker hQV hQ₁ hQ₂ hA hB hAB)
  have hv' : v = (d : G) * (c : G) := by
    simp only [hd, Subgroup.coe_mul, Subgroup.coe_inv, inv_mul_cancel_right]
  rw [hv']
  exact J.mul_mem hdJ hcJ

end Head

theorem inv_toGL_tr3 {i j : Fin 3} (hij : i ≠ j) :
    (((SpecialLinearGroup.toGL (tr3 hij (1 : F)))⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      trM hij := by
  have h : SpecialLinearGroup.toGL (tr3 hij (1 : F)) * SpecialLinearGroup.toGL (tr3 hij 1) = 1 := by
    rw [← map_mul]
    have : tr3 hij (1 : F) * tr3 hij 1 = 1 := by
      apply Subtype.ext
      show Matrix.transvection i j (1 : F) * Matrix.transvection i j 1 = 1
      rw [Matrix.transvection_mul_transvection_same (h := hij), CharTwo.add_self_eq_zero,
        Matrix.transvection_zero]
    rw [this, map_one]
  rw [inv_eq_of_mul_eq_one_right h]
  rfl

omit [CharP F 2] in
theorem g00_ne_zero_of_one {g : GL (Fin 3) F} (h20 : (g : Matrix (Fin 3) (Fin 3) F) 2 0 = 0)
    (h21 : (g : Matrix (Fin 3) (Fin 3) F) 2 1 = 0) (h10 : (g : Matrix (Fin 3) (Fin 3) F) 1 0 = 0) :
    (g : Matrix (Fin 3) (Fin 3) F) 0 0 ≠ 0 := by
  intro h
  have hdet : (g : Matrix (Fin 3) (Fin 3) F).det ≠ 0 := by
    rw [← GeneralLinearGroup.val_det_apply]
    exact Units.ne_zero _
  apply hdet
  rw [Matrix.det_fin_three, h, h20, h21, h10]
  ring

omit [CharP F 2] in
theorem eq_one_of_sq_of_cube {H : Type} [Group H] {y : H} (h2 : y ^ 2 = 1) (h3 : y ^ 3 = 1) :
    y = 1 := by
  have e : y = y ^ 3 * (y ^ 2)⁻¹ := by group
  rw [e, h2, h3, inv_one, mul_one]

section HeadP

variable [Finite F] {G : Type} [Group G] {V Z J Q : Subgroup G}
  (β : ↥V →* Multiplicative (Matrix (Fin 3) (Fin 3) F))

include β in
theorem eq_of_head_Ptheta (hF : Nat.card F = 4) {j : Fin 2}
    (hβsl : ∀ v, (Multiplicative.toAdd (β v)).trace = 0)
    (hβon : ∀ M : Matrix (Fin 3) (Fin 3) F, M.trace = 0 → ∃ v, Multiplicative.toAdd (β v) = M)
    (hβker : ∀ v, β v = 1 ↔ (v : G) ∈ Z) (hQV : Q ≤ Subgroup.normalizer (V : Set G))
    (hQ : ∀ p ∈ pCoreOf 2 (Ptheta F j), ∃ q ∈ Q, ∀ h : GL (Fin 3) F, ProjGenLinGroup.mk h = p →
      ∀ v w : ↥V, (w : G) = q * v * q⁻¹ → Multiplicative.toAdd (β w) =
        (h : Matrix (Fin 3) (Fin 3) F) * Multiplicative.toAdd (β v) *
          ((h⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    {x : G} (hxV : x ∈ Subgroup.normalizer (V : Set G)) {g : GL (Fin 3) F}
    (hgN : ProjGenLinGroup.mk g ∈
      Subgroup.normalizer ((pCoreOf 2 (Ptheta F j) : Subgroup (PGL3 F)) : Set (PGL3 F)))
    (hgsc : ProjGenLinGroup.mk g ∈ sectionCentralizer (Ptheta F j) (pCoreOf 2 (Ptheta F j)))
    (hg3 : ProjGenLinGroup.mk g ^ 3 = 1) (hg1 : ProjGenLinGroup.mk g ≠ 1)
    (hx : ∀ v w : ↥V, (w : G) = x * v * x⁻¹ → Multiplicative.toAdd (β w) =
      (g : Matrix (Fin 3) (Fin 3) F) * Multiplicative.toAdd (β v) *
        ((g⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
    (hJ : ⁅V, Q⁆ ⊔ Z ≤ J) (hJV : J ≤ V) (hxJ : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ J) : J = V := by
  have hU : ∀ {a b : Fin 3} (hab : a ≠ b), tr3 hab (1 : F) ∈ radU F (flagSpace 3 F ((j : ℕ) + 1)) →
      ∃ q ∈ Q, ∀ v w : ↥V, (w : G) = q * v * q⁻¹ →
        Multiplicative.toAdd (β w) = trM hab * Multiplicative.toAdd (β v) * trM hab := by
    intro a b hab hr
    obtain ⟨q, hq, hqa⟩ := hQ _ ((mem_pCoreOf_Ptheta hF).mpr ⟨_, hr, rfl⟩)
    refine ⟨q, hq, fun v w hvw => ?_⟩
    rw [hqa _ rfl v w hvw, inv_toGL_tr3]
    rfl
  have hne : ∀ κ : F, κ = 1 → ProjGenLinGroup.mk g ^ 2 = 1 → False := fun _ _ h2 =>
    hg1 (eq_one_of_sq_of_cube h2 hg3)
  fin_cases j
  · obtain ⟨h10, h20⟩ := entries_of_normalizer_zero hF hgN
    obtain ⟨h12, h21, h11⟩ := block_of_mem_sc_zero hF hgsc h10 h20
    have h0 := g00_ne_zero h10 h20
    refine eq_of_head β hβsl hβon hβker hQV (hU (by decide) (tr3_mem_radU_zero (by decide) 1))
      (hU (by decide) (tr3_mem_radU_zero (by decide) 1))
      (fun M htr h1 h2 => decomp_zero M htr h1 h2) hxV hx
      (κ := (g : Matrix (Fin 3) (Fin 3) F) 1 1 / (g : Matrix (Fin 3) (Fin 3) F) 0 0) ?_
      (fun M => ⟨head_zero h10 h20 h12 h21 h11 M (by decide),
        head_zero h10 h20 h12 h21 h11 M (by decide)⟩) hJ hJV hxJ
    intro hκ
    have h0' : (g : Matrix (Fin 3) (Fin 3) F) 0 0 = (g : Matrix (Fin 3) (Fin 3) F) 1 1 := by
      rw [div_eq_one_iff_eq h0] at hκ
      exact hκ.symm
    exact hne 1 rfl (sq_mk_eq_one_zero h10 h20 h12 h21 h11 h0')
  · obtain ⟨h20, h21⟩ := entries_of_normalizer_one hF hgN
    obtain ⟨h01, h10, h00⟩ := block_of_mem_sc_one hF hgsc h20 h21
    have h0 := g00_ne_zero_of_one h20 h21 h10
    refine eq_of_head β hβsl hβon hβker hQV (hU (by decide) (tr3_mem_radU_one (by decide) 1))
      (hU (by decide) (tr3_mem_radU_one (by decide) 1))
      (fun M htr h1 h2 => decomp_one M htr h1 h2) hxV hx
      (κ := (g : Matrix (Fin 3) (Fin 3) F) 2 2 / (g : Matrix (Fin 3) (Fin 3) F) 0 0) ?_
      (fun M => ⟨head_one h20 h21 h01 h10 h00 M (by decide),
        head_one h20 h21 h01 h10 h00 M (by decide)⟩) hJ hJV hxJ
    intro hκ
    have h22 : (g : Matrix (Fin 3) (Fin 3) F) 2 2 = (g : Matrix (Fin 3) (Fin 3) F) 0 0 := by
      rw [div_eq_one_iff_eq h0] at hκ
      exact hκ
    exact hne 1 rfl (sq_mk_eq_one_one h20 h21 h01 h10 h00 h22)

end HeadP

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
