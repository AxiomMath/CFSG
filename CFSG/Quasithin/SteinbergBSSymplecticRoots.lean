module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bAut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bOdd
public import CFSG.Quasithin.SteinbergBSLinearThreeRoot

public section

namespace CFSG.Quasithin.SteinbergBS

open Matrix Subgroup CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b

section Roots

variable {F : Type} [Field F] [CharP F 2]

variable (F) in
@[expose] def rootLong : Subgroup (antiSp F) where
  carrier := {g | ∃ t : F, g = uElt 0 0 t 0}
  mul_mem' := by
    rintro _ _ ⟨t, rfl⟩ ⟨s, rfl⟩
    exact ⟨t + s, by rw [uElt_mul]; congr 1 <;> ring⟩
  one_mem' := ⟨0, uElt_zero_eq_one.symm⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, by rw [uElt_inv]; congr 1; ring⟩

variable (F) in
@[expose] def rootShort : Subgroup (antiSp F) where
  carrier := {g | ∃ t : F, g = uElt 0 t 0 0}
  mul_mem' := by
    rintro _ _ ⟨t, rfl⟩ ⟨s, rfl⟩
    exact ⟨t + s, by rw [uElt_mul]; congr 1 <;> ring⟩
  one_mem' := ⟨0, uElt_zero_eq_one.symm⟩
  inv_mem' := by
    rintro _ ⟨t, rfl⟩
    exact ⟨t, by rw [uElt_inv]; congr 1; ring⟩

theorem glMat_uElt_long (t : F) :
    glMat ((uElt 0 0 t 0 : antiSp F) : GL (Fin 4) F) = 1 + Matrix.single 0 3 t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glMat_uElt, uMat]

theorem glMat_uElt_short (t : F) :
    glMat ((uElt 0 t 0 0 : antiSp F) : GL (Fin 4) F) =
      1 + Matrix.single 0 2 t + Matrix.single 1 3 t := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [glMat_uElt, uMat]

theorem mem_rootLong_iff_glMat {x : antiSp F} :
    x ∈ rootLong F ↔ ∃ t : F, glMat (x : GL (Fin 4) F) = 1 + Matrix.single 0 3 t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, glMat_uElt_long t⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, antiSp_ext (ht.trans (glMat_uElt_long t).symm)⟩

theorem mem_rootShort_iff_glMat {x : antiSp F} :
    x ∈ rootShort F ↔
      ∃ t : F, glMat (x : GL (Fin 4) F) = 1 + Matrix.single 0 2 t + Matrix.single 1 3 t := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, glMat_uElt_short t⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, antiSp_ext (ht.trans (glMat_uElt_short t).symm)⟩

theorem rootLong_le_center : rootLong F ≤ antiUnipotentCenter F := by
  rintro _ ⟨t, rfl⟩
  exact ⟨0, t, rfl⟩

theorem rootShort_le_center : rootShort F ≤ antiUnipotentCenter F := by
  rintro _ ⟨t, rfl⟩
  exact ⟨t, 0, rfl⟩

theorem rootLong_sup_rootShort : rootLong F ⊔ rootShort F = antiUnipotentCenter F := by
  refine le_antisymm (sup_le rootLong_le_center rootShort_le_center) ?_
  rintro _ ⟨b, c, rfl⟩
  have h : uElt (0 : F) b c 0 = uElt 0 0 c 0 * uElt 0 b 0 0 := by
    rw [uElt_mul]
    congr 1 <;> ring
  rw [h]
  exact mul_mem_sup ⟨c, rfl⟩ ⟨b, rfl⟩

theorem rootLong_inf_rootShort : rootLong F ⊓ rootShort F = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨⟨t, rfl⟩, ⟨s, hs⟩⟩
  obtain ⟨-, h1, h2, -⟩ := uElt_inj hs
  rw [mem_bot, h2, uElt_zero_eq_one]

theorem card_rootLong [Finite F] : Nat.card (rootLong F) = Nat.card F := by
  refine (Nat.card_congr (Equiv.ofBijective (fun t : F => (⟨uElt 0 0 t 0, t, rfl⟩ : rootLong F))
    ⟨fun t s h => ?_, ?_⟩)).symm
  · exact (uElt_inj (congrArg Subtype.val h)).2.2.1
  · rintro ⟨_, t, rfl⟩
    exact ⟨t, rfl⟩

theorem card_rootShort [Finite F] : Nat.card (rootShort F) = Nat.card F := by
  refine (Nat.card_congr (Equiv.ofBijective (fun t : F => (⟨uElt 0 t 0 0, t, rfl⟩ : rootShort F))
    ⟨fun t s h => ?_, ?_⟩)).symm
  · exact (uElt_inj (congrArg Subtype.val h)).2.1
  · rintro ⟨_, t, rfl⟩
    exact ⟨t, rfl⟩

end Roots

section Normalizer

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem mul_uMat_apply_zero (N : Matrix (Fin 4) (Fin 4) F) (a b c d : F) (i : Fin 4) :
    (N * uMat a b c d) i 0 = N i 0 := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

omit [CharP F 2] in
theorem mul_uMat_apply_one (N : Matrix (Fin 4) (Fin 4) F) (a b c d : F) (i : Fin 4) :
    (N * uMat a b c d) i 1 = N i 0 * a + N i 1 := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

omit [CharP F 2] in
theorem mul_uMat_apply_two (N : Matrix (Fin 4) (Fin 4) F) (a b c d : F) (i : Fin 4) :
    (N * uMat a b c d) i 2 = N i 0 * b + N i 1 * d + N i 2 := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

omit [CharP F 2] in
theorem mul_uMat_apply_three (N : Matrix (Fin 4) (Fin 4) F) (a b c d : F) (i : Fin 4) :
    (N * uMat a b c d) i 3 = N i 0 * c + N i 1 * (b + a * d) + N i 2 * a + N i 3 := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

omit [CharP F 2] in
theorem uMat_mul_apply_zero (N : Matrix (Fin 4) (Fin 4) F) (a b c d : F) (j : Fin 4) :
    (uMat a b c d * N) 0 j = N 0 j + a * N 1 j + b * N 2 j + c * N 3 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

omit [CharP F 2] in
theorem uMat_mul_apply_one (N : Matrix (Fin 4) (Fin 4) F) (a b c d : F) (j : Fin 4) :
    (uMat a b c d * N) 1 j = N 1 j + d * N 2 j + (b + a * d) * N 3 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

omit [CharP F 2] in
theorem uMat_mul_apply_two (N : Matrix (Fin 4) (Fin 4) F) (a b c d : F) (j : Fin 4) :
    (uMat a b c d * N) 2 j = N 2 j + a * N 3 j := by
  simp [Matrix.mul_apply, Fin.sum_univ_four, uMat]

theorem glMat_mul_eq_of_conj {h x : antiSp F} {a b c d : F} (hx : h⁻¹ * x * h = uElt a b c d) :
    glMat (x : GL (Fin 4) F) * glMat (h : GL (Fin 4) F) =
      glMat (h : GL (Fin 4) F) * uMat a b c d := by
  have h1 : x * h = h * uElt a b c d := by rw [← hx]; group
  have h2 := congrArg (fun g : antiSp F => glMat (g : GL (Fin 4) F)) h1
  simpa [glMat_uElt] using h2

theorem upper_of_mem_normalizer {h : antiSp F}
    (hh : h ∈ normalizer ((antiUnipotent F : Subgroup (antiSp F)) : Set (antiSp F))) :
    ∀ i j : Fin 4, j < i → glMat (h : GL (Fin 4) F) i j = 0 := by
  have hconj : ∀ x ∈ antiUnipotent F, h⁻¹ * x * h ∈ antiUnipotent F := fun x hx => by
    have h1 := (mem_normalizer_iff.1 (inv_mem hh) x).1 hx
    simpa using h1
  obtain ⟨a₁, b₁, c₁, d₁, hx⟩ := hconj _ (uElt_mem_antiUnipotent (1 : F) 0 0 0)
  obtain ⟨a₂, b₂, c₂, d₂, hy⟩ := hconj _ (uElt_mem_antiUnipotent (0 : F) 0 0 1)
  have hE1 := glMat_mul_eq_of_conj hx
  have hE2 := glMat_mul_eq_of_conj hy
  rw [glMat_uElt] at hE1 hE2
  set M := glMat (h : GL (Fin 4) F) with hM
  have entry : ∀ (P Q : Matrix (Fin 4) (Fin 4) F), P = Q → ∀ i j, P i j = Q i j :=
    fun P Q h i j => by rw [h]
  have e10 := entry _ _ hE1 0 0
  have e30 := entry _ _ hE1 2 0
  have e20 := entry _ _ hE2 1 0
  have e31 := entry _ _ hE1 2 1
  have e21 := entry _ _ hE2 1 1
  have e32 := entry _ _ hE1 2 2
  rw [uMat_mul_apply_zero, mul_uMat_apply_zero] at e10
  rw [uMat_mul_apply_two, mul_uMat_apply_zero] at e30
  rw [uMat_mul_apply_one, mul_uMat_apply_zero] at e20
  rw [uMat_mul_apply_two, mul_uMat_apply_one] at e31
  rw [uMat_mul_apply_one, mul_uMat_apply_one] at e21
  rw [uMat_mul_apply_two, mul_uMat_apply_two] at e32
  have h10 : M 1 0 = 0 := by linear_combination e10
  have h30 : M 3 0 = 0 := by linear_combination e30
  have h20 : M 2 0 = 0 := by linear_combination e20
  have h31 : M 3 1 = 0 := by linear_combination e31 + a₁ * h20
  have h21 : M 2 1 = 0 := by linear_combination e21 + a₂ * h10
  have h32 : M 3 2 = 0 := by linear_combination e32 + b₁ * h20 + d₁ * h21
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption

theorem upper_relations {h : antiSp F}
    (hU : ∀ i j : Fin 4, j < i → glMat (h : GL (Fin 4) F) i j = 0) :
    glMat (h : GL (Fin 4) F) 0 0 * glMat (h : GL (Fin 4) F) 3 3 = 1 ∧
      glMat (h : GL (Fin 4) F) 1 1 * glMat (h : GL (Fin 4) F) 2 2 = 1 ∧
      glMat (h : GL (Fin 4) F) 0 1 * glMat (h : GL (Fin 4) F) 3 3 =
        glMat (h : GL (Fin 4) F) 1 1 * glMat (h : GL (Fin 4) F) 2 3 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hJ := mem_antiSp.mp h.2
  have e03 := congrFun (congrFun hJ 0) 3
  have e12 := congrFun (congrFun hJ 1) 2
  have e13 := congrFun (congrFun hJ 1) 3
  rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at e03 e12 e13
  set M := glMat (h : GL (Fin 4) F) with hM
  have h10 := hU 1 0 (by decide)
  have h20 := hU 2 0 (by decide)
  have h30 := hU 3 0 (by decide)
  have h21 := hU 2 1 (by decide)
  have h31 := hU 3 1 (by decide)
  have h32 := hU 3 2 (by decide)
  rw [h10, h20, h30] at e03
  rw [h21, h31, h32] at e12
  rw [h21, h31] at e13
  norm_num at e03 e12 e13
  refine ⟨by linear_combination e03, by linear_combination e12, ?_⟩
  linear_combination e13 - M 1 1 * M 2 3 * h2

theorem upper_diag_ne_zero {h : antiSp F}
    (hU : ∀ i j : Fin 4, j < i → glMat (h : GL (Fin 4) F) i j = 0) :
    glMat (h : GL (Fin 4) F) 0 0 ≠ 0 ∧ glMat (h : GL (Fin 4) F) 1 1 ≠ 0 ∧
      glMat (h : GL (Fin 4) F) 2 2 ≠ 0 ∧ glMat (h : GL (Fin 4) F) 3 3 ≠ 0 := by
  obtain ⟨h1, h2, -⟩ := upper_relations hU
  exact ⟨left_ne_zero_of_mul_eq_one h1, left_ne_zero_of_mul_eq_one h2,
    right_ne_zero_of_mul_eq_one h2, right_ne_zero_of_mul_eq_one h1⟩

theorem conj_uElt_coords {h : antiSp F}
    (hU : ∀ i j : Fin 4, j < i → glMat (h : GL (Fin 4) F) i j = 0) {a b c d a' b' c' d' : F}
    (he : h * uElt a b c d * h⁻¹ = uElt a' b' c' d') :
    a' * glMat (h : GL (Fin 4) F) 1 1 = glMat (h : GL (Fin 4) F) 0 0 * a ∧
      d' * glMat (h : GL (Fin 4) F) 2 2 = glMat (h : GL (Fin 4) F) 1 1 * d ∧
      a' * glMat (h : GL (Fin 4) F) 1 2 + b' * glMat (h : GL (Fin 4) F) 2 2 =
        glMat (h : GL (Fin 4) F) 0 0 * b + glMat (h : GL (Fin 4) F) 0 1 * d ∧
      a' * glMat (h : GL (Fin 4) F) 1 3 + b' * glMat (h : GL (Fin 4) F) 2 3 +
          c' * glMat (h : GL (Fin 4) F) 3 3 =
        glMat (h : GL (Fin 4) F) 0 0 * c + glMat (h : GL (Fin 4) F) 0 1 * (b + a * d) +
          glMat (h : GL (Fin 4) F) 0 2 * a := by
  have h1 : uElt a' b' c' d' * h = h * uElt a b c d := by rw [← he]; group
  have h2 := congrArg (fun g : antiSp F => glMat (g : GL (Fin 4) F)) h1
  have hE : uMat a' b' c' d' * glMat (h : GL (Fin 4) F) =
      glMat (h : GL (Fin 4) F) * uMat a b c d := by
    simpa [glMat_uElt] using h2
  set M := glMat (h : GL (Fin 4) F) with hM
  have entry : ∀ (P Q : Matrix (Fin 4) (Fin 4) F), P = Q → ∀ i j, P i j = Q i j :=
    fun P Q h i j => by rw [h]
  have e01 := entry _ _ hE 0 1
  have e12 := entry _ _ hE 1 2
  have e02 := entry _ _ hE 0 2
  have e03 := entry _ _ hE 0 3
  rw [uMat_mul_apply_zero, mul_uMat_apply_one] at e01
  rw [uMat_mul_apply_one, mul_uMat_apply_two] at e12
  rw [uMat_mul_apply_zero, mul_uMat_apply_two] at e02
  rw [uMat_mul_apply_zero, mul_uMat_apply_three] at e03
  have h10 := hU 1 0 (by decide)
  have h20 := hU 2 0 (by decide)
  have h30 := hU 3 0 (by decide)
  have h21 := hU 2 1 (by decide)
  have h31 := hU 3 1 (by decide)
  have h32 := hU 3 2 (by decide)
  rw [h21, h31] at e01
  rw [h10, h32] at e12
  rw [h32] at e02
  refine ⟨by linear_combination e01, by linear_combination e12, by linear_combination e02,
    by linear_combination e03⟩

end Normalizer

section Minor

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem minorAut_uElt (a b c d : F) :
    minorAut F (uElt a b c d) =
      uElt d (c + a * b + a ^ 2 * d) (b ^ 2 + a * b * d + c * d) (a ^ 2) :=
  antiSp_ext (by rw [glMat_minorAut, glMat_uElt, minorMap_uMat, glMat_uElt])

theorem minorAut_sq_pow_uElt (r : ℕ) (a b c d : F) :
    ((minorAut F ^ 2) ^ r) (uElt a b c d) =
      uElt (a ^ 2 ^ r) (b ^ 2 ^ r) (c ^ 2 ^ r) (d ^ 2 ^ r) :=
  antiSp_ext (by rw [glMat_minorAut_sq_pow, glMat_uElt, uMat_map_pow, glMat_uElt])

theorem minorAut_odd_pow_uElt (r : ℕ) (a b c d : F) :
    (minorAut F ^ (2 * r + 1)) (uElt a b c d) =
      uElt (d ^ 2 ^ r) (c ^ 2 ^ r + a ^ 2 ^ r * b ^ 2 ^ r + (a ^ 2 ^ r) ^ 2 * d ^ 2 ^ r)
        ((b ^ 2 ^ r) ^ 2 + a ^ 2 ^ r * b ^ 2 ^ r * d ^ 2 ^ r + c ^ 2 ^ r * d ^ 2 ^ r)
        ((a ^ 2 ^ r) ^ 2) := by
  rw [pow_succ', pow_mul, MulAut.mul_apply, minorAut_sq_pow_uElt, minorAut_uElt]

omit [CharP F 2] [Finite F] in
theorem zero_pow_two_pow (r : ℕ) : (0 : F) ^ 2 ^ r = 0 :=
  zero_pow (pow_ne_zero r two_ne_zero)

end Minor

section Actions

open CFSG.ComponentClassification.OuterAutomorphisms (inner inner_normal)
open CFSG.ABGLocalTools (IsSylowOf)

variable {F : Type} [Field F] [CharP F 2] [Finite F]

theorem minorAut_mem_antiUnipotent {x : antiSp F} (hx : x ∈ antiUnipotent F) :
    minorAut F x ∈ antiUnipotent F := by
  obtain ⟨a, b, c, d, rfl⟩ := hx
  rw [minorAut_uElt]
  exact uElt_mem_antiUnipotent _ _ _ _

omit [CharP F 2] [Finite F] in
theorem map_eq_of_map_le {G : Type*} [Group G] [Finite G] {X Y : Subgroup G} {e : MulAut G}
    (h : X.map e.toMonoidHom ≤ Y) (hc : Nat.card Y ≤ Nat.card X) : X.map e.toMonoidHom = Y :=
  Subgroup.eq_of_le_of_card_ge h (by rwa [Subgroup.card_map_of_injective e.injective])

theorem map_minorAut_pow_antiUnipotent (j : ℕ) :
    (antiUnipotent F).map (minorAut F ^ j).toMonoidHom = antiUnipotent F := by
  refine map_eq_of_map_le ?_ le_rfl
  induction j with
  | zero =>
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx
  | succ j ih =>
    rintro _ ⟨x, hx, rfl⟩
    show (minorAut F ^ (j + 1)) x ∈ _
    rw [pow_succ', MulAut.mul_apply]
    exact minorAut_mem_antiUnipotent (ih ⟨x, hx, rfl⟩)

theorem mem_normalizer_of_conj_mul_pow {h : antiSp F} {j : ℕ}
    (hU : (antiUnipotent F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = antiUnipotent F) :
    h ∈ normalizer ((antiUnipotent F : Subgroup (antiSp F)) : Set (antiSp F)) := by
  apply mem_normalizer_of_map_conj_eq
  rwa [CFSG.QuasithinUnique.Setup.Family.map_toMonoidHom_mul,
    map_minorAut_pow_antiUnipotent] at hU

omit [Finite F] in
theorem conj_mem_radA1 {h : antiSp F}
    (hh : h ∈ normalizer ((antiUnipotent F : Subgroup (antiSp F)) : Set (antiSp F)))
    {x : antiSp F} (hx : x ∈ radA1 F) : h * x * h⁻¹ ∈ radA1 F := by
  obtain ⟨b, c, d, rfl⟩ := hx
  obtain ⟨a', b', c', d', he⟩ := (mem_normalizer_iff.1 hh _).1 (uElt_mem_antiUnipotent 0 b c d)
  have hU := upper_of_mem_normalizer hh
  obtain ⟨e1, -, -, -⟩ := conj_uElt_coords hU he
  have ha' : a' = 0 := by
    rw [mul_zero] at e1
    exact (mul_eq_zero.1 e1).resolve_right (upper_diag_ne_zero hU).2.1
  rw [he, ha']
  exact ⟨b', c', d', rfl⟩

omit [Finite F] in
theorem conj_mem_radA2 {h : antiSp F}
    (hh : h ∈ normalizer ((antiUnipotent F : Subgroup (antiSp F)) : Set (antiSp F)))
    {x : antiSp F} (hx : x ∈ radA2 F) : h * x * h⁻¹ ∈ radA2 F := by
  obtain ⟨a, b, c, rfl⟩ := hx
  obtain ⟨a', b', c', d', he⟩ := (mem_normalizer_iff.1 hh _).1 (uElt_mem_antiUnipotent a b c 0)
  have hU := upper_of_mem_normalizer hh
  obtain ⟨-, e2, -, -⟩ := conj_uElt_coords hU he
  have hd' : d' = 0 := by
    rw [mul_zero] at e2
    exact (mul_eq_zero.1 e2).resolve_right (upper_diag_ne_zero hU).2.2.1
  rw [he, hd']
  exact ⟨a', b', c', rfl⟩

omit [Finite F] in
theorem conj_mem_rootLong {h : antiSp F}
    (hh : h ∈ normalizer ((antiUnipotent F : Subgroup (antiSp F)) : Set (antiSp F)))
    {x : antiSp F} (hx : x ∈ rootLong F) : h * x * h⁻¹ ∈ rootLong F := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨a', b', c', d', he⟩ := (mem_normalizer_iff.1 hh _).1 (uElt_mem_antiUnipotent 0 0 t 0)
  have hU := upper_of_mem_normalizer hh
  obtain ⟨e1, e2, e3, -⟩ := conj_uElt_coords hU he
  obtain ⟨d0, d1, d2, -⟩ := upper_diag_ne_zero hU
  have ha' : a' = 0 := by
    rw [mul_zero] at e1
    exact (mul_eq_zero.1 e1).resolve_right d1
  have hd' : d' = 0 := by
    rw [mul_zero] at e2
    exact (mul_eq_zero.1 e2).resolve_right d2
  have hb' : b' = 0 := by
    simp only [ha', zero_mul, mul_zero, zero_add, add_zero] at e3
    exact (mul_eq_zero.1 e3).resolve_right d2
  rw [he, ha', hb', hd']
  exact ⟨c', rfl⟩

omit [Finite F] in
theorem conj_mem_rootShort {h : antiSp F}
    (hh : h ∈ normalizer ((antiUnipotent F : Subgroup (antiSp F)) : Set (antiSp F)))
    {x : antiSp F} (hx : x ∈ rootShort F) : h * x * h⁻¹ ∈ rootShort F := by
  obtain ⟨t, rfl⟩ := hx
  obtain ⟨a', b', c', d', he⟩ := (mem_normalizer_iff.1 hh _).1 (uElt_mem_antiUnipotent 0 t 0 0)
  have hU := upper_of_mem_normalizer hh
  obtain ⟨e1, e2, e3, e4⟩ := conj_uElt_coords hU he
  obtain ⟨d0, d1, d2, d3⟩ := upper_diag_ne_zero hU
  obtain ⟨R1, R2, R3⟩ := upper_relations hU
  have ha' : a' = 0 := by
    rw [mul_zero] at e1
    exact (mul_eq_zero.1 e1).resolve_right d1
  have hd' : d' = 0 := by
    rw [mul_zero] at e2
    exact (mul_eq_zero.1 e2).resolve_right d2
  subst ha' hd'
  set M := glMat (h : GL (Fin 4) F) with hM
  have hrel : M 0 1 * M 2 2 = M 0 0 * M 2 3 := by
    linear_combination (-(M 0 1 * M 2 2)) * R1 + (M 0 0 * M 2 2) * R3 + (M 0 0 * M 2 3) * R2
  have hc : c' * (M 3 3 * M 2 2) = 0 := by
    linear_combination M 2 2 * e4 - M 2 3 * e3 + t * hrel
  have hc' : c' = 0 := (mul_eq_zero.1 hc).resolve_right (mul_ne_zero d3 d2)
  rw [he, hc']
  exact ⟨b', rfl⟩

theorem swap_of_odd {h : antiSp F} {j : ℕ} (hj : Odd j)
    (hU : (antiUnipotent F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = antiUnipotent F) :
    (rootLong F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = rootShort F ∧
      (rootShort F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = rootLong F ∧
      (radA1 F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = radA2 F ∧
      (radA2 F).map (MulAut.conj h * minorAut F ^ j).toMonoidHom = radA1 F := by
  have hh := mem_normalizer_of_conj_mul_pow hU
  obtain ⟨r, rfl⟩ := hj
  have happly : ∀ x, (MulAut.conj h * minorAut F ^ (2 * r + 1)) x =
      h * (minorAut F ^ (2 * r + 1)) x * h⁻¹ := fun x => rfl
  have hA1 := (card_radicals (K := F)).2.1
  have hA2 := (card_radicals (K := F)).2.2.1
  refine ⟨map_eq_of_map_le ?_ (by rw [card_rootLong, card_rootShort]),
    map_eq_of_map_le ?_ (by rw [card_rootLong, card_rootShort]),
    map_eq_of_map_le ?_ (by rw [hA1, hA2]), map_eq_of_map_le ?_ (by rw [hA1, hA2])⟩
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    show (MulAut.conj h * minorAut F ^ (2 * r + 1)) (uElt 0 0 t 0) ∈ rootShort F
    rw [happly, minorAut_odd_pow_uElt]
    refine conj_mem_rootShort hh ⟨t ^ 2 ^ r, ?_⟩
    simp
  · rintro _ ⟨_, ⟨t, rfl⟩, rfl⟩
    show (MulAut.conj h * minorAut F ^ (2 * r + 1)) (uElt 0 t 0 0) ∈ rootLong F
    rw [happly, minorAut_odd_pow_uElt]
    refine conj_mem_rootLong hh ⟨(t ^ 2 ^ r) ^ 2, ?_⟩
    simp
  · rintro _ ⟨_, ⟨b, c, d, rfl⟩, rfl⟩
    show (MulAut.conj h * minorAut F ^ (2 * r + 1)) (uElt 0 b c d) ∈ radA2 F
    rw [happly, minorAut_odd_pow_uElt]
    refine conj_mem_radA2 hh ⟨d ^ 2 ^ r, c ^ 2 ^ r, (b ^ 2 ^ r) ^ 2 + c ^ 2 ^ r * d ^ 2 ^ r, ?_⟩
    simp
  · rintro _ ⟨_, ⟨a, b, c, rfl⟩, rfl⟩
    show (MulAut.conj h * minorAut F ^ (2 * r + 1)) (uElt a b c 0) ∈ radA1 F
    rw [happly, minorAut_odd_pow_uElt]
    refine conj_mem_radA1 hh ⟨c ^ 2 ^ r + a ^ 2 ^ r * b ^ 2 ^ r, (b ^ 2 ^ r) ^ 2,
      (a ^ 2 ^ r) ^ 2, ?_⟩
    simp

theorem exists_eq_conj_of_trivial_mod_center_sp {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {e : MulAut (antiSp F)} (heU : (antiUnipotent F).map e.toMonoidHom = antiUnipotent F)
    (htriv : ∀ u ∈ antiUnipotent F, e u * u⁻¹ ∈ antiUnipotentCenter F) :
    ∃ v ∈ antiUnipotent F, e = MulAut.conj v := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨g, j, hj, rfl⟩ := aut_eq_conj_mul_pow hf hF e
  have hg := mem_normalizer_of_conj_mul_pow heU
  have hgU := upper_of_mem_normalizer hg
  obtain ⟨R1, R2, -⟩ := upper_relations hgU
  obtain ⟨d0, d1, d2, d3⟩ := upper_diag_ne_zero hgU
  set M := glMat (g : GL (Fin 4) F) with hM
  have happly : ∀ x, (MulAut.conj g * minorAut F ^ j) x = g * (minorAut F ^ j) x * g⁻¹ :=
    fun x => rfl
  have hfix : ∀ a b c d a' b' c' d' : F,
      (MulAut.conj g * minorAut F ^ j) (uElt a b c d) = uElt a' b' c' d' → a' = a ∧ d' = d := by
    intro a b c d a' b' c' d' he
    have h1 := htriv _ (uElt_mem_antiUnipotent a b c d)
    rw [he, uElt_inv, uElt_mul] at h1
    obtain ⟨β, γ, hβγ⟩ := h1
    obtain ⟨ha, -, -, hd⟩ := uElt_inj hβγ
    exact ⟨by linear_combination ha - a * h2, by linear_combination hd - d * h2⟩
  rcases Nat.even_or_odd j with ⟨r, hr⟩ | ⟨r, hr⟩
  ·
    have hj2 : j = 2 * r := by omega
    subst hj2
    have hcoord : ∀ a d : F, a * M 1 1 = M 0 0 * a ^ 2 ^ r ∧ d * M 2 2 = M 1 1 * d ^ 2 ^ r := by
      intro a d
      have hx : (minorAut F ^ (2 * r)) (uElt a 0 0 d) = uElt (a ^ 2 ^ r) 0 0 (d ^ 2 ^ r) := by
        rw [pow_mul, minorAut_sq_pow_uElt, zero_pow_two_pow]
      obtain ⟨a', b', c', d', he⟩ :=
        (mem_normalizer_iff.1 hg _).1 (uElt_mem_antiUnipotent (a ^ 2 ^ r) 0 0 (d ^ 2 ^ r))
      have he' : (MulAut.conj g * minorAut F ^ (2 * r)) (uElt a 0 0 d) = uElt a' b' c' d' := by
        rw [happly, hx, he]
      obtain ⟨ha, hd⟩ := hfix _ _ _ _ _ _ _ _ he'
      obtain ⟨e1, e2, -, -⟩ := conj_uElt_coords hgU he
      rw [ha] at e1
      rw [hd] at e2
      exact ⟨e1, e2⟩
    have h11 : M 1 1 = M 0 0 := by simpa using (hcoord 1 1).1
    have h22 : M 2 2 = M 1 1 := by simpa using (hcoord 1 1).2
    have hpow : ∀ a : F, a ^ 2 ^ r = a := fun a => by
      have h1 := (hcoord a 1).1
      rw [h11] at h1
      have h3 : M 0 0 * a ^ 2 ^ r = M 0 0 * a := by linear_combination -h1
      exact mul_left_cancel₀ d0 h3
    obtain ⟨Fr, hFr, hord, -⟩ := exists_frobenius_data hf hF
    have hFr1 : Fr ^ r = 1 := RingEquiv.ext fun t => by
      rw [frobenius_pow_apply hFr, hpow]
      rfl
    have hr0 : r = 0 := by
      have h1 := orderOf_dvd_of_pow_eq_one hFr1
      rw [hord] at h1
      exact Nat.eq_zero_of_dvd_of_lt h1 (by omega)
    subst hr0
    have hl : M 1 1 = 1 := by
      have h1 : (M 1 1 + 1) ^ 2 = 0 := by
        rw [h22] at R2
        linear_combination R2 + (M 1 1 + 1) * h2
      have h3 := pow_eq_zero_iff (two_ne_zero) |>.1 h1
      linear_combination h3 - h2
    have hgu : g ∈ antiUnipotent F := by
      rw [mem_antiUnipotent_iff_upper]
      refine ⟨hgU, fun i => ?_⟩
      have h00 : M 0 0 = 1 := by rw [← h11, hl]
      have h22' : M 2 2 = 1 := by rw [h22, hl]
      have h33 : M 3 3 = 1 := by
        rw [h00, one_mul] at R1
        exact R1
      fin_cases i
      · exact h00
      · exact hl
      · exact h22'
      · exact h33
    refine ⟨g, hgu, ?_⟩
    rw [mul_zero, pow_zero, mul_one]
  ·
    subst hr
    exfalso
    have hx : (minorAut F ^ (2 * r + 1)) (uElt 1 0 0 0) = uElt 0 0 0 1 := by
      rw [minorAut_odd_pow_uElt]
      simp
    obtain ⟨a', b', c', d', he⟩ :=
      (mem_normalizer_iff.1 hg _).1 (uElt_mem_antiUnipotent (0 : F) 0 0 1)
    have he' : (MulAut.conj g * minorAut F ^ (2 * r + 1)) (uElt 1 0 0 0) = uElt a' b' c' d' := by
      rw [happly, hx, he]
    obtain ⟨ha, -⟩ := hfix _ _ _ _ _ _ _ _ he'
    obtain ⟨e1, -, -, -⟩ := conj_uElt_coords hgU he
    rw [ha, mul_zero, one_mul] at e1
    exact d1 e1

theorem le_normalizer_inf_inner' {P : Type*} [Group P] {S X : Subgroup (MulAut P)}
    (hSX : S ≤ normalizer (X : Set (MulAut P))) :
    S ≤ normalizer ((X ⊓ inner P : Subgroup (MulAut P)) : Set (MulAut P)) :=
  le_normalizer_of_forall_conj_mem fun s hs y hy =>
    mem_inf.2 ⟨(mem_normalizer_iff.1 (hSX hs) y).1 (mem_inf.1 hy).1,
      (inner_normal _).conj_mem y (mem_inf.1 hy).2 s⟩

theorem swap_of_mem {R : Subgroup (MulAut (antiSp F))}
    (hU : R ⊓ inner (antiSp F) = (antiUnipotent F).map MulAut.conj)
    {s : MulAut (antiSp F)} (hsR : s ∈ R) {h : antiSp F} {j : ℕ} (hj : Odd j)
    (hs : s = MulAut.conj h * minorAut F ^ j) :
    (rootLong F).map s.toMonoidHom = rootShort F ∧ (rootShort F).map s.toMonoidHom = rootLong F ∧
      (radA1 F).map s.toMonoidHom = radA2 F ∧ (radA2 F).map s.toMonoidHom = radA1 F := by
  have hRN : R ≤ normalizer (((antiUnipotent F).map MulAut.conj :
      Subgroup (MulAut (antiSp F))) : Set (MulAut (antiSp F))) := by
    rw [← hU]
    exact le_normalizer_inf_inner' le_normalizer
  have hsU : (antiUnipotent F).map s.toMonoidHom = antiUnipotent F :=
    map_eq_of_mem_normalizer_conj conj_injective (hRN hsR)
  subst hs
  exact swap_of_odd hj hsU

theorem symplectic_standard_confinement {f : ℕ} (hf : 1 ≤ f) (hF : Nat.card F = 2 ^ f)
    {R : Subgroup (MulAut (antiSp F))}
    (hU : R ⊓ inner (antiSp F) = (antiUnipotent F).map MulAut.conj)
    {s : MulAut (antiSp F)} (hsR : s ∈ R) {h : antiSp F} {j : ℕ} (hj : Odd j)
    (hs : s = MulAut.conj h * minorAut F ^ j) (E : Subgroup (MulAut (antiSp F))) (hER : E ≤ R)
    (hRE : R ≤ normalizer (E : Set (MulAut (antiSp F)))) (hE : IsElementaryAbelian 2 ↥E) :
    E ≤ (antiUnipotentCenter F).map MulAut.conj := by
  have hι : Function.Injective (MulAut.conj : antiSp F →* MulAut (antiSp F)) := conj_injective
  have hRN : R ≤ normalizer (((antiUnipotent F).map MulAut.conj :
      Subgroup (MulAut (antiSp F))) : Set (MulAut (antiSp F))) := by
    rw [← hU]
    exact le_normalizer_inf_inner' le_normalizer
  obtain ⟨-, -, h1, h2⟩ := swap_of_mem hU hsR hj hs
  have hE2 : ∀ g ∈ E, g * g = 1 := fun g hg => by
    have h3 := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := E) g hg
    rwa [pow_two] at h3
  set YE := (E ⊓ inner (antiSp F)).comap
    (MulAut.conj : antiSp F →* MulAut (antiSp F)) with hYEdef
  have hYEmap : YE.map MulAut.conj = E ⊓ inner (antiSp F) :=
    map_comap_eq_self inf_le_right
  have hYEU : YE ≤ antiUnipotent F := fun g hg => by
    have h3 : MulAut.conj g ∈ R ⊓ inner (antiSp F) :=
      mem_inf.2 ⟨hER (mem_inf.1 hg).1, (mem_inf.1 hg).2⟩
    rw [hU] at h3
    exact (mem_map_iff_mem hι).1 h3
  have hYE2 : ∀ g ∈ YE, g * g = 1 := fun g hg => hι (by
    rw [map_mul, map_one]
    exact hE2 _ (mem_inf.1 hg).1)
  have hsYE : YE.map s.toMonoidHom = YE := by
    refine map_eq_of_mem_normalizer_conj hι ?_
    rw [hYEmap]
    exact le_normalizer_inf_inner' hRE hsR
  have hYEZ : YE ≤ antiUnipotentCenter F := by
    rw [← radA1_inf_radA2]
    rcases elementary_le_radA1_or_radA2 hYEU hYE2 with h3 | h3
    · refine le_inf h3 ?_
      calc YE = YE.map s.toMonoidHom := hsYE.symm
        _ ≤ (radA1 F).map s.toMonoidHom := map_mono h3
        _ = radA2 F := h1
    · refine le_inf ?_ h3
      calc YE = YE.map s.toMonoidHom := hsYE.symm
        _ ≤ (radA2 F).map s.toMonoidHom := map_mono h3
        _ = radA1 F := h2
  intro e he
  have heU : (antiUnipotent F).map e.toMonoidHom = antiUnipotent F :=
    map_eq_of_mem_normalizer_conj hι (hRN (hER he))
  have htriv : ∀ u ∈ antiUnipotent F, e u * u⁻¹ ∈ antiUnipotentCenter F := by
    intro u hu
    apply hYEZ
    show MulAut.conj (e u * u⁻¹) ∈ E ⊓ inner (antiSp F)
    have hcomm : MulAut.conj (e u * u⁻¹) =
        e * (MulAut.conj u * e⁻¹ * (MulAut.conj u)⁻¹) := by
      rw [map_mul, map_inv, ← aut_mul_conj_mul_inv]
      group
    have huR : MulAut.conj u ∈ R := by
      have h3 : MulAut.conj u ∈ R ⊓ inner (antiSp F) := by
        rw [hU]
        exact mem_map_of_mem _ hu
      exact (mem_inf.1 h3).1
    refine mem_inf.2 ⟨?_, ⟨_, rfl⟩⟩
    rw [hcomm]
    exact mul_mem he ((mem_normalizer_iff.1 (hRE huR) _).1 (inv_mem he))
  obtain ⟨v, -, hev⟩ := exists_eq_conj_of_trivial_mod_center_sp hf hF heU htriv
  have heI : e ∈ E ⊓ inner (antiSp F) := mem_inf.2 ⟨he, ⟨v, hev.symm⟩⟩
  rw [← hYEmap] at heI
  obtain ⟨w, hw, rfl⟩ := heI
  exact mem_map_of_mem _ (hYEZ hw)

omit [CharP F 2] [Finite F] in
theorem exists_unique_coatom_of {G : Type*} [Group G] {S B D : Subgroup G} (hSB : S ≤ B)
    (hBD : B < D) (hmax : ∀ Y : Subgroup G, S ≤ Y → Y < D → Y ≤ B) :
    ∃! M' : Subgroup ↥D, IsCoatom M' ∧ S.subgroupOf D ≤ M' := by
  have hBle : B ≤ D := hBD.le
  have hSsub : S.subgroupOf D ≤ B.subgroupOf D := fun x hx =>
    Subgroup.mem_subgroupOf.2 (hSB (Subgroup.mem_subgroupOf.1 hx))
  have htop : ∀ b : Subgroup ↥D, b.map D.subtype = D → b = ⊤ := by
    intro b hb
    apply Subgroup.map_injective D.subtype_injective
    rw [hb, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hle : ∀ b : Subgroup ↥D, S.subgroupOf D ≤ b → b ≠ ⊤ → b ≤ B.subgroupOf D := by
    intro b hSb hb
    have hYD : b.map D.subtype < D :=
      lt_of_le_of_ne (Subgroup.map_subtype_le b) fun h => hb (htop b h)
    have hSY : S ≤ b.map D.subtype := fun x hx =>
      ⟨⟨x, (hSB.trans hBle) hx⟩, hSb (Subgroup.mem_subgroupOf.2 hx), rfl⟩
    have h1 := hmax _ hSY hYD
    exact fun x hx => Subgroup.mem_subgroupOf.2 (h1 ⟨x, hx, rfl⟩)
  have hcoatom : IsCoatom (B.subgroupOf D) := by
    refine ⟨fun h => ?_, fun b hb => ?_⟩
    · apply hBD.not_ge
      intro x hx
      have h1 : (⟨x, hx⟩ : D) ∈ B.subgroupOf D := by
        rw [h]
        exact mem_top _
      exact Subgroup.mem_subgroupOf.1 h1
    · by_contra hne
      exact absurd (hle b (hSsub.trans hb.le) hne) (not_le_of_gt hb)
  refine ⟨B.subgroupOf D, ⟨hcoatom, hSsub⟩, fun b ⟨hb, hSb⟩ => ?_⟩
  exact eq_of_le_of_not_lt (hle b hSb hb.1) fun hlt => hcoatom.1 (hb.2 _ hlt)

theorem exists_odd_coset_mem {f : ℕ} (hf : 2 ≤ f) (hF : Nat.card F = 2 ^ f)
    {A R B : Subgroup (MulAut (antiSp F))} (hKR : inner (antiSp F) ⊔ R = A)
    (hR : IsSylowOf 2 R A) (hRB : R ≤ B) (hBA : B < A)
    (hBmax : ∀ Y : Subgroup (MulAut (antiSp F)), R ≤ Y → Y < A → Y ≤ B) :
    ∃ s ∈ R, ∃ (h : antiSp F) (j : ℕ), Odd j ∧ j < 2 * f ∧
      s = MulAut.conj h * minorAut F ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hφinj : Function.Injective (autCongr F).toMonoidHom := (autCongr F).injective
  have hinner : (CFSG.ComponentClassification.OuterAutomorphisms.inner (antiSp F)).map
      (autCongr F).toMonoidHom = CFSG.ComponentClassification.OuterAutomorphisms.inner
        (CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :=
    CFSG.ComponentClassification.OuterAutomorphisms.inner_map_congr (antiProjEquiv F)
  have hKA : inner (antiSp F) ≤ A := hKR ▸ le_sup_left
  have hBmax' : ∀ Y, R.map (autCongr F).toMonoidHom ≤ Y → Y < A.map (autCongr F).toMonoidHom →
      Y ≤ B.map (autCongr F).toMonoidHom := by
    intro Y hRY hYA
    have h1 : (Y.comap (autCongr F).toMonoidHom).map (autCongr F).toMonoidHom = Y :=
      map_comap_eq_self_of_surjective (autCongr F).surjective Y
    have h2 : R ≤ Y.comap (autCongr F).toMonoidHom := map_le_iff_le_comap.1 hRY
    have h3 : Y.comap (autCongr F).toMonoidHom < A := by
      rw [← map_lt_map_iff_of_injective hφinj, h1]
      exact hYA
    rw [← h1]
    exact map_mono (hBmax _ h2 h3)
  obtain ⟨s', hs', g, j, hjo, -, hj2, hsj⟩ :=
    CFSG.QuasithinUnique.Setup.X7b.unique_Sylow_overgroup_forces_odd_diagram_coset f F hf hF
      (A.map (autCongr F).toMonoidHom) (R.map (autCongr F).toMonoidHom)
      (hinner ▸ map_mono hKA) (map_mono hR.le)
      (by rw [← hinner, ← Subgroup.map_sup, hKR])
      (CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf.2
        (CFSG.QuasithinUnique.Setup.X6.isSylowOf_map_injective _ hφinj hR))
      (exists_unique_coatom_of (map_mono hRB) ((map_lt_map_iff_of_injective hφinj).2 hBA)
        hBmax')
  obtain ⟨s, hsR, rfl⟩ := hs'
  refine ⟨s, hsR, (antiSpEquiv F).symm g, j, hjo, hj2, (autCongr F).injective ?_⟩
  rw [map_mul, autCongr_conj, MulEquiv.apply_symm_apply, autCongr_pow, autCongr_minorAut]
  exact hsj

end Actions

end CFSG.Quasithin.SteinbergBS
