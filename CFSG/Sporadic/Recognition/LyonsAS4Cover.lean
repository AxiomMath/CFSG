module

public import CFSG.Sporadic.SchreierLemmas.MoorePresentation
public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Sporadic.Recognition.LyonsSims

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.SchreierLemmas
open scoped commutatorElement

structure IsCover11 {E : Type*} [Group E] (ρ : E →* Perm (Fin 11)) (z : E) : Prop where
  ne_one : z ≠ 1
  sq_eq_one : z ^ 2 = 1
  central : z ∈ Subgroup.center E
  ker_eq : ρ.ker = Subgroup.zpowers z
  range_eq : ρ.range = alternatingGroup (Fin 11)
  perfect : Group.IsPerfect E

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 11)} {z : E}

namespace IsCover11

theorem mem_ker_iff (h : IsCover11 ρ z) {x : E} : ρ x = 1 ↔ x = 1 ∨ x = z := by
  rw [← MonoidHom.mem_ker, h.ker_eq, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨n, rfl⟩
    have h2 : z ^ 2 = 1 := h.sq_eq_one
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' n
    · left
      rw [zpow_mul, zpow_two, ← pow_two, h2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, ← pow_two, h2, one_zpow, one_mul, zpow_one]
  · rintro (rfl | rfl)
    · exact ⟨0, by simp⟩
    · exact ⟨1, by simp⟩

theorem mul_z_comm (h : IsCover11 ρ z) (x : E) : x * z = z * x :=
  (Subgroup.mem_center_iff.mp h.central x)

theorem z_mul_z (h : IsCover11 ρ z) : z * z = 1 := by
  have := h.sq_eq_one
  rwa [pow_two] at this

theorem rho_z (h : IsCover11 ρ z) : ρ z = 1 := by
  rw [h.mem_ker_iff]; right; rfl

theorem rho_mul_z (h : IsCover11 ρ z) (x : E) : ρ (x * z) = ρ x := by
  rw [map_mul, h.rho_z, mul_one]

theorem eq_or_eq_mul_z (h : IsCover11 ρ z) {x y : E} (hxy : ρ x = ρ y) : y = x ∨ y = x * z := by
  have : ρ (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
  rcases h.mem_ker_iff.mp this with h1 | h1
  · left; rw [inv_mul_eq_one] at h1; exact h1.symm
  · right; rw [← h1]; group

theorem sign_rho (h : IsCover11 ρ z) (x : E) : sign (ρ x) = 1 := by
  have : ρ x ∈ alternatingGroup (Fin 11) := h.range_eq ▸ ⟨x, rfl⟩
  exact (mem_alternatingGroup).mp this

theorem exists_lift (h : IsCover11 ρ z) {p : Perm (Fin 11)} (hp : sign p = 1) : ∃ x, ρ x = p := by
  have : p ∈ ρ.range := h.range_eq ▸ (mem_alternatingGroup).mpr hp
  exact this

theorem sq_mem (h : IsCover11 ρ z) {x : E} (hx : ρ x ^ 2 = 1) : x ^ 2 = 1 ∨ x ^ 2 = z := by
  have : ρ (x ^ 2) = 1 := by rw [map_pow]; exact hx
  exact h.mem_ker_iff.mp this

theorem sq_central (h : IsCover11 ρ z) {x : E} (hx : ρ x ^ 2 = 1) (e : E) :
    e * x ^ 2 = x ^ 2 * e := by
  rcases h.sq_mem hx with h1 | h1
  · rw [h1]; simp
  · rw [h1]; exact h.mul_z_comm e

theorem sq_eq_of_lift_conj (h : IsCover11 ρ z) {x y : E} (hx : ρ x ^ 2 = 1) {g : Perm (Fin 11)}
    (hg : sign g = 1) (hconj : g * ρ x * g⁻¹ = ρ y) : y ^ 2 = x ^ 2 := by
  obtain ⟨g', hg'⟩ := h.exists_lift hg
  have h1 : ρ (g' * x * g'⁻¹) = ρ y := by rw [map_mul, map_mul, map_inv, hg', hconj]
  have hy2 : (g' * x * g'⁻¹) ^ 2 = x ^ 2 := by
    have : (g' * x * g'⁻¹) ^ 2 = g' * x ^ 2 * g'⁻¹ := by
      rw [pow_two, pow_two]; simp [mul_assoc]
    rw [this, h.sq_central hx g']; simp [mul_assoc]
  rcases h.eq_or_eq_mul_z h1 with h2 | h2
  · rw [h2, hy2]
  · rw [h2, (Commute.mul_pow (h.mul_z_comm _) 2), h.sq_eq_one, mul_one, hy2]

end IsCover11

theorem cycleType_of_involution_11 {σ : Perm (Fin 11)} (h2 : σ ^ 2 = 1) (h1 : σ ≠ 1)
    (hs : sign σ = 1) : σ.cycleType = {2, 2} ∨ σ.cycleType = {2, 2, 2, 2} := by
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have hd := dvd_of_mem_cycleType hn
    have hd2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have := Nat.le_of_dvd (by norm_num) (hd.trans hd2)
    have := two_le_of_mem_cycleType hn
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : σ.cycleType.sum = 2 * Multiset.card σ.cycleType := by
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate]; simp [mul_comm]
  have hle : σ.cycleType.sum ≤ 11 := by
    rw [sum_cycleType]
    have := Finset.card_le_univ σ.support
    simpa using this
  have hne : σ.cycleType ≠ 0 := fun h => h1 (cycleType_eq_zero.mp h)
  have hk0 : Multiset.card σ.cycleType ≠ 0 := fun h => hne (Multiset.card_eq_zero.mp h)
  have hsg := sign_of_cycleType σ
  rw [hs, hsum] at hsg
  have heven : Even (2 * Multiset.card σ.cycleType + Multiset.card σ.cycleType) :=
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hsg.symm
  rw [hsum] at hle
  obtain ⟨m, hm⟩ := heven
  have hk : Multiset.card σ.cycleType = 2 ∨ Multiset.card σ.cycleType = 4 := by omega
  rcases hk with hk | hk
  · left; rw [hrep, hk]; rfl
  · right; rw [hrep, hk]; rfl


theorem cycleType_of_sq_eq_one_11 {σ : Perm (Fin 11)} (h2 : σ ^ 2 = 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 2) 2 := by
  have hall : ∀ n ∈ σ.cycleType, n = 2 := by
    intro n hn
    have hd := dvd_of_mem_cycleType hn
    have hd2 : orderOf σ ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    have := Nat.le_of_dvd (by norm_num) (hd.trans hd2)
    have := two_le_of_mem_cycleType hn
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate.mpr ⟨rfl, hall⟩
  have hsum : σ.support.card = 2 * Multiset.card σ.cycleType := by
    rw [← sum_cycleType]
    conv_lhs => rw [hrep]
    rw [Multiset.sum_replicate]; simp [mul_comm]
  rw [hsum, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]
  exact hrep

theorem cycleType_type22_of_card_11 {σ : Perm (Fin 11)} (h2 : σ ^ 2 = 1)
    (hs : (Finset.univ.filter fun i => σ i ≠ i).card = 4) : σ.cycleType = {2, 2} := by
  rw [cycleType_of_sq_eq_one_11 h2]
  have : σ.support.card = 4 := hs
  rw [this]; rfl

theorem cycleType_type2222_of_card_11 {σ : Perm (Fin 11)} (h2 : σ ^ 2 = 1)
    (hs : (Finset.univ.filter fun i => σ i ≠ i).card = 8) : σ.cycleType = {2, 2, 2, 2} := by
  rw [cycleType_of_sq_eq_one_11 h2]
  have : σ.support.card = 8 := hs
  rw [this]; rfl

theorem moorePerm_cycleType22_11 : ∀ j ∈ Finset.Icc 2 9, (moorePerm 11 j).cycleType = {2, 2} := by
  have hdec : ∀ j ∈ Finset.Icc 2 9, moorePerm 11 j ^ 2 = 1 ∧
      (Finset.univ.filter fun i => moorePerm 11 j i ≠ i).card = 4 := by decide
  exact fun j hj => cycleType_type22_of_card_11 (hdec j hj).1 (hdec j hj).2

theorem moorePerm_mul_cycleType22_11 : ∀ i ∈ Finset.Icc 1 7, ∀ j ∈ Finset.Icc (i + 2) 9,
    (moorePerm 11 i * moorePerm 11 j).cycleType = {2, 2} := by
  have hdec : ∀ i ∈ Finset.Icc 1 7, ∀ j ∈ Finset.Icc (i + 2) 9,
      (moorePerm 11 i * moorePerm 11 j) ^ 2 = 1 ∧
      (Finset.univ.filter fun k => (moorePerm 11 i * moorePerm 11 j) k ≠ k).card = 4 := by decide
  exact fun i hi j hj => cycleType_type22_of_card_11 (hdec i hi j hj).1 (hdec i hi j hj).2

theorem moorePerm_246_cycleType2222_11 :
    (moorePerm 11 2 * moorePerm 11 4 * moorePerm 11 6).cycleType = {2, 2, 2, 2} := by
  have hdec : (moorePerm 11 2 * moorePerm 11 4 * moorePerm 11 6) ^ 2 = 1 ∧
      (Finset.univ.filter fun k =>
        (moorePerm 11 2 * moorePerm 11 4 * moorePerm 11 6) k ≠ k).card = 8 := by
    decide
  exact cycleType_type2222_of_card_11 hdec.1 hdec.2

theorem sq_eq_one_of_cycleType_two_11 {σ : Perm (Fin 11)} (h : ∀ n ∈ σ.cycleType, n = 2) :
    σ ^ 2 = 1 := by
  rw [← orderOf_dvd_iff_pow_eq_one, ← lcm_cycleType]
  exact Multiset.lcm_dvd.mpr fun n hn => (h n hn).symm ▸ dvd_rfl

theorem sq_eq_one_of_type22_11 {σ : Perm (Fin 11)} (h : σ.cycleType = {2, 2}) : σ ^ 2 = 1 :=
  sq_eq_one_of_cycleType_two_11 fun n hn => by rw [h] at hn; simpa using hn

theorem sq_eq_one_of_type2222_11 {σ : Perm (Fin 11)} (h : σ.cycleType = {2, 2, 2, 2}) : σ ^ 2 = 1 :=
  sq_eq_one_of_cycleType_two_11 fun n hn => by rw [h] at hn; simpa using hn

theorem sign_of_type22_11 {σ : Perm (Fin 11)} (h : σ.cycleType = {2, 2}) : sign σ = 1 := by
  rw [sign_of_cycleType, h]; decide

theorem sign_of_type2222_11 {σ : Perm (Fin 11)} (h : σ.cycleType = {2, 2, 2, 2}) : sign σ = 1 := by
  rw [sign_of_cycleType, h]; decide

theorem exists_even_conj_type22_11 {σ τ : Perm (Fin 11)} (hσ : σ.cycleType = {2, 2})
    (hτ : τ.cycleType = {2, 2}) : ∃ g : Perm (Fin 11), sign g = 1 ∧ g * σ * g⁻¹ = τ := by
  have hc : IsConj σ τ := isConj_iff_cycleType_eq.mpr (hσ.trans hτ.symm)
  have hs : σ.support.card + 2 ≤ Fintype.card (Fin 11) := by
    rw [← sum_cycleType, hσ]; simp
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (alternatingGroup.isConj_of (σ := ⟨σ, (mem_alternatingGroup).mpr (sign_of_type22_11 hσ)⟩)
      (τ := ⟨τ, (mem_alternatingGroup).mpr (sign_of_type22_11 hτ)⟩) hc hs)
  refine ⟨c, (mem_alternatingGroup).mp c.2, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

theorem exists_even_conj_type2222_11 {σ τ : Perm (Fin 11)} (hσ : σ.cycleType = {2, 2, 2, 2})
    (hτ : τ.cycleType = {2, 2, 2, 2}) :
    ∃ g : Perm (Fin 11), sign g = 1 ∧ g * σ * g⁻¹ = τ := by
  have hc : IsConj σ τ := isConj_iff_cycleType_eq.mpr (hσ.trans hτ.symm)
  have hs : σ.support.card + 2 ≤ Fintype.card (Fin 11) := by
    rw [← sum_cycleType, hσ]; simp
  obtain ⟨c, hc⟩ := isConj_iff.mp
    (alternatingGroup.isConj_of (σ := ⟨σ, (mem_alternatingGroup).mpr (sign_of_type2222_11 hσ)⟩)
      (τ := ⟨τ, (mem_alternatingGroup).mpr (sign_of_type2222_11 hτ)⟩) hc hs)
  refine ⟨c, (mem_alternatingGroup).mp c.2, ?_⟩
  have := congrArg Subtype.val hc
  simpa using this

namespace IsCover11

theorem sq_eq_of_type22 (h : IsCover11 ρ z) {x y : E} (hx : (ρ x).cycleType = {2, 2})
    (hy : (ρ y).cycleType = {2, 2}) : y ^ 2 = x ^ 2 := by
  obtain ⟨g, hg, hc⟩ := exists_even_conj_type22_11 hx hy
  exact h.sq_eq_of_lift_conj (sq_eq_one_of_type22_11 hx) hg hc

theorem sq_eq_of_type2222 (h : IsCover11 ρ z) {x y : E} (hx : (ρ x).cycleType = {2, 2, 2, 2})
    (hy : (ρ y).cycleType = {2, 2, 2, 2}) : y ^ 2 = x ^ 2 := by
  obtain ⟨g, hg, hc⟩ := exists_even_conj_type2222_11 hx hy
  exact h.sq_eq_of_lift_conj (sq_eq_one_of_type2222_11 hx) hg hc

theorem exists_lift_cube_one (h : IsCover11 ρ z) {p : Perm (Fin 11)} (hp : sign p = 1)
    (hp3 : p ^ 3 = 1) : ∃ c : E, ρ c = p ∧ c ^ 3 = 1 := by
  obtain ⟨d, hd⟩ := h.exists_lift hp
  have hd3 : ρ (d ^ 3) = 1 := by rw [map_pow, hd, hp3]
  rcases h.mem_ker_iff.mp hd3 with h1 | h1
  · exact ⟨d, hd, h1⟩
  · refine ⟨d * z, by rw [h.rho_mul_z, hd], ?_⟩
    rw [(Commute.mul_pow (h.mul_z_comm d) 3), h1]
    have : z ^ 3 = z := by rw [pow_succ, h.sq_eq_one, one_mul]
    rw [this, h.z_mul_z]

theorem exists_lift_next (h : IsCover11 ρ z) {a : E} {q : Perm (Fin 11)} (hq : sign q = 1)
    (hpq : (ρ a * q) ^ 3 = 1) : ∃ b : E, ρ b = q ∧ (a * b) ^ 3 = 1 := by
  obtain ⟨d, hd⟩ := h.exists_lift hq
  have hd3 : ρ ((a * d) ^ 3) = 1 := by rw [map_pow, map_mul, hd, hpq]
  rcases h.mem_ker_iff.mp hd3 with h1 | h1
  · exact ⟨d, hd, h1⟩
  · refine ⟨d * z, by rw [h.rho_mul_z, hd], ?_⟩
    rw [← mul_assoc, (Commute.mul_pow (h.mul_z_comm (a * d)) 3), h1]
    have : z ^ 3 = z := by rw [pow_succ, h.sq_eq_one, one_mul]
    rw [this, h.z_mul_z]


theorem comm_mul_z_left (h : IsCover11 ρ z) (e f : E) : ⁅e * z, f⁆ = ⁅e, f⁆ := by
  have hw := h.mul_z_comm f
  calc ⁅e * z, f⁆ = e * (z * f) * (z⁻¹ * e⁻¹) * f⁻¹ := by simp [commutatorElement_def, mul_assoc]
    _ = e * (f * z) * (z⁻¹ * e⁻¹) * f⁻¹ := by rw [← hw]
    _ = ⁅e, f⁆ := by simp [commutatorElement_def, mul_assoc]

theorem comm_mul_z_right (h : IsCover11 ρ z) (e f : E) : ⁅e, f * z⁆ = ⁅e, f⁆ := by
  have hw := h.mul_z_comm e
  calc ⁅e, f * z⁆ = e * f * z * e⁻¹ * (z⁻¹ * f⁻¹) := by simp [commutatorElement_def, mul_assoc]
    _ = e * f * (z * e⁻¹) * (z⁻¹ * f⁻¹) := by simp [mul_assoc]
    _ = e * f * (e⁻¹ * z) * (z⁻¹ * f⁻¹) := by
        rw [(h.mul_z_comm e⁻¹).symm]
    _ = ⁅e, f⁆ := by simp [commutatorElement_def, mul_assoc]

theorem exists_moore_lifts (h : IsCover11 ρ z) :
    ∃ c : ℕ → E, (∀ i ∈ Finset.Icc 1 9, ρ (c i) = moorePerm 11 i) ∧ c 1 ^ 3 = 1 ∧
      ∀ j ∈ Finset.Icc 2 9, (c (j - 1) * c j) ^ 3 = 1 := by
  obtain ⟨c1, hc1, hc13⟩ := h.exists_lift_cube_one (p := moorePerm 11 1) (sign_moorePerm 1)
    (by decide)
  obtain ⟨c2, hc2, hc23⟩ := h.exists_lift_next (a := c1) (q := moorePerm 11 2) (sign_moorePerm 2)
    (by rw [hc1]; decide)
  obtain ⟨c3, hc3, hc33⟩ := h.exists_lift_next (a := c2) (q := moorePerm 11 3) (sign_moorePerm 3)
    (by rw [hc2]; decide)
  obtain ⟨c4, hc4, hc43⟩ := h.exists_lift_next (a := c3) (q := moorePerm 11 4) (sign_moorePerm 4)
    (by rw [hc3]; decide)
  obtain ⟨c5, hc5, hc53⟩ := h.exists_lift_next (a := c4) (q := moorePerm 11 5) (sign_moorePerm 5)
    (by rw [hc4]; decide)
  obtain ⟨c6, hc6, hc63⟩ := h.exists_lift_next (a := c5) (q := moorePerm 11 6) (sign_moorePerm 6)
    (by rw [hc5]; decide)
  obtain ⟨c7, hc7, hc73⟩ := h.exists_lift_next (a := c6) (q := moorePerm 11 7) (sign_moorePerm 7)
    (by rw [hc6]; decide)
  obtain ⟨c8, hc8, hc83⟩ := h.exists_lift_next (a := c7) (q := moorePerm 11 8) (sign_moorePerm 8)
    (by rw [hc7]; decide)
  obtain ⟨c9, hc9, hc93⟩ := h.exists_lift_next (a := c8) (q := moorePerm 11 9) (sign_moorePerm 9)
    (by rw [hc8]; decide)
  refine ⟨fun i => [1, c1, c2, c3, c4, c5, c6, c7, c8, c9].getD i 1, ?_, ?_, ?_⟩
  · intro i hi
    simp only [Finset.mem_Icc] at hi
    obtain ⟨hi1, hi2⟩ := hi
    interval_cases i <;> simpa
  · simpa using hc13
  · intro j hj
    simp only [Finset.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    interval_cases j <;> simpa

theorem sq_eq_z_of_type22 (h : IsCover11 ρ z) {x : E} (hx : (ρ x).cycleType = {2, 2}) :
    x ^ 2 = z := by
  by_contra hne
  have h1 : x ^ 2 = 1 := (h.sq_mem (sq_eq_one_of_type22_11 hx)).resolve_right hne
  have hall : ∀ y : E, (ρ y).cycleType = {2, 2} → y ^ 2 = 1 :=
    fun y hy => (h.sq_eq_of_type22 hx hy).trans h1
  have htype := moorePerm_cycleType22_11
  have htype2 := moorePerm_mul_cycleType22_11
  obtain ⟨c, hcρ, hc1, hcadj⟩ := h.exists_moore_lifts
  have hM : IsMooreFamily (11 - 2) c := by
    refine ⟨hc1, ?_, ?_, ?_⟩
    · intro j hj2 hj6
      apply hall
      rw [hcρ j (by simp only [Finset.mem_Icc]; omega)]
      exact htype j (by simp only [Finset.mem_Icc]; omega)
    · intro j hj2 hj6
      exact hcadj j (by simp only [Finset.mem_Icc]; omega)
    · intro i j hi hij hj
      apply hall
      rw [map_mul, hcρ i (by simp only [Finset.mem_Icc]; omega),
        hcρ j (by simp only [Finset.mem_Icc]; omega)]
      exact htype2 i (by simp only [Finset.mem_Icc]; omega) j
        (by simp only [Finset.mem_Icc]; omega)
  have hne2 : ∃ i ∈ Set.Icc 1 (11 - 2), c i ≠ 1 := by
    refine ⟨2, ⟨by norm_num, by norm_num⟩, fun h2 => ?_⟩
    have := hcρ 2 (by simp)
    rw [h2, map_one] at this
    have h3 : (moorePerm 11 2).cycleType = {2, 2} := htype 2 (by simp)
    rw [← this] at h3
    simp at h3
  obtain ⟨⟨-, hclos⟩, ⟨φ, hφ, -⟩, -, -, -, hinj⟩ :=
    moore_alternating_presentation (n := 11) (by norm_num) c hM
  have hφinj : Function.Injective φ := (hinj (by norm_num) hne2).1 φ hφ
  let ρ' : E →* alternatingGroup (Fin 11) :=
    ρ.codRestrict (alternatingGroup (Fin 11)) (fun e => (mem_alternatingGroup).mpr (h.sign_rho e))
  have hρφ : ∀ g : alternatingGroup (Fin 11), ρ (φ g) = (g : Perm (Fin 11)) := by
    have : ρ.comp φ = (alternatingGroup (Fin 11)).subtype := by
      apply MonoidHom.eq_of_eqOn_dense hclos
      rintro _ ⟨i, hi, rfl⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
      rw [hφ i hi]
      simp only [Set.mem_Icc] at hi
      rw [hcρ i (by simp only [Finset.mem_Icc]; exact hi)]
      rfl
    intro g
    exact DFunLike.congr_fun this g
  have hψρ : ∀ e : E, ρ (φ (ρ' e)) = ρ e := fun e => hρφ (ρ' e)
  have hψ : ∀ e : E, φ (ρ' e) = e ∨ φ (ρ' e) = e * z :=
    fun e => h.eq_or_eq_mul_z (hψρ e).symm
  have hcomm : ∀ e f : E, ⁅e, f⁆ ∈ φ.range := by
    intro e f
    have hmap : φ (ρ' ⁅e, f⁆) = ⁅φ (ρ' e), φ (ρ' f)⁆ := by simp
    have hc : ⁅φ (ρ' e), φ (ρ' f)⁆ = ⁅e, f⁆ := by
      rcases hψ e with h1 | h1 <;> rcases hψ f with h2 | h2 <;> rw [h1, h2] <;>
        simp [h.comm_mul_z_left, h.comm_mul_z_right]
    exact ⟨ρ' ⁅e, f⁆, by rw [hmap, hc]⟩
  have htop : (⊤ : Subgroup E) ≤ φ.range := by
    have hp := Group.isPerfect_def.mp h.perfect
    rw [← hp, commutator_eq_closure, Subgroup.closure_le]
    rintro _ ⟨e, f, rfl⟩
    exact hcomm e f
  obtain ⟨g, hg⟩ := htop (Subgroup.mem_top z)
  have hg1 : g = 1 := by
    apply Subtype.ext
    have := hρφ g
    rw [hg, h.rho_z] at this
    simpa using this.symm
  apply h.ne_one
  rw [← hg, hg1, map_one]


theorem inv_eq_mul_z_of_sq (h : IsCover11 ρ z) {w : E} (hw : w ^ 2 = z) : w⁻¹ = z * w := by
  apply inv_eq_of_mul_eq_one_left
  rw [mul_assoc, ← pow_two, hw, h.z_mul_z]

theorem anticomm_of_sq (h : IsCover11 ρ z) {a b : E} (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hab : (a * b) ^ 2 = z) : a * b = z * (b * a) := by
  have h1 : (a * b) * (a * b) = z := by rw [← pow_two]; exact hab
  have h2 : a * b = z * (a * b)⁻¹ := by
    calc a * b = (a * b) * (a * b) * (a * b)⁻¹ := by group
      _ = z * (a * b)⁻¹ := by rw [h1]
  rw [h2, mul_inv_rev, h.inv_eq_mul_z_of_sq ha, h.inv_eq_mul_z_of_sq hb]
  have hc : ∀ x : E, x * z = z * x := h.mul_z_comm
  calc z * (z * b * (z * a)) = z * (z * (b * z) * a) := by simp [mul_assoc]
    _ = z * (z * (z * b) * a) := by rw [hc b]
    _ = (z * z) * (z * (b * a)) := by simp [mul_assoc]
    _ = z * (b * a) := by rw [h.z_mul_z, one_mul]
    _ = z * (b * a) := rfl

theorem sq_triple (h : IsCover11 ρ z) {a b c : E} (h1 : a * b = z * (b * a))
    (h2 : a * c = z * (c * a)) (h3 : b * c = z * (c * b)) :
    (a * b * c) ^ 2 = z * (a ^ 2 * b ^ 2 * c ^ 2) := by
  have hc : ∀ x : E, x * z = z * x := h.mul_z_comm
  have hzz : z * z = 1 := h.z_mul_z
  have h2' : c * a = z * (a * c) := by
    calc c * a = (z * z) * (c * a) := by rw [hzz, one_mul]
      _ = z * (z * (c * a)) := by rw [mul_assoc]
      _ = z * (a * c) := by rw [← h2]
  have h1' : b * a = z * (a * b) := by
    calc b * a = (z * z) * (b * a) := by rw [hzz, one_mul]
      _ = z * (z * (b * a)) := by rw [mul_assoc]
      _ = z * (a * b) := by rw [← h1]
  have h3' : c * b = z * (b * c) := by
    calc c * b = (z * z) * (c * b) := by rw [hzz, one_mul]
      _ = z * (z * (c * b)) := by rw [mul_assoc]
      _ = z * (b * c) := by rw [← h3]
  have pz : ∀ x y : E, x * (z * y) = z * (x * y) := by
    intro x y; rw [← mul_assoc, hc x, mul_assoc]
  calc (a * b * c) ^ 2 = a * b * (c * a) * b * c := by rw [pow_two]; simp [mul_assoc]
    _ = a * b * (z * (a * c)) * b * c := by rw [h2']
    _ = z * (a * (b * a) * c * b * c) := by
        simp only [mul_assoc, pz]
    _ = z * (a * (z * (a * b)) * c * b * c) := by rw [h1']
    _ = z * (z * (a * a * b * c * b * c)) := by
        simp only [mul_assoc, pz]
    _ = a * a * b * c * b * c := by rw [← mul_assoc, hzz, one_mul]
    _ = a * a * b * (c * b) * c := by simp [mul_assoc]
    _ = a * a * b * (z * (b * c)) * c := by rw [h3']
    _ = z * (a ^ 2 * b ^ 2 * c ^ 2) := by
        simp only [mul_assoc, pz, pow_two]


theorem sq_eq_one_of_type2222_lift (h : IsCover11 ρ z) {x : E}
    (hx : (ρ x).cycleType = {2, 2, 2, 2}) :
    x ^ 2 = 1 := by
  have hm := moorePerm_cycleType22_11
  have hm2 := moorePerm_mul_cycleType22_11
  obtain ⟨c2, hc2⟩ := h.exists_lift (sign_moorePerm (n := 11) 2)
  obtain ⟨c4, hc4⟩ := h.exists_lift (sign_moorePerm (n := 11) 4)
  obtain ⟨c6, hc6⟩ := h.exists_lift (sign_moorePerm (n := 11) 6)
  have s2 : c2 ^ 2 = z := h.sq_eq_z_of_type22 (by rw [hc2]; exact hm 2 (by simp))
  have s4 : c4 ^ 2 = z := h.sq_eq_z_of_type22 (by rw [hc4]; exact hm 4 (by simp))
  have s6 : c6 ^ 2 = z := h.sq_eq_z_of_type22 (by rw [hc6]; exact hm 6 (by simp))
  have s24 : (c2 * c4) ^ 2 = z := h.sq_eq_z_of_type22 (by
    rw [map_mul, hc2, hc4]; exact hm2 2 (by simp) 4 (by simp))
  have s26 : (c2 * c6) ^ 2 = z := h.sq_eq_z_of_type22 (by
    rw [map_mul, hc2, hc6]; exact hm2 2 (by simp) 6 (by simp))
  have s46 : (c4 * c6) ^ 2 = z := h.sq_eq_z_of_type22 (by
    rw [map_mul, hc4, hc6]; exact hm2 4 (by simp) 6 (by simp))
  have htri := h.sq_triple (h.anticomm_of_sq s2 s4 s24) (h.anticomm_of_sq s2 s6 s26)
    (h.anticomm_of_sq s4 s6 s46)
  have h1 : (c2 * c4 * c6) ^ 2 = 1 := by
    rw [htri, s2, s4, s6]
    calc z * (z * z * z) = (z * z) * (z * z) := by simp [mul_assoc]
      _ = 1 := by rw [h.z_mul_z, one_mul]
  have hty : (ρ (c2 * c4 * c6)).cycleType = {2, 2, 2, 2} := by
    rw [map_mul, map_mul, hc2, hc4, hc6]; exact moorePerm_246_cycleType2222_11
  rw [h.sq_eq_of_type2222 hty hx] at *
  exact h1

theorem conj_mul_z_of_sq (h : IsCover11 ρ z) {a b : E} (ha : a ^ 2 = 1) (hb : b ^ 2 = z)
    (hab : (a * b) ^ 2 = 1) : b * a * b⁻¹ = a * z := by
  have ha' : a⁻¹ = a := by
    apply inv_eq_of_mul_eq_one_right; rw [← pow_two]; exact ha
  have h1 : (a * b)⁻¹ = a * b := by
    apply inv_eq_of_mul_eq_one_right; rw [← pow_two]; exact hab
  have e1 : a * b = z * (b * a) := by
    calc a * b = (a * b)⁻¹ := h1.symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = z * b * a := by rw [h.inv_eq_mul_z_of_sq hb, ha']
      _ = z * (b * a) := by rw [mul_assoc]
  have e2 : b * a = z * (a * b) := by
    calc b * a = (z * z) * (b * a) := by rw [h.z_mul_z, one_mul]
      _ = z * (z * (b * a)) := by rw [mul_assoc]
      _ = z * (a * b) := by rw [← e1]
  calc b * a * b⁻¹ = z * (a * b) * b⁻¹ := by rw [e2]
    _ = z * a := by group
    _ = a * z := (h.mul_z_comm a).symm

theorem conj_mul_z_of_sq_sq (h : IsCover11 ρ z) {a b : E} (ha : a ^ 2 = z) (hb : b ^ 2 = z)
    (hab : (a * b) ^ 2 = z) : b * a * b⁻¹ = a * z := by
  have e1 := h.anticomm_of_sq ha hb hab
  have e2 : b * a = z * (a * b) := by
    calc b * a = (z * z) * (b * a) := by rw [h.z_mul_z, one_mul]
      _ = z * (z * (b * a)) := by rw [mul_assoc]
      _ = z * (a * b) := by rw [← e1]
  calc b * a * b⁻¹ = z * (a * b) * b⁻¹ := by rw [e2]
    _ = z * a := by group
    _ = a * z := (h.mul_z_comm a).symm

theorem conj_z (h : IsCover11 ρ z) (g : E) : g * z * g⁻¹ = z := by
  rw [h.mul_z_comm g]; group

theorem conj_mul_z (h : IsCover11 ρ z) (g w : E) : g * (w * z) * g⁻¹ = g * w * g⁻¹ * z := by
  calc g * (w * z) * g⁻¹ = (g * w * g⁻¹) * (g * z * g⁻¹) := by group
    _ = g * w * g⁻¹ * z := by rw [h.conj_z]

theorem exists_conj_mul_z_of_even_conj (h : IsCover11 ρ z) {a₀ p₀ x : E}
    (hp : p₀ * a₀ * p₀⁻¹ = a₀ * z) {g : Perm (Fin 11)} (hg : sign g = 1)
    (hgx : g * ρ a₀ * g⁻¹ = ρ x) : ∃ p : E, p * x * p⁻¹ = x * z := by
  obtain ⟨g', hg'⟩ := h.exists_lift hg
  have h1 : ρ (g' * a₀ * g'⁻¹) = ρ x := by rw [map_mul, map_mul, map_inv, hg', hgx]
  refine ⟨g' * p₀ * g'⁻¹, ?_⟩
  have key : (g' * p₀ * g'⁻¹) * (g' * a₀ * g'⁻¹) * (g' * p₀ * g'⁻¹)⁻¹ =
      (g' * a₀ * g'⁻¹) * z := by
    calc (g' * p₀ * g'⁻¹) * (g' * a₀ * g'⁻¹) * (g' * p₀ * g'⁻¹)⁻¹
        = g' * (p₀ * a₀ * p₀⁻¹) * g'⁻¹ := by group
      _ = g' * (a₀ * z) * g'⁻¹ := by rw [hp]
      _ = (g' * a₀ * g'⁻¹) * z := h.conj_mul_z g' a₀
  rcases h.eq_or_eq_mul_z h1 with h2 | h2
  · rw [h2, key]
  · rw [h2, h.conj_mul_z, key]

theorem type2222_of_involution (h : IsCover11 ρ z) {x : E} (hx : x ^ 2 = 1) (h1 : x ≠ 1)
    (hz : x ≠ z) : (ρ x).cycleType = {2, 2, 2, 2} := by
  have h2 : ρ x ^ 2 = 1 := by rw [← map_pow, hx, map_one]
  have hne : ρ x ≠ 1 := fun e => by
    rcases h.mem_ker_iff.mp e with e | e
    · exact h1 e
    · exact hz e
  rcases cycleType_of_involution_11 h2 hne (h.sign_rho x) with ht | ht
  · exfalso
    have := h.sq_eq_z_of_type22 ht
    rw [hx] at this
    exact h.ne_one this.symm
  · exact ht

theorem isInvolution_of_type2222 (h : IsCover11 ρ z) {x : E}
    (hx : (ρ x).cycleType = {2, 2, 2, 2}) : x ^ 2 = 1 ∧ x ≠ 1 ∧ x ≠ z := by
  have hne : ρ x ≠ 1 := fun e => by
    have : (ρ x).cycleType = 0 := by rw [e]; exact cycleType_one
    rw [hx] at this; simp at this
  refine ⟨h.sq_eq_one_of_type2222_lift hx, fun e => hne (by rw [e, map_one]), fun e => hne ?_⟩
  rw [e]; exact h.rho_z

theorem eq_of_rho_eq_of_pow_three (h : IsCover11 ρ z) {x y : E} (hx : x ^ 3 = 1) (hy : y ^ 3 = 1)
    (hxy : ρ x = ρ y) : x = y := by
  rcases h.eq_or_eq_mul_z hxy with h1 | h1
  · exact h1.symm
  · exfalso
    have h3 : (x * z) ^ 3 = z := by
      rw [Commute.mul_pow (h.mul_z_comm x), hx, one_mul, pow_succ, h.sq_eq_one, one_mul]
    rw [← h1, hy] at h3
    exact h.ne_one h3.symm

theorem existsUnique_pow_three_lift (h : IsCover11 ρ z) {p : Perm (Fin 11)} (hp : sign p = 1)
    (hp3 : p ^ 3 = 1) : ∃! c : E, ρ c = p ∧ c ^ 3 = 1 := by
  obtain ⟨c, hc, hc3⟩ := h.exists_lift_cube_one hp hp3
  exact ⟨c, ⟨hc, hc3⟩, fun d hd => h.eq_of_rho_eq_of_pow_three hd.2 hc3 (hd.1.trans hc.symm)⟩

theorem commute_of_rho_commute_pow_three (h : IsCover11 ρ z) {x : E} (hx : x ^ 3 = 1) {g : E}
    (hg : ρ g * ρ x = ρ x * ρ g) : g * x = x * g := by
  have h1 : ρ (g * x * g⁻¹) = ρ x := by
    rw [map_mul, map_mul, map_inv, hg]; group
  have h2 : (g * x * g⁻¹) ^ 3 = 1 := by
    rw [conj_pow, hx]; group
  have := h.eq_of_rho_eq_of_pow_three h2 hx h1
  calc g * x = g * x * g⁻¹ * g := by group
    _ = x * g := by rw [this]

theorem orderOf_z (h : IsCover11 ρ z) : orderOf z = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime h.sq_eq_one h.ne_one

theorem card_ker (h : IsCover11 ρ z) : Nat.card ρ.ker = 2 := by
  rw [h.ker_eq, Nat.card_zpowers, h.orderOf_z]

theorem map_centralizer (h : IsCover11 ρ z) {x : E} (hx : x ^ 3 = 1) :
    (centralizer ({x} : Set E)).map ρ =
      centralizer ({ρ x} : Set (Perm (Fin 11))) ⊓ alternatingGroup (Fin 11) := by
  ext σ
  simp only [Subgroup.mem_map, Subgroup.mem_inf, mem_centralizer_singleton_iff,
    mem_alternatingGroup]
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨?_, h.sign_rho g⟩
    rw [← map_mul, ← map_mul, hg]
  · rintro ⟨hc, hs⟩
    obtain ⟨g, hg⟩ := h.exists_lift hs
    refine ⟨g, ?_, hg⟩
    exact h.commute_of_rho_commute_pow_three hx (by rw [hg]; exact hc)

theorem card_centralizer (h : IsCover11 ρ z) {x : E} (hx : x ^ 3 = 1) :
    Nat.card ↥(centralizer ({x} : Set E)) =
      2 * Nat.card ↥(centralizer ({ρ x} : Set (Perm (Fin 11))) ⊓ alternatingGroup (Fin 11)) := by
  set K : Subgroup E := centralizer ({x} : Set E) with hK
  have hzK : z ∈ K := by
    rw [hK, mem_centralizer_singleton_iff]
    exact (h.mul_z_comm x).symm
  have hker : ρ.ker ≤ K := by
    rw [h.ker_eq, Subgroup.zpowers_le]; exact hzK
  have h1 := Subgroup.card_ker_mul_card_range (ρ.domRestrict K)
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, h.map_centralizer hx,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv, h.card_ker] at h1
  exact h1.symm

theorem card_comap (h : IsCover11 ρ z) {S : Subgroup (Perm (Fin 11))}
    (hS : S ≤ alternatingGroup (Fin 11)) : Nat.card ↥(S.comap ρ) = 2 * Nat.card ↥S := by
  have hker : ρ.ker ≤ S.comap ρ := fun x hx => by
    simp [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
  have h1 := Subgroup.card_ker_mul_card_range (ρ.domRestrict (S.comap ρ))
  rw [MonoidHom.ker_domRestrict, MonoidHom.domRestrict_range, Subgroup.map_comap_eq, h.range_eq,
    inf_eq_right.mpr hS, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hker).toEquiv,
    h.card_ker] at h1
  exact h1.symm

end IsCover11

private def permC0 : Perm (Fin 11) := swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7
private def permQ0 : Perm (Fin 11) := swap 0 2 * swap 1 3

private theorem cycleType_permC0 : permC0.cycleType = {2, 2, 2, 2} := by
  unfold permC0
  exact cycleType_type2222_of_card_11 (by decide) (by decide)
private theorem cycleType_permQ0 : permQ0.cycleType = {2, 2} := by
  unfold permQ0
  exact cycleType_type22_of_card_11 (by decide) (by decide)
private theorem cycleType_permC0Q0 : (permC0 * permQ0).cycleType = {2, 2, 2, 2} := by
  unfold permC0 permQ0
  exact cycleType_type2222_of_card_11 (by decide) (by decide)

namespace IsCover11

variable {E : Type*} [Group E] {ρ : E →* Perm (Fin 11)} {z : E}

theorem exists_conj_mul_z_type2222 (h : IsCover11 ρ z) {x : E}
    (hx : (ρ x).cycleType = {2, 2, 2, 2}) : ∃ p : E, p * x * p⁻¹ = x * z := by
  obtain ⟨a, ha⟩ := h.exists_lift (sign_of_type2222_11 cycleType_permC0)
  obtain ⟨b, hb⟩ := h.exists_lift (sign_of_type22_11 cycleType_permQ0)
  have ha2 : a ^ 2 = 1 := h.sq_eq_one_of_type2222_lift (by rw [ha]; exact cycleType_permC0)
  have hb2 : b ^ 2 = z := h.sq_eq_z_of_type22 (by rw [hb]; exact cycleType_permQ0)
  have hab : (a * b) ^ 2 = 1 :=
    h.sq_eq_one_of_type2222_lift (by rw [map_mul, ha, hb]; exact cycleType_permC0Q0)
  obtain ⟨g, hg, hgc⟩ := exists_even_conj_type2222_11 cycleType_permC0 hx
  exact h.exists_conj_mul_z_of_even_conj (h.conj_mul_z_of_sq ha2 hb2 hab) hg
    (by rw [ha]; exact hgc)

theorem exists_conj_of_involutions (h : IsCover11 ρ z) {x y : E} (hx : x ^ 2 = 1) (hx1 : x ≠ 1)
    (hxz : x ≠ z) (hy : y ^ 2 = 1) (hy1 : y ≠ 1) (hyz : y ≠ z) :
    ∃ g : E, g * x * g⁻¹ = y := by
  have tx := h.type2222_of_involution hx hx1 hxz
  have ty := h.type2222_of_involution hy hy1 hyz
  obtain ⟨g, hg, hgc⟩ := exists_even_conj_type2222_11 tx ty
  obtain ⟨g', hg'⟩ := h.exists_lift hg
  have h1 : ρ (g' * x * g'⁻¹) = ρ y := by rw [map_mul, map_mul, map_inv, hg', hgc]
  rcases h.eq_or_eq_mul_z h1 with h2 | h2
  · exact ⟨g', h2.symm⟩
  · have tw : (ρ (g' * x * g'⁻¹)).cycleType = {2, 2, 2, 2} := by
      rw [h1]; exact ty
    obtain ⟨p, hp⟩ := h.exists_conj_mul_z_type2222 tw
    exact ⟨p * g', by rw [h2, ← hp]; group⟩

end IsCover11


end CFSG.Sporadic.Recognition.LyonsSims
