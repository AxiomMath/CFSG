module

public import CFSG.RankThree.PartTwo.Sec4.Item424Res2ProofSeven
public import CFSG.RankThree.PartTwo.Sec4.Item423Res2ProofCharThree

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)
open Matrix
open scoped MatrixGroups

namespace Item424Res2

open Res423Two Item434CharThree

theorem exists_pow_four_of_map_eq {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {D : Subgroup X} {F : Subgroup Y} (hDF : D.map e.toMonoidHom = F)
    (hF : ∃ ρ ∈ autIn (⊤ : Subgroup Y) F, ρ ^ 4 = 1 ∧ ρ ^ 2 ≠ 1) :
    ∃ σ ∈ autIn (⊤ : Subgroup X) D, σ ^ 4 = 1 ∧ σ ^ 2 ≠ 1 := by
  obtain ⟨ρ, hρ, h4, h2⟩ := hF
  have f := Sporadic.autInTopCongr e D
  rw [hDF] at f
  refine exists_pow_four_of_mulEquiv f (m := ⟨ρ, hρ⟩) ?_ ?_
  · exact Subtype.ext (by rw [Subgroup.coe_pow]; exact h4)
  · intro h
    exact h2 (by simpa using congrArg Subtype.val h)

section Field

variable {K : Type} [Field K]

@[expose] def rCenterMat : Matrix (Fin 3) (Fin 3) K := !![1, 0, 0; 0, 0, 1; 0, -1, 0]

@[expose] def rAxisMat : Matrix (Fin 3) (Fin 3) K := !![0, 1, 0; -1, 0, 0; 0, 0, 1]

@[expose] def rCenter : SL(3, K) := ⟨rCenterMat, by simp [rCenterMat, Matrix.det_fin_three]⟩

@[expose] def rAxis : SL(3, K) := ⟨rAxisMat, by simp [rAxisMat, Matrix.det_fin_three]⟩

theorem rCenter_mul_uSL (a c : K) : rCenter * uSL a 0 c = uSL c 0 (-a) * rCenter := by
  apply Subtype.ext
  change rCenterMat * CFSG.SectionRank.OddCover.u3Mat a 0 c =
    CFSG.SectionRank.OddCover.u3Mat c 0 (-a) * rCenterMat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rCenterMat, CFSG.SectionRank.OddCover.u3Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem rAxis_mul_uSL (b c : K) : rAxis * uSL 0 b c = uSL 0 (-c) b * rAxis := by
  apply Subtype.ext
  change rAxisMat * CFSG.SectionRank.OddCover.u3Mat 0 b c =
    CFSG.SectionRank.OddCover.u3Mat 0 (-c) b * rAxisMat
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rAxisMat, CFSG.SectionRank.OddCover.u3Mat, Matrix.mul_apply, Fin.sum_univ_three]

theorem rCenter_pow_four : (rCenter : SL(3, K)) ^ 4 = 1 := by
  apply Subtype.ext
  change rCenterMat ^ 4 = 1
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rCenterMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem rAxis_pow_four : (rAxis : SL(3, K)) ^ 4 = 1 := by
  apply Subtype.ext
  change rAxisMat ^ 4 = 1
  rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rAxisMat, Matrix.mul_apply, Fin.sum_univ_three]

theorem rCenter_sq_conj (a c : K) :
    rCenter ^ 2 * uSL a 0 c * (rCenter ^ 2)⁻¹ = uSL (-a) 0 (-c) := by
  rw [sq, mul_assoc rCenter rCenter, rCenter_mul_uSL, ← mul_assoc, rCenter_mul_uSL,
    mul_assoc (uSL _ _ _) rCenter rCenter, mul_inv_cancel_right]

theorem rAxis_sq_conj (b c : K) :
    rAxis ^ 2 * uSL 0 b c * (rAxis ^ 2)⁻¹ = uSL 0 (-b) (-c) := by
  rw [sq, mul_assoc rAxis rAxis, rAxis_mul_uSL, ← mul_assoc, rAxis_mul_uSL,
    mul_assoc (uSL _ _ _) rAxis rAxis, mul_inv_cancel_right]

variable [Finite K]

theorem rCenter_mem_normalizer {a₀ : K} (ha : a₀ ≠ 0) :
    rCenter ∈ Subgroup.normalizer ((lineSub a₀ 0 : Subgroup SL(3, K)) : Set SL(3, K)) := by
  have : Finite SL(3, K) := Finite.of_injective _ Subtype.val_injective
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨s, c, rfl⟩ := hx
  rw [mul_zero, rCenter_mul_uSL, mul_inv_cancel_right]
  exact ⟨c / a₀, -(s * a₀), by rw [div_mul_cancel₀ c ha, mul_zero]⟩

theorem rAxis_mem_normalizer {b₀ : K} (hb : b₀ ≠ 0) :
    rAxis ∈ Subgroup.normalizer ((lineSub 0 b₀ : Subgroup SL(3, K)) : Set SL(3, K)) := by
  have : Finite SL(3, K) := Finite.of_injective _ Subtype.val_injective
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨s, c, rfl⟩ := hx
  rw [mul_zero, rAxis_mul_uSL, mul_inv_cancel_right]
  exact ⟨-c / b₀, s * b₀, by rw [div_mul_cancel₀ (-c) hb, mul_zero]⟩

variable [CharP K 3]

omit [Finite K] in
theorem eq_zero_of_neg_eq {a : K} (h : -a = a) : a = 0 := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  linear_combination h + a * h3

theorem exists_pow_four_lineSub_center {a₀ : K} (ha : a₀ ≠ 0) :
    ∃ ρ ∈ autIn (⊤ : Subgroup SL(3, K)) (lineSub a₀ 0), ρ ^ 4 = 1 ∧ ρ ^ 2 ≠ 1 := by
  have hx : uSL a₀ 0 0 ∈ lineSub a₀ (0 : K) := ⟨1, 0, by simp⟩
  have h2 : rCenter ^ 2 * uSL a₀ 0 0 * (rCenter ^ 2)⁻¹ ≠ uSL a₀ (0 : K) 0 := by
    rw [rCenter_sq_conj]
    intro h
    exact ha (eq_zero_of_neg_eq (uSL_inj h).1)
  obtain ⟨hm, h4, h2'⟩ :=
    normalizerMonoidHom_pow_four (rCenter_mem_normalizer ha) rCenter_pow_four hx h2
  exact ⟨_, hm, h4, h2'⟩

theorem exists_pow_four_lineSub_axis {b₀ : K} (hb : b₀ ≠ 0) :
    ∃ ρ ∈ autIn (⊤ : Subgroup SL(3, K)) (lineSub 0 b₀), ρ ^ 4 = 1 ∧ ρ ^ 2 ≠ 1 := by
  have hx : uSL 0 b₀ 0 ∈ lineSub (0 : K) b₀ := ⟨1, 0, by simp⟩
  have h2 : rAxis ^ 2 * uSL 0 b₀ 0 * (rAxis ^ 2)⁻¹ ≠ uSL (0 : K) b₀ 0 := by
    rw [rAxis_sq_conj]
    intro h
    exact hb (eq_zero_of_neg_eq (uSL_inj h).2.1)
  obtain ⟨hm, h4, h2'⟩ :=
    normalizerMonoidHom_pow_four (rAxis_mem_normalizer hb) rAxis_pow_four hx h2
  exact ⟨_, hm, h4, h2'⟩

omit [Finite K] [CharP K 3] in
theorem uSL_one_conj (a b c : K) :
    uSL 1 0 0 * uSL a b c * (uSL (1 : K) 0 0)⁻¹ = uSL a b (c + b) := by
  rw [uSL_inv, uSL_mul, uSL_mul]
  congr 1 <;> ring

omit [CharP K 3] in
theorem uSL_one_mem_normalizer (a₀ b₀ : K) :
    uSL 1 0 0 ∈ Subgroup.normalizer ((lineSub a₀ b₀ : Subgroup SL(3, K)) : Set SL(3, K)) := by
  have : Finite SL(3, K) := Finite.of_injective _ Subtype.val_injective
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  obtain ⟨s, c, rfl⟩ := hx
  rw [uSL_one_conj]
  exact ⟨s, c + s * b₀, rfl⟩

omit [Finite K] in
theorem eq_zero_of_conj_mem_zpowers {a₀ b₀ : K} (ha : a₀ ≠ 0) (hb : b₀ ≠ 0) {s c : K}
    (h : uSL 1 0 0 * uSL (s * a₀) (s * b₀) c * (uSL (1 : K) 0 0)⁻¹ ∈
      Subgroup.zpowers (uSL (s * a₀) (s * b₀) c)) : s = 0 := by
  rw [uSL_one_conj] at h
  rcases eq_of_mem_zpowers_of_pow_three (uSL_pow_three _ _ _) h with h1 | h1 | h1
  · rw [← uSL_zero] at h1
    exact (mul_eq_zero.mp (uSL_inj h1).1).resolve_right ha
  · have h2 : s * b₀ = 0 := by linear_combination (uSL_inj h1).2.2
    exact (mul_eq_zero.mp h2).resolve_right hb
  · rw [sq, uSL_mul] at h1
    have h2 : s * a₀ = 0 := by linear_combination -(uSL_inj h1).1
    exact (mul_eq_zero.mp h2).resolve_right ha

omit [Finite K] in
theorem exists_eq_u3Mat_of_commute {p q r : K} (hp : p ≠ 0) (hq : q ≠ 0)
    {m : Matrix (Fin 3) (Fin 3) K} (hdet : m.det = 1)
    (hM : m * CFSG.SectionRank.OddCover.u3Mat p q r = CFSG.SectionRank.OddCover.u3Mat p q r * m) :
    ∃ a b c : K, m = CFSG.SectionRank.OddCover.u3Mat a b c ∧ a * q = p * b := by
  have h3 : (3 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 3
  have e : ∀ i j, (m * CFSG.SectionRank.OddCover.u3Mat p q r) i j =
      (CFSG.SectionRank.OddCover.u3Mat p q r * m) i j := fun i j => by rw [hM]
  have e00 : m 0 0 = m 0 0 + p * m 1 0 + r * m 2 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, CFSG.SectionRank.OddCover.u3Mat] using e 0 0
  have e01 : m 0 0 * p + m 0 1 = m 0 1 + p * m 1 1 + r * m 2 1 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, CFSG.SectionRank.OddCover.u3Mat] using e 0 1
  have e02 : m 0 0 * r + m 0 1 * q + m 0 2 = m 0 2 + p * m 1 2 + r * m 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, CFSG.SectionRank.OddCover.u3Mat] using e 0 2
  have e10 : m 1 0 = m 1 0 + q * m 2 0 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, CFSG.SectionRank.OddCover.u3Mat] using e 1 0
  have e12 : m 1 0 * r + m 1 1 * q + m 1 2 = m 1 2 + q * m 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, CFSG.SectionRank.OddCover.u3Mat] using e 1 2
  have e22 : m 2 0 * r + m 2 1 * q + m 2 2 = m 2 2 := by
    simpa [Matrix.mul_apply, Fin.sum_univ_three, CFSG.SectionRank.OddCover.u3Mat] using e 2 2
  have h20 : m 2 0 = 0 := by
    have : q * m 2 0 = 0 := by linear_combination -e10
    exact (mul_eq_zero.mp this).resolve_left hq
  have h21 : m 2 1 = 0 := by
    have : q * m 2 1 = 0 := by linear_combination e22 - r * h20
    exact (mul_eq_zero.mp this).resolve_left hq
  have h10 : m 1 0 = 0 := by
    have : p * m 1 0 = 0 := by linear_combination -e00 - r * h20
    exact (mul_eq_zero.mp this).resolve_left hp
  have h11 : m 0 0 = m 1 1 := by
    have : p * (m 0 0 - m 1 1) = 0 := by linear_combination e01 + r * h21
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hp)
  have h22 : m 1 1 = m 2 2 := by
    have : q * (m 1 1 - m 2 2) = 0 := by linear_combination e12 - r * h10
    exact sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left hq)
  have h00 : m 0 0 = 1 := by
    have hd := hdet
    rw [Matrix.det_fin_three, h20, h21, h10, ← h22, ← h11] at hd
    have h0 : (m 0 0 - 1) ^ 3 = 0 := by
      linear_combination hd - (m 0 0 ^ 2 - m 0 0) * h3
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
  refine ⟨m 0 1, m 1 2, m 0 2, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CFSG.SectionRank.OddCover.u3Mat, h00, h10, h20, h21, ← h11, ← h22]
  · linear_combination e02 - r * h11.trans h22

omit [Finite K] in
theorem exists_eq_uSL_of_commute {p q r : K} (hp : p ≠ 0) (hq : q ≠ 0) {g : SL(3, K)}
    (hg : g * uSL p q r = uSL p q r * g) :
    ∃ a b c : K, g = uSL a b c ∧ a * q = p * b := by
  obtain ⟨a, b, c, hm, hab⟩ := exists_eq_u3Mat_of_commute hp hq g.2 (congrArg Subtype.val hg)
  exact ⟨a, b, c, Subtype.ext (hm.trans (coe_uSL a b c).symm), hab⟩

omit [Finite K] in
theorem mem_lineSub_of_commute {a₀ b₀ t c₀ : K} (ha : a₀ ≠ 0) (hb : b₀ ≠ 0) (ht : t ≠ 0)
    {g : SL(3, K)} (hg : g * uSL (t * a₀) (t * b₀) c₀ = uSL (t * a₀) (t * b₀) c₀ * g) :
    g ∈ lineSub a₀ b₀ := by
  obtain ⟨a, b, c, rfl, hab⟩ :=
    exists_eq_uSL_of_commute (mul_ne_zero ht ha) (mul_ne_zero ht hb) hg
  refine ⟨a / a₀, c, ?_⟩
  have hb' : a / a₀ * b₀ = b := by
    field_simp
    have : t * (a * b₀ - a₀ * b) = 0 := by linear_combination hab
    linear_combination (sub_eq_zero.mp ((mul_eq_zero.mp this).resolve_left ht))
  rw [div_mul_cancel₀ a ha, hb']

end Field

theorem closure_pair_eq_of_card_nine {X : Type} [Group X] [Finite X] {D : Subgroup X}
    (hD9 : Nat.card D = 9) {c d : X} (hc : c ∈ D) (hd : d ∈ D) (hc1 : c ≠ 1) (hc3 : c ^ 3 = 1)
    (hdc : d ∉ Subgroup.zpowers c) : Subgroup.closure ({c, d} : Set X) = D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C := Subgroup.closure ({c, d} : Set X) with hC
  have hle : C ≤ D := by
    rw [hC, Subgroup.closure_le]
    rintro y (rfl | rfl)
    exacts [hc, hd]
  have hcC : Subgroup.zpowers c ≤ C :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c _))
  have hdC : d ∈ C := Subgroup.subset_closure (Set.mem_insert_of_mem c (Set.mem_singleton d))
  have hc3' : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hc3 hc1]
  have hdvd : Nat.card C ∣ 9 := hD9 ▸ Subgroup.card_dvd_of_le hle
  have h3 : 3 ∣ Nat.card C := hc3' ▸ Subgroup.card_dvd_of_le hcC
  have hne : Nat.card C ≠ 3 := by
    intro h
    have heq := Subgroup.eq_of_le_of_card_ge hcC (by rw [h, hc3'])
    apply hdc
    rw [heq]
    exact hdC
  have h9 : Nat.card C = 9 := by
    have hle9 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases hn : Nat.card C <;> omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [h9, hD9])

theorem census424_of_l33 {X : Type} [Group X] [Finite X]
    (e : X ≃* projSL 3 (GaloisField 3 1)) : Census424 X := by
  have hK3 : Nat.card (GaloisField 3 1) = 3 := by
    rw [GaloisField.card 3 1 one_ne_zero, pow_one]
  intro D c d J h
  exfalso
  set θ : X ≃* SL(3, GaloisField 3 1) := e.trans (slEquivProjSL (GaloisField 3 1)).symm
  obtain ⟨g, a₀, b₀, hab, hle⟩ := exists_map_le_lineSub one_ne_zero θ h.maximal.prop
  set e' := θ.trans (MulAut.conj g⁻¹) with he'
  have hDF : D.map e'.toMonoidHom = lineSub a₀ b₀ := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [card_lineSub hab, hK3, Subgroup.card_map_of_injective e'.injective, h.card_eq]
    norm_num
  by_cases hb : b₀ = 0
  · subst hb
    have ha : a₀ ≠ 0 := hab.resolve_right (fun h0 => h0 rfl)
    exact false_of_pow_four h (exists_pow_four_of_map_eq e' hDF (exists_pow_four_lineSub_center ha))
  by_cases ha : a₀ = 0
  · subst ha
    exact false_of_pow_four h (exists_pow_four_of_map_eq e' hDF (exists_pow_four_lineSub_axis hb))
  have hmem : ∀ x ∈ D, e' x ∈ lineSub a₀ b₀ := fun x hx => hDF ▸ ⟨x, hx, rfl⟩
  obtain ⟨s, c₁, hds⟩ := hmem d h.d_mem
  obtain ⟨t, c₂, hct⟩ := hmem c h.c_mem
  have hyN : e'.symm (uSL 1 0 0) ∈ Subgroup.normalizer (D : Set X) := by
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    have h1 : uSL 1 0 0 * e' x * (uSL 1 0 0)⁻¹ ∈ lineSub a₀ b₀ :=
      (Subgroup.mem_normalizer_iff.mp (uSL_one_mem_normalizer a₀ b₀) (e' x)).mp (hmem x hx)
    rw [← hDF] at h1
    obtain ⟨x', hx', hxx'⟩ := h1
    have : e'.symm (uSL 1 0 0) * x * (e'.symm (uSL 1 0 0))⁻¹ = x' := by
      apply e'.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
      exact hxx'.symm
    rw [this]
    exact hx'
  have hyd : e'.symm (uSL 1 0 0) * d * (e'.symm (uSL 1 0 0))⁻¹ ∈ Subgroup.zpowers d :=
    (Subgroup.mem_normalizer_iff.mp (h.normalizer_le hyN) d).mp (Subgroup.mem_zpowers d)
  have hyd' : uSL 1 0 0 * e' d * (uSL (1 : GaloisField 3 1) 0 0)⁻¹ ∈
      Subgroup.zpowers (e' d) := by
    have h1 := Subgroup.mem_map_of_mem e'.toMonoidHom hyd
    rw [MonoidHom.map_zpowers] at h1
    simpa using h1
  rw [hds] at hyd'
  have hs : s = 0 := eq_zero_of_conj_mem_zpowers ha hb hyd'
  have ht : t ≠ 0 := by
    rintro rfl
    have hcl := closure_pair_eq_of_card_nine h.card_eq h.c_mem h.d_mem h.c_ne_one
      (h.maximal.prop.2 c h.c_mem) h.d_not_mem
    have hZ : D ≤ (lineSub (0 : GaloisField 3 1) 0).comap e'.toMonoidHom := by
      rw [← hcl, Subgroup.closure_le]
      rintro y (rfl | rfl)
      · exact ⟨0, c₂, by simp [hct]⟩
      · exact ⟨0, c₁, by simp [hds, hs]⟩
    have hx : uSL a₀ b₀ 0 ∈ D.map e'.toMonoidHom := by
      rw [hDF]
      exact ⟨1, 0, by rw [one_mul, one_mul]⟩
    obtain ⟨x, hxD, hxe⟩ := hx
    obtain ⟨s', c', hsc⟩ := hZ hxD
    rw [hxe] at hsc
    exact ha (by simpa using (uSL_inj hsc).1)
  apply not_isSolvable_centralizer h
  have hcen : ∀ x : Subgroup.centralizer ({c} : Set X), e' x ∈ lineSub a₀ b₀ := by
    intro x
    refine mem_lineSub_of_commute ha hb ht (c₀ := c₂) ?_
    have hx : (x : X) * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp x.2
    rw [← hct, ← map_mul, hx, map_mul]
  exact Group.isSolvable_of_comm fun x y => Subtype.ext (e'.injective (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact lineSub_commute (hcen x) (hcen y)))

end Item424Res2

end CFSG.RankThree.PartTwo.Sec4
