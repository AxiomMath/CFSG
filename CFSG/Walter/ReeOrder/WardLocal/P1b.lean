module

public import CFSG.Walter.ReeOrder.WardLocal.P1

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.Walter.JT CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers
open CFSG.DirectProduct

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m) {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
  (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))

namespace Block

include B hq hK hG in
theorem hcT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) ∣ 2 * q ^ 2 :=
  (B.T_data hq hG hK).2.2

include B hq hK hG in
theorem card_CT : Nat.card (Subgroup.centralizer ({TT S} : Set G)) = 2 * q ^ 2 :=
  (CT_eq_CF hq hK (B.hcT hq hK hG) hG).2

include B hq hK hG in
theorem orderOf_PP1 {x : G} (hx : x ∈ PP1 S) (hx1 : x ≠ 1) : orderOf x = 3 :=
  orderOf_eq_prime (PP1_pow_three hq hK (B.hcT hq hK hG) hG hx) hx1

include B hq hK hG in
theorem xi2_of_isConj {x : G} (h : IsConj x (TT S) ∨ IsConj x (TT S)⁻¹) : B.ξ₂ x = 1 := by
  have hcl := blocksVChar_isClassFunction (AddSubgroup.subset_closure B.irr_2)
  have hT : B.ξ₂ (TT S) = 1 := (B.T_data hq hG hK).2.1
  have hcl' : ∀ {a b : G}, IsConj a b → B.ξ₂ a = B.ξ₂ b := by
    intro a b hab
    obtain ⟨c, hc⟩ := isConj_iff.mp hab
    rw [← hc, hcl]
  rcases h with h | h
  · rw [hcl' h, hT]
  · rw [hcl' h, inv_eq_conj B.irr_2, hT, map_one]

include B hq hK hG in
theorem xi4_of_no_involution {x : G} (hx : x ∈ PP1 S) (hx1 : x ≠ 1)
    (hinv : ∀ t : G, orderOf t = 2 → x * t ≠ t * x) :
    (Nat.card (Subgroup.centralizer ({x} : Set G)) = q ^ 2 ∧ B.ξ₄ x = 0) ∨
      (q ^ 2 < Nat.card (Subgroup.centralizer ({x} : Set G)) ∧ B.ξ₄ x = q) := by
  have hcT := B.hcT hq hK hG
  have hx3 := B.orderOf_PP1 hq hK hG hx hx1
  have hxodd : Odd (orderOf x) := by rw [hx3]; decide
  have hx33 : 3 ∣ orderOf x := by rw [hx3]
  set c := Nat.card (Subgroup.centralizer ({x} : Set G)) with hc
  have hcdvd : c ∣ 2 * q ^ 3 := B.card_centralizer_dvd hq hG hxodd hx33
  have hcodd : ¬ 2 ∣ c := by
    intro h2
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.centralizer ({x} : Set G))
      2 h2
    apply hinv t (by rw [Subgroup.orderOf_coe]; exact ht)
    exact (Subgroup.mem_centralizer_singleton_iff.mp t.2).symm
  have hc3 : c ∣ 3 ^ (3 * (2 * k + 1)) := by
    have h1 : c ∣ 2 * 3 ^ (3 * (2 * k + 1)) := by
      rw [hq, ← pow_mul, mul_comm (2 * k + 1) 3] at hcdvd; exact hcdvd
    exact (Nat.Coprime.dvd_of_dvd_mul_left
      ((Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hcodd))) h1)
  obtain ⟨j, hj, hcj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hc3
  have hP1C : PP1 S ≤ Subgroup.centralizer ({x} : Set G) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact PP1_comm hq hK hcT hG hy hx
  have hq2 : q ^ 2 ∣ c := by
    rw [← card_PP1 hq hK hcT hG]; exact Subgroup.card_dvd_of_le hP1C
  have hj2 : 2 * (2 * k + 1) ≤ j := by
    rw [hcj, hq, ← pow_mul, mul_comm] at hq2
    exact (Nat.pow_dvd_pow_iff_le_right (show 1 < 3 by norm_num)).mp hq2
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have hT3 : orderOf (TT S) = 3 := orderOf_TT
  have hTodd : Odd (orderOf (TT S)) := by rw [hT3]; decide
  have hT33 : 3 ∣ orderOf (TT S) := by rw [hT3]
  have hcm := class_mult x (TT S) (S.κ r)
  have hT4 : B.ξ₄ (TT S) = 0 := (B.T_data hq hG hK).1
  have hT2 : B.ξ₂ (TT S) = 1 := (B.T_data hq hG hK).2.1
  rw [B.sum_R hq hG hxodd hx33 hTodd hT33 hr hr1, B.card_CT hq hK hG, ← hc, hcj, hT4,
    hT2] at hcm
  have h24 := (B.eta_eq_one hq hG hxodd hx33 S.i₀).2.2
  set s := B.ξ₄ x with hs
  have hxi2 : B.ξ₂ x = 1 - s := by linear_combination h24
  rw [hxi2, hG] at hcm
  set N := (((cls x ×ˢ cls (TT S)).filter fun p => p.1 * p.2 = S.κ r).card : ℕ) with hN
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hqm1 : (q : ℂ) - 1 ≠ 0 := by
    have : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
    have : ((q : ℤ) - 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hqp1 : (q : ℂ) + 1 ≠ 0 := by
    have : ((q : ℤ) + 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hw0 : (q : ℂ) ^ 2 - q + 1 ≠ 0 := by
    have : ((q : ℤ) ^ 2 - q + 1 : ℤ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hkey : 2 * (3 : ℂ) ^ j * N = q * (q - 1) * (q ^ 3 + q - (q + 1) * s) := by
    push_cast [Nat.cast_sub hq1] at hcm
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (q : ℂ) ^ 2 - q + 1 := ⟨_, rfl⟩
    rw [← hw] at hcm hw0
    rw [show (q : ℂ) ^ 3 + 1 = ((q : ℂ) + 1) * w by rw [hw]; ring] at hcm
    have h2 : (N : ℂ) * (3 : ℂ) ^ j * (2 * (q : ℂ) ^ 2) * (2 * ((q : ℂ) + 1) * w) =
        (q : ℂ) ^ 3 * (((q : ℂ) + 1) * w) * ((q : ℂ) - 1) * (2 * ((q : ℂ) + 1) * w) *
          (1 + (1 - s) * 1 / w + s * 0 / ((q : ℂ) * w) - 2 / (((q : ℂ) + 1) * w)) := by
      rw [hcm]; ring
    field_simp at h2
    rw [hw] at h2
    linear_combination h2
  obtain ⟨z, hz⟩ := exists_int_of_isIntegral (isIntegral_irr B.irr_4 x)
    (r := (((q : ℚ) ^ 3 + q) - 2 * 3 ^ j * N / (q * (q - 1))) / (q + 1)) (by
      push_cast
      rw [← hs]
      field_simp
      linear_combination hkey)
  rw [← hs] at hz
  have hkeyZ : 2 * (3 : ℤ) ^ j * N = q * (q - 1) * (q ^ 3 + q - (q + 1) * z) := by
    have : ((2 * (3 : ℤ) ^ j * N : ℤ) : ℂ) =
        ((q * (q - 1) * (q ^ 3 + q - (q + 1) * z) : ℤ) : ℂ) := by
      push_cast; rw [← hz]; exact hkey
    exact_mod_cast this
  have hlow : 1 + (1 - z) ^ 2 + z ^ 2 ≤ (3 : ℤ) ^ j := by
    have hX : ({1, B.ξ₂, B.ξ₄} : Finset (G → ℂ)) ⊆ (irreducibles_finite G).toFinset := by
      intro χ hχ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
      rw [Set.Finite.mem_toFinset]
      rcases hχ with rfl | rfl | rfl
      · exact one_mem_blocksIrr G
      · exact B.irr_2
      · exact B.irr_4
    have h := sum_normSq_le x hX
    rw [Finset.sum_insert (by simp [B.n12, B.n14]), Finset.sum_pair B.n24, hxi2, ← hs, hz,
      ← hc, hcj] at h
    simp only [Pi.one_apply, map_one] at h
    have e1 : Complex.normSq (1 - (z : ℂ)) = ((1 - z : ℤ) : ℝ) ^ 2 := by
      rw [show (1 - (z : ℂ)) = ((1 - z : ℤ) : ℂ) by push_cast; ring, Complex.normSq_intCast]
      ring
    rw [e1, Complex.normSq_intCast] at h
    have h' : ((1 + (1 - z) ^ 2 + z ^ 2 : ℤ) : ℝ) ≤ ((3 ^ j : ℤ) : ℝ) := by
      push_cast at h ⊢; nlinarith
    exact_mod_cast h'
  rcases cx_arith (q := (q : ℤ)) (n := 2 * k + 1) (by rw [hq]; push_cast; ring) (by omega) hj2
    hj hkeyZ hlow with ⟨hj', hz0⟩ | ⟨hj', hzq⟩
  · left
    refine ⟨by rw [hcj, hj', hq, ← pow_mul, mul_comm], ?_⟩
    rw [hz, hz0]; simp
  · right
    refine ⟨?_, by rw [hz, hzq]; push_cast; ring⟩
    rw [hcj, hq, ← pow_mul, mul_comm]
    exact Nat.pow_lt_pow_right (by norm_num) hj'

end Block

@[expose] noncomputable def AA (S : WardSetup G PSL(2, K) q (-1)) : Finset G :=
  Finset.univ.filter fun x => x ∈ PP1 S ∧ x ≠ 1 ∧ (∀ t : G, orderOf t = 2 → x * t ≠ t * x) ∧
    q ^ 2 < Nat.card (Subgroup.centralizer ({x} : Set G))

omit [CharP K 3] in
theorem mem_AA {x : G} : x ∈ AA S ↔ x ∈ PP1 S ∧ x ≠ 1 ∧
    (∀ t : G, orderOf t = 2 → x * t ≠ t * x) ∧
      q ^ 2 < Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  simp [AA]

namespace Block

include B hq hK hG in
theorem xi2_PP1 {x : G} (hx : x ∈ PP1 S) (hx1 : x ≠ 1) :
    B.ξ₂ x = if x ∈ AA S then 1 - (q : ℂ) else 1 := by
  have h24 := (B.eta_eq_one hq hG (by rw [B.orderOf_PP1 hq hK hG hx hx1]; decide)
    (by rw [B.orderOf_PP1 hq hK hG hx hx1]) S.i₀).2.2
  by_cases hinv : ∃ t : G, orderOf t = 2 ∧ x * t = t * x
  · obtain ⟨t, ht, hxt⟩ := hinv
    have hnA : x ∉ AA S := fun h => (mem_AA.mp h).2.2.1 t ht hxt
    simp only [hnA, ↓reduceIte]
    have hxp : IsPGroup 3 (Subgroup.zpowers x) :=
      (isPGroup_PP1 (S := S)).to_le (Subgroup.zpowers_le.mpr hx)
    exact B.xi2_of_isConj hq hK hG (isConj_T_of_commute hq hK hx1 hxp ht hxt)
  · push Not at hinv
    rcases B.xi4_of_no_involution hq hK hG hx hx1 hinv with ⟨hc, h4⟩ | ⟨hc, h4⟩
    · have hnA : x ∉ AA S := fun h => by
        have := (mem_AA.mp h).2.2.2; omega
      simp only [hnA, ↓reduceIte]; linear_combination h24 - h4
    · have hA : x ∈ AA S := mem_AA.mpr ⟨hx, hx1, hinv, hc⟩
      simp only [hA, ↓reduceIte]; linear_combination h24 - h4

include B hq hK hG in
theorem count_AA : ∃ n₀ : ℕ, q * n₀ + (AA S).card = 2 * q - 1 := by
  have hcT := B.hcT hq hK hG
  obtain ⟨n₀, hn₀⟩ := exists_natCast_restrict (PP1 S).subtype B.irr_2
    (one_mem_blocksIrr (PP1 S))
  refine ⟨n₀, ?_⟩
  unfold CFSG.BlocksInnerProduct at hn₀
  rw [card_PP1 hq hK hcT hG] at hn₀
  have hsum : ∑ u : PP1 S, (B.ξ₂ ∘ (PP1 S).subtype) u * starRingEnd ℂ ((1 : PP1 S → ℂ) u) =
      ∑ x ∈ (Finset.univ.filter fun x : G => x ∈ PP1 S),
        (if x = 1 then (q : ℂ) ^ 2 - q + 1 else if x ∈ AA S then 1 - (q : ℂ) else 1) := by
    set g : G → ℂ := fun x =>
      if x = 1 then (q : ℂ) ^ 2 - q + 1 else if x ∈ AA S then 1 - (q : ℂ) else 1 with hg
    have hval : ∀ u : PP1 S, (B.ξ₂ ∘ (PP1 S).subtype) u * starRingEnd ℂ ((1 : PP1 S → ℂ) u) =
        g u := by
      intro u
      simp only [Function.comp_apply, Subgroup.coe_subtype, Pi.one_apply, map_one, mul_one, hg]
      by_cases h1 : (u : G) = 1
      · simp only [h1, ↓reduceIte]; exact B.xi_one.1
      · simp only [h1, ↓reduceIte]; exact B.xi2_PP1 hq hK hG u.2 h1
    rw [Finset.sum_congr rfl (fun u _ => hval u)]
    exact (Finset.sum_subtype _ (by simp) g).symm
  set s₁ := (Finset.univ.filter fun x : G => x ∈ PP1 S) with hs₁
  have hs₁card : s₁.card = q ^ 2 := by
    rw [← card_PP1 hq hK hcT hG, Nat.card_eq_fintype_card, ← Fintype.card_coe]
    simp [hs₁, Fintype.card_subtype]
  have h1s : (1 : G) ∈ s₁ := by simp [hs₁]
  have hAs : AA S ⊆ s₁ := fun x hx => by simp [hs₁, (mem_AA.mp hx).1]
  have hA1 : (1 : G) ∉ AA S := fun h => (mem_AA.mp h).2.1 rfl
  have hgx : ∀ x ∈ s₁, (if x = 1 then (q : ℂ) ^ 2 - q + 1 else if x ∈ AA S then 1 - (q : ℂ)
      else 1) =
        1 + (if x = 1 then (q : ℂ) ^ 2 - q else 0) + (if x ∈ AA S then -(q : ℂ) else 0) := by
    intro x _
    by_cases h1 : x = 1
    · subst h1; simp [hA1]; ring
    · by_cases hA : x ∈ AA S <;> simp [h1, hA]; ring
  rw [Finset.sum_congr rfl hgx, Finset.sum_add_distrib, Finset.sum_add_distrib,
    Finset.sum_ite_eq' s₁ 1] at hsum
  simp only [h1s, ↓reduceIte] at hsum
  rw [Finset.sum_const, hs₁card] at hsum
  rw [show (∑ x ∈ s₁, if x ∈ AA S then -(q : ℂ) else 0) = ∑ x ∈ AA S, -(q : ℂ) by
    rw [← Finset.sum_filter]; congr 1; ext x; simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hAs h, h⟩⟩] at hsum
  rw [hsum, Finset.sum_const] at hn₀
  simp only [nsmul_eq_mul, mul_one, smul_neg] at hn₀
  have hq0 : (q : ℂ) ≠ 0 := by
    have : 0 < q := by rw [hq]; positivity
    exact_mod_cast this.ne'
  have hfin : ((q * n₀ + (AA S).card : ℕ) : ℂ) = ((2 * q - 1 : ℕ) : ℂ) := by
    have hq1 : 1 ≤ 2 * q := by
      have : 0 < q := by rw [hq]; positivity
      omega
    push_cast [Nat.cast_sub hq1]
    field_simp at hn₀
    push_cast at hn₀
    apply mul_left_cancel₀ hq0
    linear_combination -hn₀
  exact_mod_cast hfin

end Block

end CFSG.Walter.WardLocal
