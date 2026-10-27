module

public import CFSG.Walter.ReeOrder.WardLocal.ClassMult
public import CFSG.Walter.ReeOrder.WardLocal.PSL
public import CFSG.Walter.ReeOrder.WardLocal.ArithThree

public section

open scoped BigOperators Classical MatrixGroups

namespace CFSG.Walter.WardLocal

open CFSG.Walter.Ward CFSG.SmallDefect CFSG.BlockSectionOrthogonality.Helpers CFSG.DirectProduct
open CFSG.Walter.JT

variable {G : Type} [Group G] [Fintype G] {K : Type} [Field K] [Fintype K] [DecidableEq K]
  [CharP K 3] {q : ℕ} {S : WardSetup G PSL(2, K) q (-1)} {D : S.EtaData} {m : ℕ}
  (B : Block S D m)

namespace Block

omit [Fintype K] [DecidableEq K] in
theorem orderOf_pslU {b : K} (hb : b ≠ 0) : orderOf (pslU b) = 3 :=
  orderOf_eq_prime (pslU_pow_three b) (pslU_ne_one hb)

omit [CharP K 3] in
theorem theta_unip {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) {y : PSL(2, K)} (hy : orderOf y = 3) :
    S.W.θ2 y + S.W.θ3 y = -1 ∧ S.W.θ4 y = 0 ∧ (∀ θ ∈ S.W.RFam, θ y = 1) ∧
      ∀ θ ∈ S.W.SFam, θ y = -1 := by
  have h3q : 3 ∣ q := hq ▸ dvd_pow_self 3 (by omega)
  have hoc : ∀ g : PSL(2, K), orderOf (g⁻¹ * y * g) = 3 := fun g => by
    rw [show g⁻¹ * y * g = g⁻¹ * y * g⁻¹⁻¹ by group, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hy]
  rcases S.W.odd_classes y (by rw [hy]; decide) with h | ⟨g, hg, -⟩ | ⟨g, hg, -⟩ | h
  · rw [h, orderOf_one] at hy; omega
  · exfalso
    have hdvd : orderOf (g⁻¹ * y * g) ∣ Nat.card S.W.Ro := by
      rw [← Subgroup.orderOf_mk _ hg]; exact orderOf_dvd_natCard _
    rw [hoc] at hdvd
    have := S.W.Ro_card
    omega
  · exfalso
    have hdvd : orderOf (g⁻¹ * y * g) ∣ Nat.card S.W.So := by
      rw [← Subgroup.orderOf_mk _ hg]; exact orderOf_dvd_natCard _
    rw [hoc] at hdvd
    have := S.W.So_card
    omega
  · obtain ⟨h1, h2, h3, h4⟩ := h
    refine ⟨by rw [h1]; push_cast; ring, h2, fun θ hθ => by rw [h3 θ hθ]; push_cast; ring,
      fun θ hθ => by rw [h4 θ hθ]; push_cast; ring⟩

omit [CharP K 3] in
theorem isIntegral_half_sub {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (y : PSL(2, K)) :
    IsIntegral ℤ ((χ (S.κ y) - χ (S.J * S.κ y)) / 2) := by
  have h1 := S.τ_expand hχ y
  have h2 := S.σ_expand hχ y
  simp only [WardSetup.τ, WardSetup.σ] at h1 h2
  have : (χ (S.κ y) - χ (S.J * S.κ y)) / 2 =
      ∑ θ ∈ (irreducibles_finite PSL(2, K)).toFinset, (S.mb χ θ : ℂ) * θ y := by
    rw [h1, h2, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun θ _ => ?_
    have := S.two_mb χ θ
    have h' : ((2 * (S.mb χ θ : ℤ) : ℤ) : ℂ) = ((S.Ar χ θ - S.M χ θ : ℤ) : ℂ) := by rw [this]
    push_cast at h'
    linear_combination (-(θ y) / 2) * h'
  rw [this]
  refine IsIntegral.sum _ fun θ hθ => ?_
  rw [Set.Finite.mem_toFinset] at hθ
  have := (isIntegral_algebraMap (R := ℤ) (A := ℂ) (x := (S.mb χ θ : ℤ))).mul
    (isIntegral_irr hθ y)
  simpa using this

omit [CharP K 3] in
theorem xi_J_unip {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) {y : PSL(2, K)} (hy : orderOf y = 3) :
    B.ξ₂ (S.J * S.κ y) = -1 ∧ B.ξ₃ (S.J * S.κ y) = 0 ∧ B.ξ₄ (S.J * S.κ y) = 0 := by
  obtain ⟨hθ, -, -, -⟩ := theta_unip (S := S) hq hy
  have hodd : Odd (orderOf y) := by rw [hy]; decide
  have h2S1 : B.ξ₂ ∈ S.S1 := by rw [B.hS1]; simp
  have h3S1 : B.ξ₃ ∈ S.S1 := by rw [B.hS1]; simp
  have h4S1 : B.ξ₄ ∈ S.S1 := by rw [B.hS1]; simp
  have h3S2 : B.ξ₃ ∈ S.S2 := by rw [B.hS2]; simp
  have h4S2 : B.ξ₄ ∈ S.S2 := by rw [B.hS2]; simp
  have hval : ∀ {χ : G → ℂ}, χ ∈ BlocksIrr G → χ ∈ S.S1 →
      χ (S.J * S.κ y) = S.d1 χ + S.d2 χ * S.W.θ2 y + S.d3 χ * S.W.θ3 y := by
    intro χ hχ h1
    obtain ⟨hR, hS⟩ := S.P_rows hχ (Or.inl h1)
    have hd := S.σ_decomp hχ hodd
    rw [Finset.sum_eq_zero (fun θ hθ => by rw [hR θ hθ]; simp),
      Finset.sum_eq_zero (fun θ hθ => by rw [hS θ hθ]; simp)] at hd
    simp only [WardSetup.σ] at hd
    rw [hd]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hval B.irr_2 h2S1, B.d1_2, S.van2 B.irr_2 B.ξ₂_S2, S.van3 B.irr_2 B.ξ₂_S3]
    simp
  · rw [hval B.irr_3 h3S1, (S.agree12 h3S1 h3S2).symm, (S.agree13 h3S1 B.ξ₃_S3).symm, B.d1_3]
    push_cast
    linear_combination hθ
  · rw [hval B.irr_4 h4S1, (S.agree12 h4S1 h4S2).symm, (S.agree13 h4S1 B.ξ₄_S3).symm, B.d1_4]
    push_cast
    linear_combination -hθ

theorem q_half {k q : ℕ} (hq : q = 3 ^ (2 * k + 1)) : ∃ k' : ℕ, q = 2 * k' + 1 ∧ Odd k' := by
  have h4 : q % 4 = 3 := by
    rw [hq, pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  exact ⟨q / 2, by omega, ⟨q / 4, by omega⟩⟩

omit [CharP K 3] in
theorem real_unip_const {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
    {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (hreal : starRingEnd ℂ ∘ χ = χ) {b : K} (hb : b ≠ 0) :
    χ (S.κ (pslU b)) = χ (S.κ (pslU 1)) := by
  obtain ⟨k', hk', hodd⟩ := q_half hq
  obtain ⟨j, hj | hj⟩ := conj_pslU (hK.trans hk') hodd hb
  · rw [← hj, map_mul, map_mul, map_inv]
    exact blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ) _ _
  · rw [← hj, map_mul, map_mul, map_inv,
      blocksVChar_isClassFunction (AddSubgroup.subset_closure hχ), ← pslU_inv, map_inv,
      inv_eq_conj hχ]
    have := congrFun hreal (S.κ (pslU 1))
    simpa using this

omit [CharP K 3] in
theorem real_unip_mul_q {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hK : Fintype.card K = q)
    {χ : G → ℂ} (hχ : χ ∈ BlocksIrr G) (hreal : starRingEnd ℂ ∘ χ = χ) {d : ℤ}
    (hd : χ 1 = (q : ℂ) * d) : ∃ a : ℤ, χ (S.κ (pslU 1)) = a * q := by
  set t := χ (S.κ (pslU 1)) with ht
  let φ : pslE K →* G := S.κ.comp (pslE K).subtype
  obtain ⟨n, hn⟩ := exists_natCast_restrict φ hχ (one_mem_blocksIrr (pslE K))
  have hcardU : Nat.card (pslE K) = q := by rw [card_pslE, Nat.card_eq_fintype_card, hK]
  have hsum : ∑ u : pslE K, (χ ∘ φ) u * starRingEnd ℂ ((1 : pslE K → ℂ) u) =
      (q : ℂ) * d + ((q : ℂ) - 1) * t := by
    have hval : ∀ u : pslE K, (χ ∘ φ) u * starRingEnd ℂ ((1 : pslE K → ℂ) u) =
        if u = 1 then (q : ℂ) * d else t := by
      intro u
      simp only [Pi.one_apply, map_one, mul_one, Function.comp_apply]
      split_ifs with hu
      · rw [hu, map_one, hd]
      · obtain ⟨_, ⟨b, rfl⟩⟩ := u
        have hb : b ≠ 0 := by
          rintro rfl
          exact hu (Subtype.ext (pslU_zero))
        exact real_unip_const hq hK hχ hreal hb
    rw [Finset.sum_congr rfl fun u _ => hval u, Finset.sum_ite, Finset.sum_const,
      Finset.sum_const, Finset.filter_eq']
    simp only [Finset.mem_univ, ↓reduceIte, Finset.card_singleton, one_smul, nsmul_eq_mul]
    congr 1
    have hfe : (Finset.univ.filter fun u : pslE K => ¬ u = 1) = Finset.univ.erase 1 := by
      ext u; simp
    have : (Finset.univ.filter fun u : pslE K => ¬ u = 1).card = q - 1 := by
      rw [hfe, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
        ← Nat.card_eq_fintype_card, hcardU]
    rw [this]
    have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
    push_cast [Nat.cast_sub hq1]
    ring
  unfold BlocksInnerProduct at hn
  rw [hsum, hcardU] at hn
  have hq0 : (q : ℂ) ≠ 0 := by
    have : 0 < q := by rw [hq]; positivity
    exact_mod_cast this.ne'
  have hq1 : (q : ℂ) - 1 ≠ 0 := by
    have : 3 ≤ q := by rw [hq]; exact Nat.le_self_pow (by omega) 3
    have : ((q : ℤ) - 1 : ℤ) ≠ 0 := by omega
    exact_mod_cast this
  have hteq : t = (((q * n - q * d : ℤ) : ℚ) / ((q - 1 : ℤ) : ℚ) : ℚ) := by
    push_cast
    field_simp at hn ⊢
    linear_combination hn
  obtain ⟨z, hz⟩ := exists_int_of_isIntegral (isIntegral_irr hχ _) hteq
  have hzq : (q : ℤ) ∣ ((q : ℤ) - 1) * z := by
    refine ⟨n - d, ?_⟩
    have : (((q : ℤ) - 1) * z : ℂ) = ((q * (n - d) : ℤ) : ℂ) := by
      push_cast
      rw [← hz]
      field_simp at hn
      linear_combination hn
    exact_mod_cast this
  have hcop : IsCoprime (q : ℤ) ((q : ℤ) - 1) := ⟨1, -1, by ring⟩
  obtain ⟨a, ha⟩ := hcop.dvd_of_dvd_mul_left hzq
  refine ⟨a, ?_⟩
  show χ (S.κ (pslU 1)) = _
  rw [hz, ha]; push_cast; ring

theorem card_shape {n c : ℕ} (hc : c ∣ 2 * (3 ^ n) ^ 3) (h2 : 2 ∣ c) :
    ∃ j ≤ 3 * n, c = 2 * 3 ^ j := by
  obtain ⟨c', rfl⟩ := h2
  have : c' ∣ 3 ^ (3 * n) := by
    have h1 : c' ∣ (3 ^ n) ^ 3 := (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)).mp hc
    rwa [← pow_mul, mul_comm] at h1
  obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp this
  exact ⟨j, hj, rfl⟩

variable {k : ℕ} (hq : q = 3 ^ (2 * k + 1)) (hG : Nat.card G = q ^ 3 * (q ^ 3 + 1) * (q - 1))
  (hK : Fintype.card K = q)
include hq hG hK

theorem T_data : B.ξ₄ (S.κ (pslU 1)) = 0 ∧ B.ξ₂ (S.κ (pslU 1)) = 1 ∧
    Nat.card (Subgroup.centralizer ({S.κ (pslU 1)} : Set G)) ∣ 2 * q ^ 2 := by
  set T := S.κ (pslU (1 : K)) with hT
  have hT3 : orderOf T = 3 := by rw [hT, S.orderOf_κ, orderOf_pslU one_ne_zero]
  have hTodd : Odd (orderOf T) := by rw [hT3]; decide
  have hT33 : 3 ∣ orderOf T := by rw [hT3]
  obtain ⟨a, ha⟩ := real_unip_mul_q (S := S) hq hK B.irr_4 B.real_4
    (d := (q : ℤ) ^ 2 - q + 1) (by rw [B.xi_one.2.2]; push_cast; ring)
  have hJT := (B.xi_J_unip hq (orderOf_pslU (one_ne_zero (α := K)))).2.2
  have hpar : Even a := by
    have hint := isIntegral_half_sub B.irr_4 (S := S) (pslU (1 : K))
    rw [hJT, ← hT, ha] at hint
    obtain ⟨w, hw⟩ := exists_int_of_isIntegral hint (r := (a * q : ℚ) / 2) (by push_cast; ring)
    have hw' : a * q = 2 * w := by
      have : ((a * q : ℤ) : ℂ) = ((2 * w : ℤ) : ℂ) := by
        push_cast; linear_combination 2 * hw
      exact_mod_cast this
    have hqodd : Odd (q : ℤ) := by
      rw [hq]; push_cast; exact Odd.pow (by decide)
    rcases Int.even_or_odd a with h | h
    · exact h
    · exfalso
      have : Odd (a * q) := h.mul hqodd
      rw [hw'] at this
      exact (Int.not_even_iff_odd.mpr this) (even_two_mul w)
  have h24 := (B.eta_eq_one hq hG hTodd hT33 S.i₀).2.2
  have hξ2 : B.ξ₂ T = 1 - a * q := by rw [← ha]; linear_combination h24
  have hcdvd := B.card_centralizer_dvd hq hG hTodd hT33
  set c := Nat.card (Subgroup.centralizer ({T} : Set G)) with hc
  have hJmem : S.J ∈ Subgroup.centralizer ({T} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (S.κ_comm (pslU 1)).symm
  have h2c : 2 ∣ c := by
    have := Subgroup.orderOf_dvd_natCard _ hJmem
    rwa [S.orderOf_J] at this
  obtain ⟨j, hj, hcj⟩ := card_shape (n := 2 * k + 1) (hq ▸ hcdvd) h2c
  have hlow : 1 + (1 - a * q) ^ 2 + (a * q) ^ 2 ≤ (2 * 3 ^ j : ℤ) := by
    have hX : ({1, B.ξ₂, B.ξ₄} : Finset (G → ℂ)) ⊆ (irreducibles_finite G).toFinset := by
      intro χ hχ
      simp only [Finset.mem_insert, Finset.mem_singleton] at hχ
      rw [Set.Finite.mem_toFinset]
      rcases hχ with rfl | rfl | rfl
      · exact one_mem_blocksIrr G
      · exact B.irr_2
      · exact B.irr_4
    have h := sum_normSq_le T hX
    rw [Finset.sum_insert (by simp [B.n12, B.n14]), Finset.sum_pair B.n24, hξ2, ha] at h
    rw [← hc, hcj] at h
    simp only [Pi.one_apply, map_one] at h
    have e1 : Complex.normSq (1 - (a : ℂ) * q) = ((1 - a * q : ℤ) : ℝ) ^ 2 := by
      rw [show (1 - (a : ℂ) * q) = ((1 - a * q : ℤ) : ℂ) by push_cast; ring, Complex.normSq_intCast]
      ring
    have e2 : Complex.normSq ((a : ℂ) * q) = ((a * q : ℤ) : ℝ) ^ 2 := by
      rw [show ((a : ℂ) * q) = ((a * q : ℤ) : ℂ) by push_cast; ring, Complex.normSq_intCast]
      ring
    rw [e1, e2] at h
    have h' : ((1 + (1 - a * q) ^ 2 + (a * q) ^ 2 : ℤ) : ℝ) ≤ ((2 * 3 ^ j : ℤ) : ℝ) := by
      push_cast at h ⊢; linarith
    exact_mod_cast h'
  obtain ⟨r, hr, hr1⟩ := S.exists_Ro
  have hcm := class_mult T T (S.κ r)
  rw [B.sum_R hq hG hTodd hT33 hTodd hT33 hr hr1, ← hc, hξ2, ha, hcj, hG] at hcm
  set N := (((cls T ×ˢ cls T).filter fun p => p.1 * p.2 = S.κ r).card : ℕ) with hN
  have hq1 : 1 ≤ q := by rw [hq]; exact Nat.one_le_pow _ _ (by norm_num)
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hw0 : (q : ℂ) ^ 2 - q + 1 ≠ 0 := by
    have : ((q : ℤ) ^ 2 - q + 1 : ℤ) ≠ 0 := by nlinarith
    exact_mod_cast this
  have hz : ((N : ℤ) * (2 * 3 ^ j) ^ 2 : ℤ) =
      (q : ℤ) ^ 4 * (q - 1) * ((a * (q + 1) - 1) ^ 2 + q ^ 2) := by
    have : (((N : ℤ) * (2 * 3 ^ j) ^ 2 : ℤ) : ℂ) =
        (((q : ℤ) ^ 4 * (q - 1) * ((a * (q + 1) - 1) ^ 2 + q ^ 2) : ℤ) : ℂ) := by
      push_cast [Nat.cast_sub hq1] at hcm ⊢
      rw [show (N : ℂ) * (2 * 3 ^ j) ^ 2 = (N : ℂ) * (2 * 3 ^ j) * (2 * 3 ^ j) by ring, hcm]
      obtain ⟨w, hw⟩ : ∃ w : ℂ, w = (q : ℂ) ^ 2 - q + 1 := ⟨_, rfl⟩
      rw [← hw]
      rw [← hw] at hw0
      rw [show (q : ℂ) ^ 3 + 1 = ((q : ℂ) + 1) * w by rw [hw]; ring]
      have hq10 : (q : ℂ) + 1 ≠ 0 := by
        have : ((q : ℤ) + 1 : ℤ) ≠ 0 := by omega
        exact_mod_cast this
      field_simp
      rw [hw]
      ring
    exact_mod_cast this
  obtain ⟨ha0, hj2⟩ := cT_arith (q := (q : ℤ)) (n := 2 * k + 1) (by rw [hq]; push_cast; ring)
    (by omega) hj hpar hz hlow
  refine ⟨by rw [ha, ha0]; simp, by rw [hξ2, ha0]; simp, ?_⟩
  rw [hcj, hq, ← pow_mul]
  exact Nat.mul_dvd_mul_left 2 (pow_dvd_pow 3 (by omega))

end Block

end CFSG.Walter.WardLocal
