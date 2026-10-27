module

public import CFSG.Quasithin.Background.HL3WrMParam
public import CFSG.Quasithin.Background.HL3WrShat

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix CFSG.Quasithin.H13
open scoped Matrix

@[expose] def t02m : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 1; 0, 1, 0; 0, 0, 1]

@[expose] def c3m : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, 0; 0, 0, 1; 0, 1, 1]

@[expose] def s7m : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![0, 0, 1; 1, 0, 1; 0, 1, 0]

@[expose] def s7i : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 1, 0; 0, 0, 1; 1, 0, 0]

theorem exists_conj_t02m : ∀ a : Matrix (Fin 3) (Fin 3) (ZMod 2), a * a = 1 → a ≠ 1 →
    ∃ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g.det ≠ 0 ∧ a * g = g * t02m := by
  decide +kernel

theorem exists_conj_c3m : ∀ a : Matrix (Fin 3) (Fin 3) (ZMod 2), a * a * a = 1 → a ≠ 1 →
    ∃ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g.det ≠ 0 ∧ a * g = g * c3m := by
  decide +kernel

theorem exists_conj_s7m : ∀ a : Matrix (Fin 3) (Fin 3) (ZMod 2), a ^ 7 = 1 → a ≠ 1 →
    ∃ g : Matrix (Fin 3) (Fin 3) (ZMod 2), g.det ≠ 0 ∧ (a * g = g * s7m ∨ a * g = g * s7i) := by
  decide +kernel

theorem card_filter_t02m_t02m : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    t02m * X * t02mᵀ = X).card = 32 := by
  decide +kernel

theorem card_filter_c3m_one : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    c3m * X * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X).card = 8 := by
  decide +kernel

theorem card_filter_c3m_c3m : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    c3m * X * c3mᵀ = X).card = 8 := by
  decide +kernel

theorem card_filter_s7m_one : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    s7m * X * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X).card = 1 := by
  decide +kernel

theorem card_filter_s7i_one : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    s7i * X * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X).card = 1 := by
  decide +kernel

theorem card_filter_s7m_s7m : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    s7m * X * s7mᵀ = X).card ≤ 8 := by
  decide +kernel

theorem card_filter_s7m_s7i : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    s7m * X * s7iᵀ = X).card ≤ 8 := by
  decide +kernel

theorem card_filter_s7i_s7m : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    s7i * X * s7mᵀ = X).card ≤ 8 := by
  decide +kernel

theorem card_filter_s7i_s7i : (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
    s7i * X * s7iᵀ = X).card ≤ 8 := by
  decide +kernel

@[expose] noncomputable def slOfMat (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hg : g.det ≠ 0) :
    ↥SL32 :=
  ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero g hg, mem_SL32 _⟩

theorem mat_slOfMat (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) (hg : g.det ≠ 0) :
    mat (slOfMat g hg) = g :=
  rfl

theorem eq_of_mat_eq {a b : ↥SL32} (h : mat a = mat b) : a = b := by
  apply Subtype.ext
  apply Units.ext
  exact h

theorem mat_ne_one {a : ↥SL32} (ha : a ≠ 1) : mat a ≠ 1 := fun h =>
  ha (eq_of_mat_eq (h.trans mat_one.symm))

theorem mat_pow (a : ↥SL32) (n : ℕ) : mat (a ^ n) = mat a ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, mat_one]
  | succ n ih => rw [pow_succ, pow_succ, mat_mul, ih]

theorem eq_conj_of_mat {a : ↥SL32} {g r : Matrix (Fin 3) (Fin 3) (ZMod 2)} (hg : g.det ≠ 0)
    (hr : r.det ≠ 0) (h : mat a * g = g * r) :
    a = slOfMat g hg * slOfMat r hr * (slOfMat g hg)⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq]
  apply eq_of_mat_eq
  rw [mat_mul, mat_mul, mat_slOfMat, mat_slOfMat, h]

theorem card_fixV_rho (g : ↥SL32 × ↥SL32) :
    Nat.card ↥(fixV (Subgroup.zpowers (rho g))) =
      (Finset.univ.filter fun X : Matrix (Fin 3) (Fin 3) (ZMod 2) =>
        mat g.1 * X * (mat g.2)ᵀ = X).card := by
  classical
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  refine Nat.card_congr
    { toFun := fun w => ⟨Multiplicative.toAdd (w : WMod), ?_⟩
      invFun := fun X => ⟨Multiplicative.ofAdd X.1, ?_⟩
      left_inv := fun w => rfl
      right_inv := fun X => rfl }
  · have h := mem_fixV_zpowers.mp w.2
    rw [← toAdd_rho]
    exact congrArg Multiplicative.toAdd h
  · rw [mem_fixV_zpowers]
    apply Multiplicative.toAdd.injective
    rw [toAdd_rho]
    exact X.2

theorem rho_conj (g h a b : ↥SL32) :
    rho (g * a * g⁻¹, h * b * h⁻¹) = rho (g, h) * rho (a, b) * (rho (g, h))⁻¹ := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

theorem card_fixV_rho_conj (g h a b : ↥SL32) :
    Nat.card ↥(fixV (Subgroup.zpowers (rho (g * a * g⁻¹, h * b * h⁻¹)))) =
      Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) := by
  rw [rho_conj, card_fixV_conj]

theorem card_fixV_rho_swap (a b : ↥SL32) :
    Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) =
      Nat.card ↥(fixV (Subgroup.zpowers (rho (b, a)))) := by
  have e : rho (b, a) = tau * rho (a, b) * tau⁻¹ := (tau_conj_rho (a, b)).symm
  rw [e, card_fixV_conj]

theorem card_fixV_rho_conj_left (g a b : ↥SL32) :
    Nat.card ↥(fixV (Subgroup.zpowers (rho (g * a * g⁻¹, b)))) =
      Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) := by
  have e : (1 : ↥SL32) * b * 1⁻¹ = b := by group
  rw [← card_fixV_rho_conj g 1 a b, e]

theorem det_t02m : t02m.det ≠ 0 := by decide

theorem det_c3m : c3m.det ≠ 0 := by decide

theorem det_s7m : s7m.det ≠ 0 := by decide

theorem det_s7i : s7i.det ≠ 0 := by decide

theorem card_fixV_rho_diag {a b : ↥SL32} (ha : a * a = 1) (hb : b * b = 1) (ha1 : a ≠ 1)
    (hb1 : b ≠ 1) : Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) = 32 := by
  have hta : mat a * mat a = 1 := by rw [← mat_mul, ha, mat_one]
  have htb : mat b * mat b = 1 := by rw [← mat_mul, hb, mat_one]
  obtain ⟨g, hg, hga⟩ := exists_conj_t02m (mat a) hta (mat_ne_one ha1)
  obtain ⟨h, hh, hhb⟩ := exists_conj_t02m (mat b) htb (mat_ne_one hb1)
  rw [eq_conj_of_mat hg det_t02m hga, eq_conj_of_mat hh det_t02m hhb, card_fixV_rho_conj,
    card_fixV_rho]
  exact card_filter_t02m_t02m

theorem exists_eq_conj_c3m {a : ↥SL32} (ha : a ^ 3 = 1) (ha1 : a ≠ 1) :
    ∃ g : ↥SL32, a = g * slOfMat c3m det_c3m * g⁻¹ := by
  have h3 : mat a * mat a * mat a = 1 := by
    rw [← mat_mul, ← mat_mul, ← pow_three', ha, mat_one]
  obtain ⟨g, hg, hga⟩ := exists_conj_c3m (mat a) h3 (mat_ne_one ha1)
  exact ⟨slOfMat g hg, eq_conj_of_mat hg det_c3m hga⟩

theorem exists_eq_conj_s7m {a : ↥SL32} (ha : a ^ 7 = 1) (ha1 : a ≠ 1) :
    ∃ g : ↥SL32, a = g * slOfMat s7m det_s7m * g⁻¹ ∨ a = g * slOfMat s7i det_s7i * g⁻¹ := by
  have h7 : mat a ^ 7 = 1 := by rw [← mat_pow, ha, mat_one]
  obtain ⟨g, hg, hga | hga⟩ := exists_conj_s7m (mat a) h7 (mat_ne_one ha1)
  · exact ⟨slOfMat g hg, Or.inl (eq_conj_of_mat hg det_s7m hga)⟩
  · exact ⟨slOfMat g hg, Or.inr (eq_conj_of_mat hg det_s7i hga)⟩

theorem card_fixV_rho_le_of_three {a b : ↥SL32} (ha : a ^ 3 = 1) (hb : b ^ 3 = 1)
    (hab : (a, b) ≠ 1) : Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) ≤ 32 := by
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b ≠ 1 := fun h => hab (by rw [h]; rfl)
    obtain ⟨g, rfl⟩ := exists_eq_conj_c3m hb hb1
    rw [card_fixV_rho_swap, card_fixV_rho_conj_left, card_fixV_rho]
    exact card_filter_c3m_one.le.trans (by norm_num)
  · obtain ⟨g, rfl⟩ := exists_eq_conj_c3m ha ha1
    by_cases hb1 : b = 1
    · subst hb1
      rw [card_fixV_rho_conj_left, card_fixV_rho]
      exact card_filter_c3m_one.le.trans (by norm_num)
    · obtain ⟨h, rfl⟩ := exists_eq_conj_c3m hb hb1
      rw [card_fixV_rho_conj, card_fixV_rho]
      exact card_filter_c3m_c3m.le.trans (by norm_num)

theorem card_fixV_rho_le_of_seven {a b : ↥SL32} (ha : a ^ 7 = 1) (hb : b ^ 7 = 1)
    (hab : (a, b) ≠ 1) : Nat.card ↥(fixV (Subgroup.zpowers (rho (a, b)))) ≤ 32 := by
  have h1 : ∀ r : ↥SL32, (r = slOfMat s7m det_s7m ∨ r = slOfMat s7i det_s7i) →
      Nat.card ↥(fixV (Subgroup.zpowers (rho (r, 1)))) ≤ 32 := by
    rintro r (rfl | rfl)
    · rw [card_fixV_rho]
      exact card_filter_s7m_one.le.trans (by norm_num)
    · rw [card_fixV_rho]
      exact card_filter_s7i_one.le.trans (by norm_num)
  by_cases ha1 : a = 1
  · subst ha1
    have hb1 : b ≠ 1 := fun h => hab (by rw [h]; rfl)
    obtain ⟨g, hg | hg⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hg, card_fixV_rho_swap,
      card_fixV_rho_conj_left]
    · exact h1 _ (Or.inl rfl)
    · exact h1 _ (Or.inr rfl)
  · obtain ⟨g, hg | hg⟩ := exists_eq_conj_s7m ha ha1
    · rw [hg]
      by_cases hb1 : b = 1
      · subst hb1
        rw [card_fixV_rho_conj_left]
        exact h1 _ (Or.inl rfl)
      · obtain ⟨h, hh | hh⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hh, card_fixV_rho_conj,
          card_fixV_rho]
        · exact card_filter_s7m_s7m.trans (by norm_num)
        · exact card_filter_s7m_s7i.trans (by norm_num)
    · rw [hg]
      by_cases hb1 : b = 1
      · subst hb1
        rw [card_fixV_rho_conj_left]
        exact h1 _ (Or.inr rfl)
      · obtain ⟨h, hh | hh⟩ := exists_eq_conj_s7m hb hb1 <;> rw [hh, card_fixV_rho_conj,
          card_fixV_rho]
        · exact card_filter_s7i_s7m.trans (by norm_num)
        · exact card_filter_s7i_s7i.trans (by norm_num)

theorem card_fixV_le_of_odd {y : MulAut WMod} (hy : y ∈ norm) (hy1 : y ≠ 1)
    (ho : Odd (orderOf y)) : Nat.card ↥(fixV (Subgroup.zpowers y)) ≤ 32 := by
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  obtain ⟨g, rfl⟩ := mem_img_of_odd hy ho
  set n := orderOf (rho g) with hn
  have hng : n = orderOf g := orderOf_injective rho rho_injective g
  have hn0 : n ≠ 0 := (orderOf_pos (rho g)).ne'
  have hn1 : n ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.mp h)
  have hdvd : n ∣ 168 ^ 2 := by
    rw [hng]
    have h := orderOf_dvd_natCard g
    rwa [Nat.card_prod, card_SL32, ← sq] at h
  have h37 : 3 ∣ n ∨ 7 ∣ n := by
    by_contra hno
    push Not at hno
    have hc2 : Nat.Coprime n 2 := ho.coprime_two_right
    have hc3 : Nat.Coprime n 3 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      Nat.prime_three).mpr hno.1))
    have hc7 : Nat.Coprime n 7 := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd
      (by norm_num)).mpr hno.2))
    have hc : Nat.Coprime n (168 ^ 2) := by
      have e : (168 : ℕ) ^ 2 = 2 ^ 6 * 3 ^ 2 * 7 ^ 2 := by norm_num
      rw [e]
      exact Nat.Coprime.mul_right (Nat.Coprime.mul_right (hc2.pow_right 6) (hc3.pow_right 2))
        (hc7.pow_right 2)
    exact hn1 (Nat.Coprime.eq_one_of_dvd hc hdvd)
  have key : ∀ p : ℕ, p ∣ n → (p = 3 ∨ p = 7) →
      Nat.card ↥(fixV (Subgroup.zpowers (rho g))) ≤ 32 := by
    intro p hp hp37
    have hpo : orderOf (rho g ^ (n / p)) = p := orderOf_pow_orderOf_div hn0 hp
    obtain ⟨g', hg'⟩ : ∃ g', g' = g ^ (n / p) := ⟨_, rfl⟩
    have hrho : rho g ^ (n / p) = rho g' := by rw [hg', map_pow]
    have hg'p : g' ^ p = 1 := by
      have h1 := pow_orderOf_eq_one (rho g ^ (n / p))
      rw [hpo, hrho] at h1
      apply rho_injective
      rw [map_pow, h1, map_one]
    have hg'1 : g' ≠ 1 := fun h => by
      rw [hrho, h, map_one, orderOf_one] at hpo
      rcases hp37 with rfl | rfl <;> omega
    have hle : fixV (Subgroup.zpowers (rho g)) ≤ fixV (Subgroup.zpowers (rho g')) := by
      refine B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ?_)
      rw [← hrho]
      exact (Subgroup.zpowers (rho g)).pow_mem (Subgroup.mem_zpowers (rho g)) _
    refine (Subgroup.card_le_of_le hle).trans ?_
    have hab : (g'.1, g'.2) ≠ 1 := hg'1
    rcases hp37 with rfl | rfl
    · exact card_fixV_rho_le_of_three (by rw [← Prod.pow_fst, hg'p]; rfl)
        (by rw [← Prod.pow_snd, hg'p]; rfl) hab
    · exact card_fixV_rho_le_of_seven (by rw [← Prod.pow_fst, hg'p]; rfl)
        (by rw [← Prod.pow_snd, hg'p]; rfl) hab
  rcases h37 with h | h
  · exact key 3 h (Or.inl rfl)
  · exact key 7 h (Or.inr rfl)

theorem tau_eW_diag (i : Fin 3) : tau (eW i i) = eW i i := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_tau]
  exact Matrix.transpose_single i i (1 : ZMod 2)

theorem eq_one_of_single_diag {c d : Matrix (Fin 3) (Fin 3) (ZMod 2)}
    (h : ∀ i : Fin 3, c * Matrix.single i i 1 * dᵀ = Matrix.single i i 1) : c = 1 ∧ d = 1 := by
  have hent : ∀ i j k : Fin 3, c j i * d k i = Matrix.single i i (1 : ZMod 2) j k := by
    intro i j k
    rw [← h i, Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [Matrix.mul_single_apply_same, mul_one, Matrix.transpose_apply]
    · intro l _ hl
      rw [Matrix.mul_single_apply_of_ne (hbj := hl), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have h11 : ∀ x y : ZMod 2, x * y = 1 → x = 1 ∧ y = 1 := by decide
  have hdiag : ∀ i, c i i = 1 ∧ d i i = 1 := fun i => h11 _ _ (by
    rw [hent]
    simp)
  have hc : ∀ i j, j ≠ i → c j i = 0 := fun i j hji => by
    have h1 := hent i j i
    rw [(hdiag i).2, mul_one] at h1
    rw [h1]
    simp [Ne.symm hji]
  have hd : ∀ i k, k ≠ i → d k i = 0 := fun i k hki => by
    have h1 := hent i i k
    rw [(hdiag i).1, one_mul] at h1
    rw [h1]
    simp [Ne.symm hki]
  refine ⟨Matrix.ext fun j i => ?_, Matrix.ext fun k i => ?_⟩
  · by_cases hji : j = i
    · subst hji
      rw [(hdiag j).1, Matrix.one_apply_eq]
    · rw [hc i j hji, Matrix.one_apply_ne hji]
  · by_cases hki : k = i
    · subst hki
      rw [(hdiag k).2, Matrix.one_apply_eq]
    · rw [hd i k hki, Matrix.one_apply_ne hki]

theorem eq_one_or_eq_tau {y : MulAut WMod} (hy : y ∈ norm)
    (hfix : ∀ i : Fin 3, y (eW i i) = eW i i) : y = 1 ∨ y = tau := by
  obtain ⟨g, rfl | rfl⟩ := mem_norm_iff.mp hy
  · left
    have hc : ∀ i : Fin 3, mat g.1 * Matrix.single i i 1 * (mat g.2)ᵀ = Matrix.single i i 1 :=
      fun i => by
        have h := congrArg Multiplicative.toAdd (hfix i)
        rw [toAdd_rho] at h
        exact h
    obtain ⟨h1, h2⟩ := eq_one_of_single_diag hc
    have hg : g = 1 :=
      Prod.ext (eq_of_mat_eq (h1.trans mat_one.symm)) (eq_of_mat_eq (h2.trans mat_one.symm))
    rw [hg, map_one]
  · right
    have hc : ∀ i : Fin 3, mat g.1 * Matrix.single i i 1 * (mat g.2)ᵀ = Matrix.single i i 1 :=
      fun i => by
        have h := congrArg Multiplicative.toAdd (hfix i)
        change Multiplicative.toAdd (rho g (tau (eW i i))) = _ at h
        rw [tau_eW_diag, toAdd_rho] at h
        exact h
    obtain ⟨h1, h2⟩ := eq_one_of_single_diag hc
    have hg : g = 1 :=
      Prod.ext (eq_of_mat_eq (h1.trans mat_one.symm)) (eq_of_mat_eq (h2.trans mat_one.symm))
    rw [hg, map_one, one_mul]

theorem eq_one_or_eq_of_fix_of_not_mem_img {s y : MulAut WMod} (hs : s ∈ norm) (hss : s * s = 1)
    (hsi : s ∉ img) (hy : y ∈ norm) (hfix : ∀ w ∈ fixV (Subgroup.zpowers s), y w = w) :
    y = 1 ∨ y = s := by
  obtain ⟨g, hg | hg⟩ := mem_norm_iff.mp hs
  · exact absurd (hg ▸ rho_mem_img g) hsi
  have hg12 : g.1 * g.2 = 1 := by
    have hss' : rho g * tau * (rho g * tau) = 1 := hg ▸ hss
    have h : rho (g * g.swap) = 1 := by
      rw [map_mul]
      calc rho g * rho g.swap = rho g * (tau * rho g * tau⁻¹) := by rw [tau_conj_rho]
        _ = rho g * tau * (rho g * tau) * (tau⁻¹ * tau⁻¹) := by group
        _ = 1 := by rw [hss', one_mul, tau_inv, tau_mul_self]
    exact congrArg Prod.fst (rho_injective (h.trans (map_one rho).symm))
  have hg2 : g.2 = g.1⁻¹ := eq_inv_of_mul_eq_one_right hg12
  set φ := rho (g.1, 1) with hφ
  have hsφ : s = φ * tau * φ⁻¹ := by
    rw [hg, hφ, ← map_inv, mul_assoc, tau_mul_rho, ← mul_assoc, ← map_mul]
    congr 2
    refine Prod.ext ?_ ?_
    · change g.1 = g.1 * (1 : ↥SL32)⁻¹
      rw [inv_one, mul_one]
    · change g.2 = 1 * g.1⁻¹
      rw [one_mul, hg2]
  have hφn : φ ∈ norm := img_le_norm (rho_mem_img _)
  have hy' : φ⁻¹ * y * φ ∈ norm := norm.mul_mem (norm.mul_mem (norm.inv_mem hφn) hy) hφn
  have hfix' : ∀ i : Fin 3, (φ⁻¹ * y * φ) (eW i i) = eW i i := by
    intro i
    have hmem : φ (eW i i) ∈ fixV (Subgroup.zpowers s) := by
      rw [mem_fixV_zpowers, hsφ]
      change φ (tau (φ⁻¹ (φ (eW i i)))) = φ (eW i i)
      rw [MulAut.inv_apply_self, tau_eW_diag]
    change φ⁻¹ (y (φ (eW i i))) = eW i i
    rw [hfix _ hmem, MulAut.inv_apply_self]
  rcases eq_one_or_eq_tau hy' hfix' with h | h
  · left
    calc y = φ * (φ⁻¹ * y * φ) * φ⁻¹ := by group
      _ = 1 := by rw [h]; group
  · right
    calc y = φ * (φ⁻¹ * y * φ) * φ⁻¹ := by group
      _ = s := by rw [h, hsφ]

theorem exists_transvection_of_le_norm {A : Subgroup (MulAut WMod)} (hAn : A ≤ norm)
    (hA2 : IsElemAbelian2 A) (hA4 : 4 ≤ Nat.card A) (hfix : 64 ≤ Nat.card (fixV A)) :
    ∃ t : ↥SL32, t * t = 1 ∧ t ≠ 1 ∧
      (fixV A = fixV (Subgroup.zpowers (rho (t, 1))) ∨
        fixV A = fixV (Subgroup.zpowers (rho (1, t)))) := by
  have : Finite (MulAut WMod) := MulEquiv.finite_left
  have hsq : ∀ s ∈ A, s * s = 1 := fun s hs => by rw [← sq]; exact hA2.2 s hs
  have hord : ∀ s ∈ A, s ≠ 1 → orderOf s = 2 := fun s hs hs1 => by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (hA2.2 s hs) hs1
  have hfixeq : ∀ s ∈ A, s ≠ 1 → fixV A = fixV (Subgroup.zpowers s) := fun s hs hs1 => by
    have hle : fixV A ≤ fixV (Subgroup.zpowers s) :=
      B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hs)
    exact Subgroup.eq_of_le_of_card_ge hle ((card_fixV_le (hAn hs) (hord s hs hs1)).trans hfix)
  have himg : ∀ s ∈ A, s ∈ img := by
    intro s hs
    by_contra hsi
    have hs1 : s ≠ 1 := fun h => hsi (h ▸ img.one_mem)
    have hb : ∃ b ∈ A, b ≠ 1 ∧ b ≠ s := by
      by_contra hno
      push Not at hno
      have hle : A ≤ Subgroup.zpowers s := fun b hb => by
        by_cases hb1 : b = 1
        · rw [hb1]
          exact (Subgroup.zpowers s).one_mem
        · rw [hno b hb hb1]
          exact Subgroup.mem_zpowers s
      have h1 := Subgroup.card_le_of_le hle
      rw [Nat.card_zpowers, hord s hs hs1] at h1
      omega
    obtain ⟨b, hbA, hb1, hbs⟩ := hb
    have hbfix : ∀ w ∈ fixV (Subgroup.zpowers s), b w = w := fun w hw => by
      rw [← hfixeq s hs hs1] at hw
      exact hw b hbA
    rcases eq_one_or_eq_of_fix_of_not_mem_img (hAn hs) (hsq s hs) hsi (hAn hbA) hbfix with h | h
    · exact hb1 h
    · exact hbs h
  obtain ⟨s, hsA, hs1⟩ : ∃ s ∈ A, s ≠ 1 := by
    by_contra hno
    push Not at hno
    have hA1 : A = ⊥ := eq_bot_iff.mpr fun s hs => (Subgroup.mem_bot).mpr (hno s hs)
    rw [hA1, Subgroup.card_bot] at hA4
    omega
  obtain ⟨g, rfl⟩ := himg s hsA
  have hgg : g * g = 1 := rho_injective (by rw [map_mul, hsq _ hsA, map_one])
  have hg1 : g ≠ 1 := fun h => hs1 (by rw [h, map_one])
  have hfs := hfixeq _ hsA hs1
  by_cases ha : g.1 = 1
  · have hb : g.2 ≠ 1 := fun h => hg1 (Prod.ext ha h)
    refine ⟨g.2, congrArg Prod.snd hgg, hb, Or.inr ?_⟩
    rw [hfs]
    congr 3
    exact Prod.ext ha rfl
  · by_cases hb : g.2 = 1
    · refine ⟨g.1, congrArg Prod.fst hgg, ha, Or.inl ?_⟩
      rw [hfs]
      congr 3
      exact Prod.ext rfl hb
    · exfalso
      have h32 := card_fixV_rho_diag (congrArg Prod.fst hgg) (congrArg Prod.snd hgg) ha hb
      have h64 : 64 ≤ Nat.card ↥(fixV (Subgroup.zpowers (rho g))) := hfs ▸ hfix
      rw [show rho g = rho (g.1, g.2) from rfl, h32] at h64
      omega

abbrev axMat (x y : ZMod 2) : Matrix (Fin 3) (Fin 3) (ZMod 2) := !![1, 0, x; 0, 1, y; 0, 0, 1]

theorem axMat_mul (x y x' y' : ZMod 2) :
    axMat x y * axMat x' y' = axMat (x + x') (y + y') := by
  revert x y x' y'
  decide

theorem axMat_mul_self (x y : ZMod 2) : axMat x y * axMat x y = 1 := by
  revert x y
  decide

theorem axMat_zero : axMat 0 0 = 1 := by decide

@[expose] def R1 : Subgroup ↥SL32 where
  carrier := {g | ∃ x y : ZMod 2, mat g = axMat x y}
  mul_mem' := by
    rintro g h ⟨x, y, hg⟩ ⟨x', y', hh⟩
    exact ⟨x + x', y + y', by rw [mat_mul, hg, hh, axMat_mul]⟩
  one_mem' := ⟨0, 0, by rw [mat_one, axMat_zero]⟩
  inv_mem' := by
    rintro g ⟨x, y, hg⟩
    refine ⟨x, y, ?_⟩
    calc mat g⁻¹ = mat g⁻¹ * (mat g * mat g) := by rw [hg, axMat_mul_self, Matrix.mul_one]
      _ = axMat x y := by rw [← Matrix.mul_assoc, mat_inv_mul, Matrix.one_mul, hg]

theorem R1_le_U3 : R1 ≤ U3 := by
  rintro g ⟨x, y, hg⟩
  have h1 : ∀ x y : ZMod 2, axMat x y *ᵥ e0 = e0 := by decide
  have h2 : ∀ x y : ZMod 2, e2 ᵥ* axMat x y = e2 := by decide
  refine ⟨?_, ?_⟩
  · change mat g *ᵥ e0 = e0
    rw [hg]
    exact h1 x y
  · change e2 ᵥ* mat g = e2
    rw [hg]
    exact h2 x y

@[expose] noncomputable def t02 : ↥SL32 := slOfMat t02m det_t02m

theorem t02_ne_one : t02 ≠ 1 := fun h => by
  have h1 := congrArg mat h
  rw [mat_one] at h1
  exact absurd h1 (by decide)

theorem fix_axMat_left : ∀ x y : ZMod 2, (x, y) ≠ (0, 0) → ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2),
    (axMat x y * X * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X ↔
      t02m * X * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = X) := by
  decide +kernel

theorem fix_axMat_right : ∀ x y : ZMod 2, (x, y) ≠ (0, 0) → ∀ X : Matrix (Fin 3) (Fin 3) (ZMod 2),
    ((1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X * (axMat x y)ᵀ = X ↔
      (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * X * t02mᵀ = X) := by
  decide +kernel

theorem card_R1 : Nat.card ↥R1 = 4 := by
  have h : Nat.card ↥R1 = Nat.card {a : ↥SL32 // ∃ x y : ZMod 2, mat a = axMat x y} := rfl
  rw [h]
  exact (card_SL32_subtype (fun M => ∃ x y : ZMod 2, M = axMat x y)).trans (by decide +kernel)

@[expose] noncomputable def A1 : Subgroup (MulAut WMod) := (R1.prod ⊥).map rho

@[expose] noncomputable def A2 : Subgroup (MulAut WMod) := ((⊥ : Subgroup ↥SL32).prod R1).map rho

theorem t02_mem_R1 : t02 ∈ R1 := ⟨1, 0, rfl⟩

theorem axMat_ne_of_ne_one {g : ↥SL32} {x y : ZMod 2} (hg : mat g = axMat x y) (hg1 : g ≠ 1) :
    (x, y) ≠ (0, 0) := fun h => by
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
  exact hg1 (eq_of_mat_eq (by rw [hg, axMat_zero, mat_one]))

theorem fixV_rho_R1_left {g : ↥SL32} (hg : g ∈ R1) (hg1 : g ≠ 1) :
    fixV (Subgroup.zpowers (rho (g, 1))) = fixV (Subgroup.zpowers (rho (t02, 1))) := by
  obtain ⟨x, y, hxy⟩ := hg
  have hne := axMat_ne_of_ne_one hxy hg1
  ext w
  rw [mem_fixV_zpowers, mem_fixV_zpowers, ← Multiplicative.toAdd.injective.eq_iff,
    ← Multiplicative.toAdd.injective.eq_iff, toAdd_rho, toAdd_rho]
  change mat g * _ * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = _ ↔
    t02m * _ * (1 : Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ = _
  rw [hxy]
  exact fix_axMat_left x y hne _

theorem fixV_rho_R1_right {g : ↥SL32} (hg : g ∈ R1) (hg1 : g ≠ 1) :
    fixV (Subgroup.zpowers (rho (1, g))) = fixV (Subgroup.zpowers (rho (1, t02))) := by
  obtain ⟨x, y, hxy⟩ := hg
  have hne := axMat_ne_of_ne_one hxy hg1
  ext w
  rw [mem_fixV_zpowers, mem_fixV_zpowers, ← Multiplicative.toAdd.injective.eq_iff,
    ← Multiplicative.toAdd.injective.eq_iff, toAdd_rho, toAdd_rho]
  change (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * _ * (mat g)ᵀ = _ ↔
    (1 : Matrix (Fin 3) (Fin 3) (ZMod 2)) * _ * t02mᵀ = _
  rw [hxy]
  exact fix_axMat_right x y hne _

theorem card_A1 : Nat.card ↥A1 = 4 := by
  unfold A1
  rw [Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_R1,
    Subgroup.card_bot, mul_one]

theorem card_A2 : Nat.card ↥A2 = 4 := by
  unfold A2
  rw [Subgroup.card_map_of_injective rho_injective, card_prod_subgroup, card_R1,
    Subgroup.card_bot, one_mul]

theorem fixV_A1 : fixV A1 = fixV (Subgroup.zpowers (rho (t02, 1))) := by
  apply le_antisymm
  · exact B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ⟨(t02, 1), ⟨t02_mem_R1, Subgroup.one_mem _⟩,
      rfl⟩)
  · rintro w hw _ ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩
    obtain rfl : h = 1 := Subgroup.mem_bot.mp hh
    by_cases hg1 : g = 1
    · rw [hg1]
      change rho 1 w = w
      rw [map_one]
      rfl
    · rw [← fixV_rho_R1_left hg hg1] at hw
      exact mem_fixV_zpowers.mp hw

theorem fixV_A2 : fixV A2 = fixV (Subgroup.zpowers (rho (1, t02))) := by
  apply le_antisymm
  · exact B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ⟨(1, t02), ⟨Subgroup.one_mem _, t02_mem_R1⟩,
      rfl⟩)
  · rintro w hw _ ⟨⟨h, g⟩, ⟨hh, hg⟩, rfl⟩
    obtain rfl : h = 1 := Subgroup.mem_bot.mp hh
    by_cases hg1 : g = 1
    · rw [hg1]
      change rho 1 w = w
      rw [map_one]
      rfl
    · rw [← fixV_rho_R1_right hg hg1] at hw
      exact mem_fixV_zpowers.mp hw

theorem padicValNat_four : padicValNat 2 4 = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num, padicValNat.prime_pow]

theorem A1_mem_aSet {Y : Subgroup (MulAut WMod)} (hY : (U3.prod U3).map rho ≤ Y) :
    A1 ∈ E3.aSet 2 Y := by
  have hne : A1 ≠ ⊥ := by
    intro h
    have hm : rho (t02, 1) ∈ A1 := ⟨(t02, 1), ⟨t02_mem_R1, Subgroup.one_mem _⟩, rfl⟩
    have h1 : rho (t02, 1) = 1 := Subgroup.mem_bot.mp ((Subgroup.ext_iff.mp h _).mp hm)
    exact t02_ne_one (congrArg Prod.fst (rho_injective (h1.trans (map_one rho).symm)))
  have hcomm : ∀ a ∈ A1, ∀ b ∈ A1, a * b = b * a := by
    rintro _ ⟨⟨g, h⟩, ⟨⟨x, y, hg⟩, hh⟩, rfl⟩ _ ⟨⟨g', h'⟩, ⟨⟨x', y', hg'⟩, hh'⟩, rfl⟩
    obtain rfl : h = 1 := Subgroup.mem_bot.mp hh
    obtain rfl : h' = 1 := Subgroup.mem_bot.mp hh'
    have hg2 : mat g = axMat x y := hg
    have hg2' : mat g' = axMat x' y' := hg'
    have hgg : g * g' = g' * g := eq_of_mat_eq (by
      rw [mat_mul, mat_mul, hg2, hg2', axMat_mul, axMat_mul, add_comm x, add_comm y])
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext hgg rfl
  have hsq : ∀ a ∈ A1, a ^ 2 = 1 := by
    rintro _ ⟨⟨g, h⟩, ⟨⟨x, y, hg⟩, hh⟩, rfl⟩
    obtain rfl : h = 1 := Subgroup.mem_bot.mp hh
    have hg2 : mat g = axMat x y := hg
    have e : ((g, 1) : ↥SL32 × ↥SL32) ^ 2 = 1 := by
      refine Prod.ext (eq_of_mat_eq ?_) (by simp)
      change mat (g ^ 2) = mat 1
      rw [mat_pow, hg2, sq, axMat_mul_self, mat_one]
    rw [← map_pow, e, map_one]
  have hfixB : ∀ B : Subgroup (MulAut WMod), B ≤ A1 → E3.mQuot A1 B < 2 → fixV B = fixV A1 := by
    intro B hB hm
    have hB1 : B ≠ ⊥ := by
      rintro rfl
      unfold E3.mQuot at hm
      rw [Subgroup.relIndex_bot_left, card_A1, padicValNat_four] at hm
      omega
    obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨⟨g, h⟩, ⟨hg, hh⟩, rfl⟩ := hB hbB
    obtain rfl : h = 1 := Subgroup.mem_bot.mp hh
    have hg1 : g ≠ 1 := fun h1 => hb1' (by rw [h1]; exact map_one rho)
    apply le_antisymm
    · rw [fixV_A1, ← fixV_rho_R1_left hg hg1]
      exact B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hbB)
    · exact B1.fixV_le_fixV hB
  exact ⟨(Subgroup.map_mono (Subgroup.prod_mono R1_le_U3 bot_le)).trans hY, hne, ⟨hcomm, hsq⟩,
    hfixB⟩

theorem A2_mem_aSet {Y : Subgroup (MulAut WMod)} (hY : (U3.prod U3).map rho ≤ Y) :
    A2 ∈ E3.aSet 2 Y := by
  have hne : A2 ≠ ⊥ := by
    intro h
    have hm : rho (1, t02) ∈ A2 := ⟨(1, t02), ⟨Subgroup.one_mem _, t02_mem_R1⟩, rfl⟩
    have h1 : rho (1, t02) = 1 := Subgroup.mem_bot.mp ((Subgroup.ext_iff.mp h _).mp hm)
    exact t02_ne_one (congrArg Prod.snd (rho_injective (h1.trans (map_one rho).symm)))
  have hcomm : ∀ a ∈ A2, ∀ b ∈ A2, a * b = b * a := by
    rintro _ ⟨⟨h, g⟩, ⟨hh, ⟨x, y, hg⟩⟩, rfl⟩ _ ⟨⟨h', g'⟩, ⟨hh', ⟨x', y', hg'⟩⟩, rfl⟩
    obtain rfl : h = 1 := Subgroup.mem_bot.mp hh
    obtain rfl : h' = 1 := Subgroup.mem_bot.mp hh'
    have hg2 : mat g = axMat x y := hg
    have hg2' : mat g' = axMat x' y' := hg'
    have hgg : g * g' = g' * g := eq_of_mat_eq (by
      rw [mat_mul, mat_mul, hg2, hg2', axMat_mul, axMat_mul, add_comm x, add_comm y])
    rw [← map_mul, ← map_mul]
    congr 1
    exact Prod.ext rfl hgg
  have hsq : ∀ a ∈ A2, a ^ 2 = 1 := by
    rintro _ ⟨⟨h, g⟩, ⟨hh, ⟨x, y, hg⟩⟩, rfl⟩
    obtain rfl : h = 1 := Subgroup.mem_bot.mp hh
    have hg2 : mat g = axMat x y := hg
    have e : ((1, g) : ↥SL32 × ↥SL32) ^ 2 = 1 := by
      refine Prod.ext (by simp) (eq_of_mat_eq ?_)
      change mat (g ^ 2) = mat 1
      rw [mat_pow, hg2, sq, axMat_mul_self, mat_one]
    rw [← map_pow, e, map_one]
  have hfixB : ∀ B : Subgroup (MulAut WMod), B ≤ A2 → E3.mQuot A2 B < 2 → fixV B = fixV A2 := by
    intro B hB hm
    have hB1 : B ≠ ⊥ := by
      rintro rfl
      unfold E3.mQuot at hm
      rw [Subgroup.relIndex_bot_left, card_A2, padicValNat_four] at hm
      omega
    obtain ⟨⟨b, hbB⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
    have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
    obtain ⟨⟨h, g⟩, ⟨hh, hg⟩, rfl⟩ := hB hbB
    obtain rfl : h = 1 := Subgroup.mem_bot.mp hh
    have hg1 : g ≠ 1 := fun h1 => hb1' (by rw [h1]; exact map_one rho)
    apply le_antisymm
    · rw [fixV_A2, ← fixV_rho_R1_right hg hg1]
      exact B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hbB)
    · exact B1.fixV_le_fixV hB
  exact ⟨(Subgroup.map_mono (Subgroup.prod_mono bot_le R1_le_U3)).trans hY, hne, ⟨hcomm, hsq⟩,
    hfixB⟩

theorem fixV_zpowers_conj (φ x : MulAut WMod) :
    fixV (Subgroup.zpowers (φ * x * φ⁻¹)) = (fixV (Subgroup.zpowers x)).map φ.toMonoidHom :=
  CFSG.Quasithin.fixV_zpowers_conj φ x

theorem exists_fixV_rho_left_eq {t : ↥SL32} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g : ↥SL32, fixV (Subgroup.zpowers (rho (t, 1))) =
      (fixV (Subgroup.zpowers (rho (t02, 1)))).map (rho (g, 1)).toMonoidHom := by
  have htm : mat t * mat t = 1 := by rw [← mat_mul, ht, mat_one]
  obtain ⟨g, hg, hgt⟩ := exists_conj_t02m (mat t) htm (mat_ne_one ht1)
  refine ⟨slOfMat g hg, ?_⟩
  have e : rho (t, 1) = rho (slOfMat g hg, 1) * rho (t02, 1) * (rho (slOfMat g hg, 1))⁻¹ := by
    rw [← rho_conj]
    congr 2
    · exact eq_conj_of_mat hg det_t02m hgt
    · group
  rw [e, fixV_zpowers_conj]

theorem exists_fixV_rho_right_eq {t : ↥SL32} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ g : ↥SL32, fixV (Subgroup.zpowers (rho (1, t))) =
      (fixV (Subgroup.zpowers (rho (1, t02)))).map (rho (1, g)).toMonoidHom := by
  have htm : mat t * mat t = 1 := by rw [← mat_mul, ht, mat_one]
  obtain ⟨g, hg, hgt⟩ := exists_conj_t02m (mat t) htm (mat_ne_one ht1)
  refine ⟨slOfMat g hg, ?_⟩
  have e : rho (1, t) = rho (1, slOfMat g hg) * rho (1, t02) * (rho (1, slOfMat g hg))⁻¹ := by
    rw [← rho_conj]
    congr 2
    · group
    · exact eq_conj_of_mat hg det_t02m hgt
  rw [e, fixV_zpowers_conj]

theorem exists_aSet_map_le {Y A : Subgroup (MulAut WMod)} (hY : (U3.prod U3).map rho ≤ Y)
    (hAn : A ≤ norm) (hA2 : IsElemAbelian2 A) (hA4 : 4 ≤ Nat.card A)
    (hfix : 64 ≤ Nat.card ↥(fixV A)) :
    ∃ B ∈ E3.aSet 2 Y, ∃ y ∈ img, (fixV B).map y.toMonoidHom ≤ fixV A := by
  obtain ⟨t, ht, ht1, h | h⟩ := exists_transvection_of_le_norm hAn hA2 hA4 hfix
  · obtain ⟨g, hg⟩ := exists_fixV_rho_left_eq ht ht1
    refine ⟨A1, A1_mem_aSet hY, rho (g, 1), rho_mem_img _, ?_⟩
    rw [fixV_A1, h, hg]
  · obtain ⟨g, hg⟩ := exists_fixV_rho_right_eq ht ht1
    refine ⟨A2, A2_mem_aSet hY, rho (1, g), rho_mem_img _, ?_⟩
    rw [fixV_A2, h, hg]

end L3Wr

end H

end CFSG.Quasithin
