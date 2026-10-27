module

public import CFSG.RankThree.GF2n.Smith81.OrthTensorModel
public import CFSG.RankThree.GF2n.Stroth80.Sec310SLTransv
public import CFSG.RankThree.GF2n.Stroth80.Sec57B
public import CFSG.RankThree.GF2n.Stroth80.Sec310Nt
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

theorem orth_even_card (K : Type) [Field K] [Finite K] [CharP K 2] : Even (Nat.card K) := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hn⟩ := FiniteField.card K 2
  rw [Nat.card_eq_fintype_card, hn]
  exact (Nat.even_pow.mpr ⟨even_two, PNat.ne_zero n⟩)

theorem orth_odd_prod_pow_sub_one {r : ℤ} (hr : Even r) {s : Finset ℕ} {e : ℕ → ℕ}
    (he : ∀ j ∈ s, e j ≠ 0) : Odd (∏ j ∈ s, (r ^ e j - 1)) := by
  refine Finset.prod_induction _ Odd (fun a b ha hb => ha.mul hb) odd_one (fun j hj => ?_)
  exact (hr.pow_of_ne_zero (he j hj)).sub_odd odd_one

theorem orth_pow_mul_odd_inj {q : ℤ} (hq : Even q) (hq0 : q ≠ 0) {a b : ℕ} {X Y : ℤ}
    (hX : Odd X) (hY : Odd Y) (h : q ^ a * X = q ^ b * Y) : a = b := by
  have key : ∀ {a b : ℕ} {X Y : ℤ}, Odd X → q ^ a * X = q ^ b * Y → b ≤ a := by
    intro a b X Y hX h
    by_contra hlt
    push Not at hlt
    obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
    have h1 : q ^ a * X = q ^ a * (q ^ (d + 1) * Y) := by rw [h]; ring
    have h2 : X = q ^ (d + 1) * Y := mul_left_cancel₀ (pow_ne_zero a hq0) h1
    have h3 : Even X := by
      rw [h2]
      exact (hq.pow_of_ne_zero (Nat.succ_ne_zero d)).mul_right Y
    exact (Int.not_even_iff_odd.mpr hX) h3
  exact le_antisymm (key hY h.symm) (key hX h)

theorem card_orth_two_minus {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) =
      2 * Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)⁆ := by
  have hmin := CFSG.ClassicalGroups.Orthogonal.isMinus_quadMinus (K := K) (m := 2)
    (by norm_num) hirr
  obtain ⟨-, -, -, hidx, -, -, -⟩ :=
    CFSG.RankThree.PartOne.even_minus_four_six_actual_derived_extraction
      (quadMinus 2 K b c) hmin.nondeg (Or.inl (by rw [hmin.finrank_eq]))
      (fun U hU => hmin.noTS U (by rw [hmin.finrank_eq] at hU; omega))
  have hle : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)⁆ ≤
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c) := by
    rw [Subgroup.commutator_le]
    intro g hg h hh
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)
  have hcard := ((⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)⁆).subgroupOf
        (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c))).card_mul_index
  rw [hidx, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at hcard
  omega

theorem card_statedOmega_minus_eq_of_two_le {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hm : 2 ≤ m) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (Nat.card ↥(StatedOmega (StatedQuadMinus m K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m + 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · rw [CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map_of_two_le (n := 2)
        (by norm_num) hirr, Subgroup.card_map_of_injective (MulEquiv.injective _),
      ← CFSG.ClassicalGroups.Orthogonal.commutator_orthogonalGroup_quadMinus_of_two_le
        (n := 2) (by norm_num) hirr]
    have h2 : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
        2 * (Nat.card ↥⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c),
          TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)⁆ : ℤ) := by
      exact_mod_cast card_orth_two_minus hirr
    have hO : (Nat.card (TauCeti.QuadraticMap.orthogonalGroup (quadMinus 2 K b c)) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (2 * (2 - 1)) * ((Nat.card K : ℤ) ^ 2 + 1) *
          ∏ i ∈ Finset.Icc 1 (2 - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) :=
      (CFSG.Timmesfeld.ClassicalOrders.card_quadMinus 1 hirr).2
    linarith
  · exact card_statedOmega_minus_eq h3 hirr

section OrderForms

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem orth_even_card_int (K : Type) [Field K] [Finite K] [CharP K 2] :
    Even (Nat.card K : ℤ) := by
  obtain ⟨r, hr⟩ := orth_even_card K
  exact ⟨r, by exact_mod_cast hr⟩

theorem orth_card_omegaPlus_form (hq : 4 ≤ Nat.card K) {k : ℕ} (hk : 2 ≤ k) :
    ∃ X : ℤ, Odd X ∧ (Nat.card ↥(StatedOmega (StatedQuadPlus k K)) : ℤ) =
      (Nat.card K : ℤ) ^ (k * (k - 1)) * X := by
  have hev : Even (Nat.card K : ℤ) := orth_even_card_int K
  rcases (show k = 2 ∨ 3 ≤ k by omega) with rfl | h3
  · obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K hq
    refine ⟨((Nat.card K : ℤ) ^ 2 - 1) ^ 2, ?_, ?_⟩
    · exact ((hev.pow_of_ne_zero two_ne_zero).sub_odd odd_one).pow
    · rw [Nat.card_congr e.toEquiv, Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two]
      have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
      push_cast [Nat.cast_sub this]
      ring
  · refine ⟨((Nat.card K : ℤ) ^ k - 1) *
      ∏ i ∈ Finset.Icc 1 (k - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1), ?_, ?_⟩
    · refine ((hev.pow_of_ne_zero (by omega)).sub_odd odd_one).mul
        (orth_odd_prod_pow_sub_one hev (e := fun i => 2 * i) (fun j hj => ?_))
      have := (Finset.mem_Icc.mp hj).1
      omega
    · rw [card_statedOmega_plus_eq h3]
      ring

theorem orth_card_omegaMinus_form {k : ℕ} (hk : 2 ≤ k) {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ X : ℤ, Odd X ∧ (Nat.card ↥(StatedOmega (StatedQuadMinus k K b c)) : ℤ) =
      (Nat.card K : ℤ) ^ (k * (k - 1)) * X := by
  have hev : Even (Nat.card K : ℤ) := orth_even_card_int K
  refine ⟨((Nat.card K : ℤ) ^ k + 1) *
    ∏ i ∈ Finset.Icc 1 (k - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1), ?_, ?_⟩
  · refine ((hev.pow_of_ne_zero (by omega)).add_one).mul
      (orth_odd_prod_pow_sub_one hev (e := fun i => 2 * i) (fun j hj => ?_))
    have := (Finset.mem_Icc.mp hj).1
    omega
  · rw [card_statedOmega_minus_eq_of_two_le hk hirr]
    ring

theorem orth_card_sp_form (k : ℕ) :
    ∃ X : ℤ, Odd X ∧ (Nat.card ↥(StatedSp k K) : ℤ) = (Nat.card K : ℤ) ^ (k ^ 2) * X := by
  have hev : Even (Nat.card K : ℤ) := orth_even_card_int K
  refine ⟨∏ j ∈ Finset.Icc 1 k, (((Nat.card K : ℤ) ^ 2) ^ j - 1), ?_,
    CFSG.GroupTheory.WeirSylow.natCard_statedSp_cast K k⟩
  refine orth_odd_prod_pow_sub_one (r := (Nat.card K : ℤ) ^ 2)
    (hev.pow_of_ne_zero two_ne_zero) (e := fun j => j) (fun j hj => ?_)
  have := (Finset.mem_Icc.mp hj).1
  omega

theorem orth_dvd_card_statedSL {k : ℕ} (hk : 1 ≤ k) :
    (Nat.card K) ^ (∑ i ∈ Finset.range k, i) ∣ Nat.card ↥(StatedSL k K) := by
  classical
  haveI : NeZero k := ⟨by omega⟩
  letI : Fintype K := Fintype.ofFinite K
  have h1 := Matrix.card_SL_mul_card_units (n := Fin k) (R := K)
  have h2 := Matrix.card_GL_field (𝔽 := K) k
  rw [← CFSG.Open.StatedAPI.card_statedSL, Nat.card_units] at h1
  have hq : Fintype.card K = Nat.card K := (Nat.card_eq_fintype_card).symm
  rw [hq] at h2
  have h3 : Nat.card ↥(StatedSL k K) * (Nat.card K - 1) =
      ∏ i : Fin k, (Nat.card K ^ k - Nat.card K ^ (i : ℕ)) := h1.trans h2
  have h4 : (Nat.card K) ^ (∑ i ∈ Finset.range k, i) ∣
      ∏ i : Fin k, (Nat.card K ^ k - Nat.card K ^ (i : ℕ)) := by
    have hd : ∏ i : Fin k, Nat.card K ^ (i : ℕ) ∣
        ∏ i : Fin k, (Nat.card K ^ k - Nat.card K ^ (i : ℕ)) := by
      refine Finset.prod_dvd_prod_of_dvd _ _ (fun i _ => ?_)
      exact Nat.dvd_sub (pow_dvd_pow _ i.2.le) dvd_rfl
    have he : ∏ i : Fin k, Nat.card K ^ (i : ℕ) = Nat.card K ^ (∑ i ∈ Finset.range k, i) := by
      rw [Finset.prod_pow_eq_pow_sum, Fin.sum_univ_eq_sum_range (fun i => i) k]
    rwa [he] at hd
  rw [← h3] at h4
  have hcop : Nat.Coprime ((Nat.card K) ^ (∑ i ∈ Finset.range k, i)) (Nat.card K - 1) := by
    apply Nat.Coprime.pow_left
    have hpos : 1 ≤ Nat.card K := Nat.card_pos
    obtain ⟨d, hd⟩ : ∃ d, Nat.card K = d + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hd, Nat.add_sub_cancel]
    have h' : Nat.Coprime (1 + d) d := Nat.coprime_add_self_left.mpr (Nat.coprime_one_left d)
    rwa [add_comm] at h'
  exact hcop.dvd_of_dvd_mul_right h4

end OrderForms

section Arith2

theorem orth_mul_pred_inj {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    (h : k * (k - 1) = m * (m - 1)) : k = m := by
  obtain ⟨a, rfl⟩ : ∃ a, k = a + 1 := ⟨k - 1, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h
  have : a = b := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h1 | h1 <;> nlinarith
  omega

theorem orth_omega_exp_eq {q : ℤ} (hq : Even q) (hq0 : q ≠ 0) {k m : ℕ} (hk : 1 ≤ k) (hm : 1 ≤ m)
    {X Y : ℤ} (hX : Odd X) (hY : Odd Y) (h : q ^ (k * (k - 1)) * X = q ^ (m * (m - 1)) * Y) :
    k = m :=
  orth_mul_pred_inj hk hm (orth_pow_mul_odd_inj hq hq0 hX hY h)

theorem orth_sp_exp_ne {q : ℤ} (hq : Even q) (hq0 : q ≠ 0) {k m : ℕ} (hm : 2 ≤ m)
    {X Y : ℤ} (hX : Odd X) (hY : Odd Y) (h : q ^ (k ^ 2) * X = q ^ (m * (m - 1)) * Y) :
    False := by
  have h1 := orth_pow_mul_odd_inj hq hq0 hX hY h
  obtain ⟨b, rfl⟩ : ∃ b, m = b + 1 := ⟨m - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1
  have hb : 1 ≤ b := by omega
  rcases le_or_gt k b with h2 | h2
  · nlinarith
  · nlinarith

theorem orth_sl_exp_false {q : ℕ} (hq : Even q) (hq0 : q ≠ 0) {m k : ℕ} (hm : 3 ≤ m)
    (hk : 2 * m ≤ k + 1) {Y : ℕ} {X : ℤ} (hX : Odd X)
    (hY : (Y : ℤ) = (q : ℤ) ^ (m * (m - 1)) * X)
    (hdvd : q ^ (∑ i ∈ Finset.range k, i) ∣ Y) : False := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  have hS := Finset.sum_range_id_mul_two (j + 1)
  simp only [Nat.add_sub_cancel] at hS
  set S := ∑ i ∈ Finset.range (j + 1), i with hSdef
  simp only [Nat.add_sub_cancel] at hY
  have h1 : (a + 1) * a + 1 ≤ S := by
    have h2 := Nat.mul_le_mul (show 2 * a + 1 ≤ j + 1 by omega) (show 2 * a ≤ j by omega)
    nlinarith
  obtain ⟨d, hd⟩ : ∃ d, S = (a + 1) * a + 1 + d := ⟨S - ((a + 1) * a + 1), by omega⟩
  have h3 : ((q : ℤ) ^ S) ∣ (Y : ℤ) := by exact_mod_cast hdvd
  rw [hY, hd, pow_add, pow_add, pow_one] at h3
  have h4 : (q : ℤ) ^ ((a + 1) * a) * ((q : ℤ) * (q : ℤ) ^ d) ∣ (q : ℤ) ^ ((a + 1) * a) * X := by
    rw [← mul_assoc]
    exact h3
  have h5 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hq0))).mp h4
  have h6 : (q : ℤ) ∣ X := (dvd_mul_right _ _).trans h5
  have h7 : (2 : ℤ) ∣ X := by
    obtain ⟨r, hr⟩ := hq
    have h2q : (2 : ℤ) ∣ (q : ℤ) := ⟨(r : ℤ), by exact_mod_cast (by omega : q = 2 * r)⟩
    exact dvd_trans h2q h6
  exact (Int.not_even_iff_odd.mpr hX) (even_iff_two_dvd.mpr h7)

end Arith2

section Sign

theorem orth_card_plus_ne_minus {K K' : Type} [Field K] [Finite K] [CharP K 2] [Field K']
    [Finite K'] [CharP K' 2] (hKK : Nat.card K' = Nat.card K) (hq : 4 ≤ Nat.card K) {m : ℕ}
    (hm : 3 ≤ m) {b c : K'} (hirr : ∀ s : K', s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(StatedOmega (StatedQuadPlus m K)) ≠
      Nat.card ↥(StatedOmega (StatedQuadMinus m K' b c)) := by
  intro h
  have h1 := card_statedOmega_plus_eq (K := K) hm
  have h2 := card_statedOmega_minus_eq_of_two_le (K := K') (m := m) (by omega) hirr
  rw [hKK] at h2
  have h3 : ((Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℕ) : ℤ) =
      ((Nat.card ↥(StatedOmega (StatedQuadMinus m K' b c)) : ℕ) : ℤ) := by rw [h]
  rw [h1, h2] at h3
  have hq0 : (1 : ℤ) < (Nat.card K : ℤ) := by exact_mod_cast (show 1 < Nat.card K by omega)
  have hP : 0 < ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    apply Finset.prod_pos
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have : (1 : ℤ) < (Nat.card K : ℤ) ^ (2 * i) := one_lt_pow₀ hq0 (by omega)
    omega
  have hpow : 0 < (Nat.card K : ℤ) ^ (m * (m - 1)) :=
    pow_pos (by omega : (0 : ℤ) < (Nat.card K : ℤ)) _
  have h4 := mul_right_cancel₀ hP.ne' h3
  have h5 := mul_left_cancel₀ hpow.ne' h4
  omega

end Sign

section Group

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem orth_eq_of_simple_quotient {R : Type} [Group R] {N₁ N₂ : Subgroup R} [N₁.Normal]
    [N₂.Normal] [IsSimpleGroup (R ⧸ N₁)] (h : N₁ ≤ N₂) (hne : N₂ ≠ ⊤) : N₂ = N₁ := by
  have hmap : (N₂.map (QuotientGroup.mk' N₁)).Normal :=
    Subgroup.Normal.map inferInstance (QuotientGroup.mk' N₁) (QuotientGroup.mk'_surjective N₁)
  haveI := hmap
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N₂.map (QuotientGroup.mk' N₁)) with h0 | h1
  · refine le_antisymm (fun x hx => ?_) h
    have : QuotientGroup.mk' N₁ x ∈ N₂.map (QuotientGroup.mk' N₁) := ⟨x, hx, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · exfalso
    apply hne
    rw [eq_top_iff]
    intro x _
    have : QuotientGroup.mk' N₁ x ∈ N₂.map (QuotientGroup.mk' N₁) := by rw [h1]; trivial
    obtain ⟨y, hy, hyx⟩ := this
    have hyn : y⁻¹ * x ∈ N₁ := QuotientGroup.eq.mp hyx
    have hx' : x = y * (y⁻¹ * x) := by group
    rw [hx']
    exact N₂.mul_mem hy (h hyn)

theorem orth_SL_dim_bound (h34 : Stroth34Statement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec5Hyp hc n t) (hNtCN : hc.CN t = Nt M (LB M Q B) t)
    (hNt : Nat.card ↥(Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = Nat.card Z) {k : ℕ} (hk : 2 ≤ k)
    (hnat : NaturalRep (ι := Fin k) K (StatedSL k K) (Rt M (LB M Q B) t)
      (Vt M (LB M Q B) B Z t) Z (hc.CN t)) : n ≤ k + 1 := by
  classical
  have h35all := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have hVQB : Vt M (LB M Q B) B Z t ≤ QB B :=
    stroth310SL_of_34 h34 G M Q Z B hc n t hs ⟨K, inferInstance, inferInstance, hK, k, hk, hnat⟩
  have hcardV := card_of_naturalRep hnat sec39_Z_le_Vt hK
  obtain ⟨n', γ, M₀, -, hglob⟩ := stroth_globalModelDataGF hc.hyp
  have hS : ∀ (c : GaloisField 2 n') (e : M₀.E), e ∈ M₀.img (Vt M (LB M Q B) B Z t) →
      c • e ∈ M₀.img (Vt M (LB M Q B) B Z t) :=
    fun c e he => hc.smul_mem_img_Vt hglob t c he
  obtain ⟨m', φ', hnorm', ψ', c', hker', hequiv', -, -, hSeq'⟩ :=
    exists_natural_data_of_subspace hc.hyp (hc.Vt_le_Q t) sec39_Z_le_Vt (hc.Rt_le_H0 t)
      (hc.Rt_normalizes_Vt hs.mem) (fun _ => Ctx.mem_CN (hc := hc)) hglob hS
  have hLRB : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  obtain ⟨b, hbV, hb0, hu0, hBb, hP1, hP2, hcount⟩ := hc.matrix_elation_data hs.width hs.n_gt
    hs.noA2 h35all.2.2.1 h35all.2.2.2 hglob (hc.B_le_Vt hs.mem) (le_inf (hc.Vt_le_Q t) hVQB) hS
    (hc.Rt_le_H0 t) (hc.Rt_normalizes_Vt hs.mem) hLRB φ' c' hSeq'
  have hT := hcount (LB M Q B ⊓ hc.CN t) (fun x => by
    rw [Subgroup.mem_inf, Ctx.mem_CN]
    constructor
    · rintro ⟨hx, -, hxv⟩
      exact ⟨hx, hxv⟩
    · rintro ⟨hx, hxv⟩
      exact ⟨hx, hLRB hx, hxv⟩)
  have hm'0 : m' ≠ 0 := by
    rintro rfl
    exact hu0 (Subsingleton.elim _ _)
  have hq : 2 ≤ Nat.card Z := by have := hc.hyp.q4; omega
  have hKg : Nat.card (GaloisField 2 n') = Nat.card Z := hglob.card
  haveI := hnorm'
  have hcardV' : Nat.card ↥(Vt M (LB M Q B) B Z t) = Nat.card Z * Nat.card Z ^ m' := by
    have hcardQ : Nat.card (↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t)) =
        Nat.card Z ^ m' := by
      rw [Nat.card_congr ψ'.toEquiv,
        show Nat.card (Multiplicative (Fin m' → GaloisField 2 n')) =
          Nat.card (Fin m' → GaloisField 2 n') from rfl,
        Nat.card_fun, hKg, Nat.card_eq_fintype_card (α := Fin m'), Fintype.card_fin]
    have hcardZ : Nat.card (Z.subgroupOf (Vt M (LB M Q B) B Z t)) = Nat.card Z :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe sec39_Z_le_Vt).toEquiv
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Z.subgroupOf (Vt M (LB M Q B) B Z t)), hcardQ, hcardZ, mul_comm]
  rw [hcardV'] at hcardV
  have hkm : k = m' := by
    have h1 : Nat.card Z * Nat.card Z ^ m' =
        Nat.card Z * Nat.card Z ^ Fintype.card (Fin k) := hcardV
    rw [Fintype.card_fin] at h1
    exact (Nat.pow_right_injective hq (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1)).symm
  have hcap : Nat.card ↥(LB M Q B ⊓ hc.CN t) ≤ Nat.card Q * Nat.card Z := by
    rw [← hNt, hNtCN]
    exact Nat.card_le_card_of_injective (Subgroup.inclusion inf_le_right)
      (Subgroup.inclusion_injective _)
  have hLB := h35all.2.2.1
  rw [hKg] at hT
  have h3 : Nat.card Q * Nat.card Z ^ (n - 1) ≤ Nat.card Q * Nat.card Z ^ m' := by
    calc Nat.card Q * Nat.card Z ^ (n - 1) = Nat.card ↥(LB M Q B ⊓ hc.CN t) *
          Nat.card Z ^ (m' - 1) := by rw [← hLB]; exact hT
      _ ≤ (Nat.card Q * Nat.card Z) * Nat.card Z ^ (m' - 1) := Nat.mul_le_mul_right _ hcap
      _ = Nat.card Q * Nat.card Z ^ m' := by
          obtain ⟨d, rfl⟩ : ∃ d, m' = d + 1 := ⟨m' - 1, by omega⟩
          simp [pow_succ]
          ring
  have h4 := Nat.le_of_mul_le_mul_left h3 Nat.card_pos
  have h5 := (Nat.pow_le_pow_iff_right hq).mp h4
  omega

theorem orth_natural_quotient (hc : Ctx M Q Z B) {t : G}
    (hNtCN : Nt M (LB M Q B) t ≤ hc.CN t) (hnotle : ¬ Rt M (LB M Q B) t ≤ hc.CN t)
    {Y : Type} [Group Y] [IsSimpleGroup Y]
    [hNn : ((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    (e : ↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) ≃* Y)
    {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : Subgroup (GL ι K)}
    (hnat : NaturalRep K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t)) :
    hc.CN t = Nt M (LB M Q B) t ∧ Nat.card ↥X = Nat.card Y := by
  obtain ⟨φ, hφr, hφk, -⟩ := hnat
  haveI : IsSimpleGroup (↥(Rt M (LB M Q B) t) ⧸
      (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) := e.isSimpleGroup
  haveI : φ.ker.Normal := φ.normal_ker
  have hle : (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) ≤ φ.ker := by
    rw [hφk]
    exact fun x hx => Subgroup.mem_subgroupOf.mpr (hNtCN (Subgroup.mem_subgroupOf.mp hx))
  have hne : φ.ker ≠ ⊤ := by
    rw [hφk]
    intro h
    exact hnotle (Subgroup.subgroupOf_eq_top.mp h)
  have heq : φ.ker = (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) :=
    orth_eq_of_simple_quotient hle hne
  refine ⟨?_, ?_⟩
  · have hCNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
    refine le_antisymm (fun x hx => ?_) hNtCN
    have hxR := hCNR hx
    have hmem : (⟨x, hxR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := by
      rw [hφk]
      exact Subgroup.mem_subgroupOf.mpr hx
    rw [heq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · rw [← hφr]
    calc Nat.card ↥φ.range = Nat.card (↥(Rt M (LB M Q B) t) ⧸ φ.ker) :=
          (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
      _ = Nat.card (↥(Rt M (LB M Q B) t) ⧸
            (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) :=
          Nat.card_congr (QuotientGroup.quotientMulEquivOfEq heq).toEquiv
      _ = Nat.card Y := Nat.card_congr e.toEquiv

theorem orth_e2_core (h34 : Stroth34Statement) (h310 : Stroth310Statement) (hc : Ctx M Q Z B)
    {n : ℕ} {t : G} (hs : Sec5Hyp hc n t)
    (hNt : Nat.card ↥(Nt M (LB M Q B) t) = Nat.card Q * Nat.card Z)
    {Y : Type} [Group Y] [IsSimpleGroup Y] (hY2 : ¬ IsPGroup 2 Y)
    [hNn : ((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    (e : ↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) ≃* Y) :
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (k : ℕ), Nat.card K = Nat.card Z ∧ 2 ≤ k ∧
        n ≤ k + 1 ∧ Nat.card ↥(StatedSL k K) = Nat.card Y) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (k : ℕ), Nat.card K = Nat.card Z ∧ 1 ≤ k ∧
        Nat.card ↥(StatedSp k K) = Nat.card Y) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (k : ℕ), Nat.card K = Nat.card Z ∧ 2 ≤ k ∧
        NaturalRep (ι := Fin k ⊕ Fin k) K (StatedOmega (StatedQuadPlus k K))
          (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) ∧
        Nat.card ↥(StatedOmega (StatedQuadPlus k K)) = Nat.card Y) ∨
    (∃ (K : Type) (_ : Field K) (_ : Finite K) (k : ℕ) (b c : K), Nat.card K = Nat.card Z ∧
        2 ≤ k ∧ (∀ s : K, s ^ 2 + b * s + c ≠ 0) ∧
        NaturalRep (ι := Fin (k - 1) ⊕ Fin (k - 1) ⊕ Fin 2) K
          (StatedOmega (StatedQuadMinus k K b c)) (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z
          (hc.CN t) ∧
        Nat.card ↥(StatedOmega (StatedQuadMinus k K b c)) = Nat.card Y) := by
  classical
  have h35all := stroth_3_5 h34 hc hs.width hs.n_gt hs.noA2 hs.gen
  have hRLB : Rt M (LB M Q B) t ≠ LB M Q B := by
    intro heq
    have hL : IsPGroup 2 ↥(LB M Q B) := Ctx.isPGroup_LB h34 hc hs.width hs.n_gt hs.noA2 hs.gen
    have hR2 : IsPGroup 2 ↥(Rt M (LB M Q B) t) := by rw [heq]; exact hL
    exact hY2 ((hR2.to_quotient _).of_equiv e)
  have hNtle : Nt M (LB M Q B) t ≤ hc.CN t := hc.Nt_le_CN h34 hs
  have hnotle : ¬ Rt M (LB M Q B) t ≤ hc.CN t := hc.not_Rt_le_CN h35all.2.1 hs.mem hRLB
  rcases h310 G M Q Z B hc n hs.width hs.n_gt hs.noA2 hs.gen t hs.mem hs.notQ with
    hRL | ⟨K, hF, hFin, hK, hfam⟩
  · exact absurd hRL hRLB
  rcases hfam with ⟨k, hk, hnat⟩ | ⟨k, hk, hnat⟩ | ⟨k, hk, hnat⟩ | ⟨k, b, c, hk, hirr, hnat⟩
  · obtain ⟨hCN, hcard⟩ := orth_natural_quotient hc hNtle hnotle e hnat
    exact Or.inl ⟨K, hF, hFin, k, hK, hk, orth_SL_dim_bound h34 hc hs hCN hNt hK hk hnat, hcard⟩
  · obtain ⟨-, hcard⟩ := orth_natural_quotient hc hNtle hnotle e hnat
    exact Or.inr (Or.inl ⟨K, hF, hFin, k, hK, hk, hcard⟩)
  · obtain ⟨-, hcard⟩ := orth_natural_quotient hc hNtle hnotle e hnat
    exact Or.inr (Or.inr (Or.inl ⟨K, hF, hFin, k, hK, hk, hnat, hcard⟩))
  · obtain ⟨-, hcard⟩ := orth_natural_quotient hc hNtle hnotle e hnat
    exact Or.inr (Or.inr (Or.inr ⟨K, hF, hFin, k, b, c, hK, hk, hirr, hnat, hcard⟩))

theorem orth_not_pgroup_of_dvd {Y : Type} [Group Y] [Finite Y] {q : ℕ} (hq : Even q)
    (hq1 : 2 ≤ q)
    (hodd : ∀ p : ℕ, p.Prime → p ∣ q ^ 2 + 1 → p ∣ Nat.card Y) : ¬ IsPGroup 2 Y := by
  intro h2
  obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := 2)).mp h2
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd
    (show q ^ 2 + 1 ≠ 1 by have : 0 < q ^ 2 := by positivity
                           omega)
  have h1 := hodd p hp hpd
  rw [hj] at h1
  have hp2 : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  subst hp2
  have h3 : Even (q ^ 2 + 1) := even_iff_two_dvd.mpr hpd
  have h4 : Even (q ^ 2) := (Nat.even_pow.mpr ⟨hq, two_ne_zero⟩)
  exact (Nat.even_add_one.mp h3) h4

theorem orth_e2Natural_plus (h34 : Stroth34Statement) (h310 : Stroth310Statement) (hc : Ctx M Q Z B)
    {t : G} {m : ℕ} (hs : Sec5Hyp hc (2 * m) t) (hm : 3 ≤ m) (hE : CaseE2Plus M Q Z B t m) :
    OmegaPlusNat hc t m := by
  classical
  obtain ⟨-, -, hNt, ⟨hNn, KE, hFE, hFinE, hKE, ⟨e⟩⟩, -⟩ := hE
  haveI := hNn
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP KE 2 := charP_two_of_card_eq_two_pow (hKE.trans hZ2)
  have hq4 : 4 ≤ Nat.card KE := by rw [hKE]; exact hc.hyp.q4
  obtain ⟨hsimple, -, hodd⟩ := endg_omegaPlus_facts hq4 hm
  haveI := hsimple
  have hqe : Even (Nat.card KE) := orth_even_card KE
  have hY2 : ¬ IsPGroup 2 ↥(StatedOmega (StatedQuadPlus m KE)) :=
    orth_not_pgroup_of_dvd hqe (by omega) hodd
  have hcore := orth_e2_core h34 h310 hc hs hNt hY2 e
  have hqZ : Even (Nat.card Z : ℤ) := by
    rw [← hKE]; exact orth_even_card_int KE
  have hq0 : (Nat.card Z : ℤ) ≠ 0 := by have := hc.hyp.q4; omega
  obtain ⟨XE, hXE, hYE⟩ := orth_card_omegaPlus_form hq4 (show 2 ≤ m by omega)
  rw [hKE] at hYE
  rcases hcore with ⟨K, fK, finK, k, hKq, hk, hdim, hcard⟩ | ⟨K, fK, finK, k, hKq, hk, hcard⟩ |
    ⟨K, fK, finK, k, hKq, hk, hnat, hcard⟩ | ⟨K, fK, finK, k, b, c, hKq, hk, hirr, hnat, hcard⟩
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    refine orth_sl_exp_false (q := Nat.card Z) ?_ (by have := hc.hyp.q4; omega) hm hdim
      (Y := Nat.card ↥(StatedOmega (StatedQuadPlus m KE))) hXE ?_ ?_
    · rw [← hKE]; exact orth_even_card KE
    · exact_mod_cast hYE
    · rw [← hcard, ← hKq]
      exact orth_dvd_card_statedSL (by omega)
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    obtain ⟨X', hX', hY'⟩ := orth_card_sp_form (K := K) k
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedSp k K) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadPlus m KE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    exact orth_sp_exp_ne hqZ hq0 (by omega) hX' hXE h1
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    have hq4K : 4 ≤ Nat.card K := by rw [hKq]; exact hc.hyp.q4
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaPlus_form hq4K hk
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadPlus k K)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadPlus m KE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = m := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact ⟨K, fK, finK, hKq, hnat⟩
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaMinus_form (K := K) hk hirr
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadMinus k K b c)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadPlus m KE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = m := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact orth_card_plus_ne_minus (K := KE) (K' := K) (hKq.trans hKE.symm) hq4 hm hirr hcard.symm

theorem orth_e2Natural_minus (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hc : Ctx M Q Z B) {t : G} {m : ℕ} (hs : Sec5Hyp hc (2 * m) t) (hm : 3 ≤ m)
    (hE : CaseE2Minus M Q Z B t m) :
    OmegaMinusNat hc t m := by
  classical
  obtain ⟨-, -, hNt, ⟨hNn, KE, hFE, hFinE, hKE, bE, cE, hirrE, ⟨e⟩⟩, -⟩ := hE
  haveI := hNn
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP KE 2 := charP_two_of_card_eq_two_pow (hKE.trans hZ2)
  have hq4 : 4 ≤ Nat.card KE := by rw [hKE]; exact hc.hyp.q4
  obtain ⟨hsimple, -, hodd⟩ := endg_omegaMinus_facts hq4 (show 2 ≤ m by omega) hirrE
  haveI := hsimple
  have hqe : Even (Nat.card KE) := orth_even_card KE
  have hY2 : ¬ IsPGroup 2 ↥(StatedOmega (StatedQuadMinus m KE bE cE)) :=
    orth_not_pgroup_of_dvd hqe (by omega) hodd
  have hcore := orth_e2_core h34 h310 hc hs hNt hY2 e
  have hqZ : Even (Nat.card Z : ℤ) := by
    rw [← hKE]; exact orth_even_card_int KE
  have hq0 : (Nat.card Z : ℤ) ≠ 0 := by have := hc.hyp.q4; omega
  obtain ⟨XE, hXE, hYE⟩ := orth_card_omegaMinus_form (K := KE) (show 2 ≤ m by omega) hirrE
  rw [hKE] at hYE
  rcases hcore with ⟨K, fK, finK, k, hKq, hk, hdim, hcard⟩ | ⟨K, fK, finK, k, hKq, hk, hcard⟩ |
    ⟨K, fK, finK, k, hKq, hk, hnat, hcard⟩ | ⟨K, fK, finK, k, b, c, hKq, hk, hirr, hnat, hcard⟩
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    refine orth_sl_exp_false (q := Nat.card Z) ?_ (by have := hc.hyp.q4; omega) hm hdim
      (Y := Nat.card ↥(StatedOmega (StatedQuadMinus m KE bE cE))) hXE ?_ ?_
    · rw [← hKE]; exact orth_even_card KE
    · exact_mod_cast hYE
    · rw [← hcard, ← hKq]
      exact orth_dvd_card_statedSL (by omega)
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    obtain ⟨X', hX', hY'⟩ := orth_card_sp_form (K := K) k
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedSp k K) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus m KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    exact orth_sp_exp_ne hqZ hq0 (by omega) hX' hXE h1
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    have hq4K : 4 ≤ Nat.card K := by rw [hKq]; exact hc.hyp.q4
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaPlus_form hq4K hk
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadPlus k K)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus m KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = m := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact orth_card_plus_ne_minus (K := K) (K' := KE) (hKE.trans hKq.symm) hq4K hm hirrE hcard
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaMinus_form (K := K) hk hirr
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadMinus k K b c)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus m KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = m := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact ⟨K, fK, finK, hKq, b, c, hirr, hnat⟩

end Group

end CFSG.RankThree.GF2n.Smith81
