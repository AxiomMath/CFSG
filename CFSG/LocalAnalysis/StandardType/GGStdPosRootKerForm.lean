module

public import CFSG.Timmesfeld.ARS.CaseEWeight
public import CFSG.LocalAnalysis.StandardType.GGSimplyLacedWeyl

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.Timmesfeld.ARS

private theorem ggRootKer_cartanPair_add_left {I : Type} [Fintype I] (A : Matrix I I ℤ)
    (u v w : I → ℤ) : cartanPair A (u + v) w = cartanPair A u w + cartanPair A v w := by
  simp only [cartanPair, map_add, mul_add, Finset.sum_add_distrib]

theorem ggRootKer_cartanPair_add_right {I : Type} [Fintype I] (A : Matrix I I ℤ)
    (u v w : I → ℤ) : cartanPair A u (v + w) = cartanPair A u v + cartanPair A u w := by
  simp only [cartanPair, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem ggRootKer_cartanPair_sub_left {I : Type} [Fintype I] (A : Matrix I I ℤ)
    (u v w : I → ℤ) : cartanPair A (u - v) w = cartanPair A u w - cartanPair A v w := by
  simp only [cartanPair, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem ggRootKer_cartanPair_sub_right {I : Type} [Fintype I] (A : Matrix I I ℤ)
    (u v w : I → ℤ) : cartanPair A u (v - w) = cartanPair A u v - cartanPair A u w := by
  simp only [cartanPair, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem ggRootKer_cartanPair_smul_left {I : Type} [Fintype I] (A : Matrix I I ℤ) (c : ℤ)
    (u w : I → ℤ) : cartanPair A (c • u) w = c * cartanPair A u w := by
  simp only [cartanPair, map_zsmul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem ggRootKer_cartanPair_smul_right {I : Type} [Fintype I] (A : Matrix I I ℤ) (c : ℤ)
    (u w : I → ℤ) : cartanPair A u (c • w) = c * cartanPair A u w := by
  simp only [cartanPair, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private theorem ggRootKer_prime_dvd_cases {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {c : ℤ}
    (h1 : -2 ≤ c) (h2 : c ≤ 1) (h : (p : ℤ) ∣ c - 2) : p = 3 ∧ c = -1 := by
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hp3' : (3 : ℤ) ≤ p := by exact_mod_cast hp3
  obtain ⟨t, ht⟩ := h
  have ht1 : t = -1 := by
    rcases lt_trichotomy t (-1) with h | h | h
    · nlinarith
    · exact h
    · nlinarith
  subst ht1
  have hp4 : p ≤ 4 := by omega
  interval_cases p
  · omega
  · exact absurd hp (by norm_num)

private theorem ggRootKer_a2_pair_ne_zero :
    ∀ P ∈ ([(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)] : List (ℤ × ℤ)),
      ∀ Q ∈ ([(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)] : List (ℤ × ℤ)),
        2 * P.1 * Q.1 - (P.1 * Q.2 + P.2 * Q.1) + 2 * P.2 * Q.2 ≠ 0 := by
  decide

private theorem ggRootKer_exists_coroot_not_dvd {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I ℤ} (hA : TauCeti.IsFiniteType A) (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hA)) (h3 : 3 ≤ Fintype.card I)
    {a b : I → ℤ} (ha : a ∈ roots hA ∅) (hb : b ∈ roots hA ∅) (hab : cartanPair A a b = -1) :
    ∃ l, ¬ (3 : ℤ) ∣ coroot A l (a - b) := by
  by_contra hcon
  push Not at hcon
  have hsymm := cartan_symm_of_posDef hpd
  have hqa : cartanPair A a a = 2 := cartanForm_eq_two hA hsymm ha
  have hqb : cartanPair A b b = 2 := cartanForm_eq_two hA hsymm hb
  have hba : cartanPair A b a = -1 := by rw [cartanPair_comm hsymm]; exact hab
  have hsl : ∀ (k : I) (v : I → ℤ), cartanPair A (Pi.single k 1) v = coroot A k v :=
    fun k v => by rw [cartanPair_comm hsymm, cartanPair_single]
  set L : List (ℤ × ℤ) := [(1, 0), (-1, 0), (0, 1), (0, -1), (1, 1), (-1, -1)] with hL
  have hnode : ∀ k, (coroot A k a = 0 ∧ coroot A k b = 0) ∨
      ∃ P ∈ L, (Pi.single k 1 : I → ℤ) = P.1 • a + P.2 • b := by
    intro k
    by_cases h1 : a = Pi.single k 1
    · exact Or.inr ⟨(1, 0), by simp [hL], by rw [h1]; simp⟩
    by_cases h2 : a = -Pi.single k 1
    · exact Or.inr ⟨(-1, 0), by simp [hL], by rw [h2]; simp⟩
    by_cases h3' : b = Pi.single k 1
    · exact Or.inr ⟨(0, 1), by simp [hL], by rw [h3']; simp⟩
    by_cases h4 : b = -Pi.single k 1
    · exact Or.inr ⟨(0, -1), by simp [hL], by rw [h4]; simp⟩
    have ha1 := coroot_le_one hA hpd ha h1
    have ha2 := neg_one_le_coroot hA hpd ha h2
    have hb1 := coroot_le_one hA hpd hb h3'
    have hb2 := neg_one_le_coroot hA hpd hb h4
    have hd := hcon k
    rw [map_sub] at hd
    have hxy : coroot A k a = coroot A k b := by omega
    have hkk : A k k = 2 := hA.apply_self k
    rcases (by omega : coroot A k a = 0 ∨ coroot A k a = 1 ∨ coroot A k a = -1) with h0 | h0 | h0
    · exact Or.inl ⟨h0, hxy ▸ h0⟩
    all_goals
      refine Or.inr ⟨(coroot A k a, coroot A k a), by simp [hL, h0], ?_⟩
      refine sub_eq_zero.mp (by_contra fun hne => ?_)
      have hpos := cartanForm_pos hpd hne
      rw [← cartanPair_self] at hpos
      simp only [ggRootKer_cartanPair_sub_left, ggRootKer_cartanPair_sub_right,
        ggRootKer_cartanPair_add_left, ggRootKer_cartanPair_add_right,
        ggRootKer_cartanPair_smul_left, ggRootKer_cartanPair_smul_right, hsl, cartanPair_single,
        coroot_single, map_sub, map_add, map_zsmul, smul_eq_mul] at hpos
      rw [← hxy, h0] at hpos
      linarith
  have hedge : ∀ c d, (coxeterMatrix hA).M c d = 3 →
      (∃ P ∈ L, (Pi.single c 1 : I → ℤ) = P.1 • a + P.2 • b) →
        ∃ P ∈ L, (Pi.single d 1 : I → ℤ) = P.1 • a + P.2 • b := by
    rintro c d hcd ⟨P, -, hc⟩
    refine (hnode d).resolve_left fun ⟨hda, hdb⟩ => ?_
    have hdc : A d c = 0 := by
      rw [← coroot_single A d c, hc, map_add, map_zsmul, map_zsmul, hda, hdb, smul_zero,
        smul_zero, add_zero]
    simp only [coxeterMatrix, TauCeti.coxeterMatrixOfCartanMatrix_apply, hdc, mul_zero,
      TauCeti.coxeterOrder_zero] at hcd
    omega
  obtain ⟨k₀, hk₀⟩ : ∃ k, ∃ P ∈ L, (Pi.single k 1 : I → ℤ) = P.1 • a + P.2 • b := by
    by_contra hnone
    have hall : ∀ k, coroot A k a = 0 := fun k =>
      ((hnode k).resolve_right fun h => hnone ⟨k, h⟩).1
    have h0 : cartanPair A a a = 0 := by simp [cartanPair, hall]
    omega
  have hall : ∀ j, ∃ P ∈ L, (Pi.single j 1 : I → ℤ) = P.1 • a + P.2 • b := by
    intro j
    induction hconn.2 k₀ j with
    | refl => exact hk₀
    | tail _ hstep ih => exact hedge _ _ hstep ih
  have hjoin : ∀ x y, x ≠ y → A x y = -1 := by
    intro x y hxy
    obtain ⟨P, hP, hx⟩ := hall x
    obtain ⟨Q, hQ, hy⟩ := hall y
    have hval : A x y = 2 * Q.1 * P.1 - (Q.1 * P.2 + Q.2 * P.1) + 2 * Q.2 * P.2 := by
      rw [← coroot_single A x y, ← cartanPair_single, hx, hy]
      simp only [ggRootKer_cartanPair_add_left, ggRootKer_cartanPair_add_right,
        ggRootKer_cartanPair_smul_left, ggRootKer_cartanPair_smul_right, hqa, hqb, hab, hba]
      ring
    have hne : A x y ≠ 0 := hval ▸ ggRootKer_a2_pair_ne_zero Q hQ P hP
    have hle := hA.apply_le_zero_of_ne hxy
    have hmem := hA.apply_mul_apply_mem_of_ne hxy
    rw [← hsymm x y] at hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    have hm1 : -1 ≤ A x y := by rcases hmem with h | h | h | h <;> nlinarith
    omega
  obtain ⟨i, j, l, hij, hil, hjl⟩ := (Fintype.two_lt_card_iff (α := I)).mp (by omega)
  have hv : (Pi.single i 1 + Pi.single j 1 + Pi.single l 1 : I → ℤ) ≠ 0 := by
    intro h
    have := congrFun h i
    simp [Pi.single_apply, hij.symm, hil.symm] at this
  have hpos := cartanForm_pos hpd hv
  rw [← cartanPair_self] at hpos
  simp only [ggRootKer_cartanPair_add_left, ggRootKer_cartanPair_add_right, cartanPair_single,
    coroot_single, map_add] at hpos
  linarith [hA.apply_self i, hA.apply_self j, hA.apply_self l, hjoin i j hij, hjoin j i hij.symm,
    hjoin i l hil, hjoin l i hil.symm, hjoin j l hjl, hjoin l j hjl.symm]

theorem ggRootKer_eq_of_rad {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef)
    (hconn : GGSimplyLacedConnected (coxeterMatrix hA)) (h3 : 3 ≤ Fintype.card I) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {β β' : I → ℤ} (hβ : β ∈ roots hA ∅) (hβ' : β' ∈ roots hA ∅)
    (h : ∀ l, (p : ℤ) ∣ coroot A l (β' - β)) : β' = β := by
  have hsymm := cartan_symm_of_posDef hpd
  have hq : cartanPair A β β = 2 := cartanForm_eq_two hA hsymm hβ
  have hq' : cartanPair A β' β' = 2 := cartanForm_eq_two hA hsymm hβ'
  have hc : cartanPair A β β' = cartanPair A β' β := cartanPair_comm hsymm _ _
  by_contra hne
  have hle : cartanPair A β' β ≤ 1 := by
    have := cartanForm_pos hpd (sub_ne_zero.mpr hne)
    rw [← cartanPair_self] at this
    simp only [ggRootKer_cartanPair_sub_left, ggRootKer_cartanPair_sub_right] at this
    linarith
  have hge : -2 ≤ cartanPair A β' β := by
    by_cases h0 : β' + β = 0
    · rw [eq_neg_of_add_eq_zero_left h0, ← neg_one_smul ℤ β, ggRootKer_cartanPair_smul_left]
      linarith
    · have := cartanForm_pos hpd h0
      rw [← cartanPair_self] at this
      simp only [ggRootKer_cartanPair_add_left, ggRootKer_cartanPair_add_right] at this
      linarith
  have hdvd : (p : ℤ) ∣ cartanPair A β' β - 2 := by
    rw [← hq, ← ggRootKer_cartanPair_sub_left]
    exact Finset.dvd_sum fun k _ => dvd_mul_of_dvd_right (h k) _
  obtain ⟨rfl, hc1⟩ := ggRootKer_prime_dvd_cases hp hp2 hge hle hdvd
  obtain ⟨l, hl⟩ := ggRootKer_exists_coroot_not_dvd hA hpd hconn h3 hβ' hβ hc1
  exact hl (by exact_mod_cast h l)

end CFSG.StandardType

end
