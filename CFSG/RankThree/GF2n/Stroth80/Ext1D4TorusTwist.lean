module

public import CFSG.RankThree.GF2n.Stroth80.Ext1D4Torus

public section

namespace CFSG.RankThree.GF2n.Stroth80.Ext1D4

@[expose] def IsGoodVal8 (x : ℤ) : Prop := x ≠ 0 ∧ x % 7 ≠ 0 ∧ |x| ≤ 14

instance : DecidablePred IsGoodVal8 := fun x => by unfold IsGoodVal8; infer_instance

abbrev IsMinWt (W : Finset (Fin 4 → ℤ)) : Prop := W = natWt ∨ W = evenWt ∨ W = oddWt

theorem sep_same_twist {W : Finset (Fin 4 → ℤ)} (hW : IsMinWt W) {a b : ℕ}
    (hab : (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1)) :
    ∀ β ∈ posRoot, ∀ ψ ∈ W, ∀ χ ∈ W,
      ∃ e ∈ testVec, dot4 β e = 0 ∧ IsGoodVal8 (dot4 ((2 : ℤ) ^ a • ψ - (2 : ℤ) ^ b • χ) e) := by
  rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hW with rfl | rfl | rfl <;> decide +kernel

theorem sep_nonzero {W₁ W₂ : Finset (Fin 4 → ℤ)} (hW₁ : IsMinWt W₁) (hW₂ : IsMinWt W₂) :
    ∀ β ∈ posRoot, ∀ ψ ∈ W₁, ∀ χ ∈ W₂, ∃ e ∈ testVec, dot4 β e = 0 ∧
      (dot4 ψ e ≠ 0 ∨ dot4 χ e ≠ 0) ∧ |dot4 ψ e| ≤ 2 ∧ |dot4 χ e| ≤ 2 := by
  rcases hW₁ with rfl | rfl | rfl <;> rcases hW₂ with rfl | rfl | rfl <;> decide +kernel

section Field

variable {K : Type*} [Field K] [Fintype K] [CharP K 2]

theorem coprime_card_sub_one_two_pow {f : ℕ} (hf : Fintype.card K = 2 ^ f) (hf1 : 1 ≤ f)
    (n : ℕ) : IsCoprime ((Fintype.card K - 1 : ℕ) : ℤ) ((2 : ℤ) ^ n) := by
  have hodd : Odd (Fintype.card K - 1) := by
    rw [hf]
    exact Nat.Even.sub_odd Nat.one_le_two_pow (by rw [Nat.even_pow]; exact ⟨even_two, by omega⟩)
      odd_one
  rw [show (2 : ℤ) ^ n = ((2 ^ n : ℕ) : ℤ) by push_cast; rfl, Nat.isCoprime_iff_coprime]
  exact Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 hodd)

theorem dvd_of_dvd_mul_half {f m : ℕ} (hf : Fintype.card K = 2 ^ f) (hf1 : 1 ≤ f)
    (hm : 2 * m = Fintype.card K) {x : ℤ} (h : ((Fintype.card K - 1 : ℕ) : ℤ) ∣ x * m) :
    ((Fintype.card K - 1 : ℕ) : ℤ) ∣ x := by
  have hm' : (m : ℤ) = (2 : ℤ) ^ (f - 1) := by
    have : m = 2 ^ (f - 1) := by
      have h2 : 2 ^ f = 2 * 2 ^ (f - 1) := by rw [← pow_succ']; congr 1; omega
      omega
    rw [this]
    push_cast
    rfl
  rw [hm'] at h
  exact (coprime_card_sub_one_two_pow hf hf1 (f - 1)).dvd_of_dvd_mul_right h

theorem zpow_ne_one_of_isGoodVal8 {g : Kˣ} (hg : orderOf g = Fintype.card K - 1) {m : ℕ}
    (hm : 2 * m = Fintype.card K) (hq : 8 ≤ Fintype.card K) {x : ℤ} (hx : IsGoodVal8 x) (k : ℕ) :
    g ^ ((2 : ℤ) ^ k * (x * m)) ≠ 1 := by
  intro h
  rw [← orderOf_dvd_iff_zpow_eq_one, hg] at h
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hf3 : 3 ≤ (f : ℕ) := by
    by_contra hlt
    have : 2 ^ (f : ℕ) ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h1 : ((Fintype.card K - 1 : ℕ) : ℤ) ∣ (2 : ℤ) ^ k * x :=
    dvd_of_dvd_mul_half hf (by omega) hm (by rwa [mul_assoc])
  have hdvd := (coprime_card_sub_one_two_pow hf (by omega) k).dvd_of_dvd_mul_left h1
  obtain ⟨hx0, hx7, hx14⟩ := hx
  have hq1 : Fintype.card K - 1 = 2 ^ (f : ℕ) - 1 := by rw [hf]
  rcases Nat.lt_or_ge (f : ℕ) 4 with hlt | hge
  · have hf3' : (f : ℕ) = 3 := by omega
    rw [hq1, hf3'] at hdvd
    exact hx7 (Int.emod_eq_zero_of_dvd (by exact_mod_cast hdvd))
  · have h15 : 15 ≤ Fintype.card K - 1 := by
      rw [hq1]
      have : 2 ^ 4 ≤ 2 ^ (f : ℕ) := Nat.pow_le_pow_right (by norm_num) hge
      omega
    refine hx0 (Int.eq_zero_of_abs_lt_dvd hdvd ?_)
    have : (15 : ℤ) ≤ ((Fintype.card K - 1 : ℕ) : ℤ) := by exact_mod_cast h15
    linarith

theorem zpow_ne_one_of_mid {g : Kˣ} (hg : orderOf g = Fintype.card K - 1) {f m : ℕ}
    (hf : Fintype.card K = 2 ^ f) (hm : 2 * m = Fintype.card K) {a : ℕ} (ha : 2 ≤ a)
    (haf : a + 2 ≤ f) {u v : ℤ} (huv : u ≠ 0 ∨ v ≠ 0) (hu : |u| ≤ 2) (hv : |v| ≤ 2) :
    g ^ (((2 : ℤ) ^ a * u - v) * m) ≠ 1 := by
  intro h
  rw [← orderOf_dvd_iff_zpow_eq_one, hg] at h
  have hdvd := dvd_of_dvd_mul_half hf (by omega) hm h
  have h4 : (4 : ℤ) ≤ (2 : ℤ) ^ a := by
    have : (2 : ℤ) ^ 2 ≤ (2 : ℤ) ^ a := pow_le_pow_right₀ (by norm_num) ha
    linarith
  have h4a : 4 * (2 : ℤ) ^ a ≤ (2 : ℤ) ^ f := by
    have : (2 : ℤ) ^ (a + 2) ≤ (2 : ℤ) ^ f := pow_le_pow_right₀ (by norm_num) haf
    rw [pow_add] at this
    linarith
  have hP16 : (16 : ℤ) ≤ (2 : ℤ) ^ f := by
    have : (2 : ℤ) ^ 4 ≤ (2 : ℤ) ^ f := pow_le_pow_right₀ (by norm_num) (by omega)
    linarith
  have hq1 : ((Fintype.card K - 1 : ℕ) : ℤ) = (2 : ℤ) ^ f - 1 := by
    rw [hf, Nat.cast_sub Nat.one_le_two_pow]
    push_cast
    rfl
  have hau : |(2 : ℤ) ^ a * u| ≤ 2 * (2 : ℤ) ^ a := by
    rw [abs_mul, abs_of_pos (by positivity)]
    nlinarith [abs_nonneg u]
  have hlt : |(2 : ℤ) ^ a * u - v| < ((Fintype.card K - 1 : ℕ) : ℤ) := by
    have := abs_sub ((2 : ℤ) ^ a * u) v
    rw [hq1]
    linarith
  have h0 := Int.eq_zero_of_abs_lt_dvd hdvd hlt
  have hveq : v = (2 : ℤ) ^ a * u := by linarith
  by_cases hu0 : u = 0
  · rw [hu0, mul_zero] at hveq
    rcases huv with h | h
    · exact h hu0
    · exact h hveq
  · have h1 : 1 ≤ |u| := Int.one_le_abs hu0
    have h2 : |v| = (2 : ℤ) ^ a * |u| := by rw [hveq, abs_mul, abs_of_pos (by positivity)]
    nlinarith

theorem wtChar_succ (m k : ℕ) (v : Fin 4 → ℤ) (z : Fin 4 → Kˣ) :
    wtChar m (k + 1) v z = wtChar m k v z ^ 2 := by
  rw [wtChar, wtChar, pow_succ, pow_mul]

theorem wtChar_card {f : ℕ} (hf : Fintype.card K = 2 ^ f) (m : ℕ) (v : Fin 4 → ℤ)
    (z : Fin 4 → Kˣ) : wtChar m f v z = wtChar m 0 v z := by
  rw [wtChar, wtChar, pow_zero, pow_one, ← hf]
  exact Units.ext (by rw [Units.val_pow_eq_pow_val, FiniteField.pow_card])

theorem wtChar_zpow_eq_iff (m a : ℕ) (ψ χ e : Fin 4 → ℤ) (g : Kˣ) :
    wtChar m a ψ (fun i => g ^ e i) = wtChar m 0 χ (fun i => g ^ e i) →
      g ^ (((2 : ℤ) ^ a * dot4 ψ e - dot4 χ e) * m) = 1 := by
  intro h
  rw [wtChar_zpow, wtChar_zpow] at h
  rw [sub_mul, zpow_sub, mul_assoc, h, pow_zero, one_mul, mul_inv_cancel]

theorem isMinWt_cases {W₁ W₂ : Finset (Fin 4 → ℤ)} (hW₁ : IsMinWt W₁) (hW₂ : IsMinWt W₂)
    (hne : W₁ ≠ W₂) :
    (W₁ = natWt ∧ W₂ = evenWt) ∨ (W₁ = natWt ∧ W₂ = oddWt) ∨
      (W₁ = evenWt ∧ W₂ = natWt) ∨ (W₁ = evenWt ∧ W₂ = oddWt) ∨
      (W₁ = oddWt ∧ W₂ = natWt) ∨ (W₁ = oddWt ∧ W₂ = evenWt) := by
  rcases hW₁ with rfl | rfl | rfl <;> rcases hW₂ with rfl | rfl | rfl <;> simp_all

theorem torusSep_twist {f m : ℕ} (hf : Fintype.card K = 2 ^ f) (hm : 2 * m = Fintype.card K)
    (hq : 4 ≤ Fintype.card K) {W₁ W₂ : Finset (Fin 4 → ℤ)} (hW₁ : IsMinWt W₁)
    (hW₂ : IsMinWt W₂) {a : ℕ} (ha : a < f) (hne : W₁ = W₂ → a ≠ 0 ∧ 8 ≤ Fintype.card K) :
    ∀ β ∈ posRoot, ∀ (ψ : W₁) (χ : W₂), ∃ z : Fin 4 → Kˣ, wtChar m 0 β z = 1 ∧
      wtChar m a (ψ : Fin 4 → ℤ) z ≠ wtChar m 0 (χ : Fin 4 → ℤ) z := by
  intro β hβ ψ χ
  obtain ⟨g, hg⟩ := exists_orderOf_eq_card_sub_one (K := K)
  have hroot : ∀ e, dot4 β e = 0 → wtChar m 0 β (fun i => g ^ e i) = 1 := fun e he => by
    rw [wtChar_zpow, he, zero_mul, mul_zero, zpow_zero]
  have hfrob : a + 1 = f → (∀ z : Fin 4 → Kˣ, wtChar m 0 (ψ : Fin 4 → ℤ) z ≠
      wtChar m 1 (χ : Fin 4 → ℤ) z → wtChar m a (ψ : Fin 4 → ℤ) z ≠
        wtChar m 0 (χ : Fin 4 → ℤ) z) := by
    intro haf z h heq
    apply h
    rw [← wtChar_card hf, ← haf, wtChar_succ, heq, ← wtChar_succ]
  by_cases hW : W₁ = W₂
  · obtain ⟨ha0, hq8⟩ := hne hW
    subst hW
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    ·
      have ha1 : a = 1 := by omega
      subst ha1
      obtain ⟨e, -, he0, hgood⟩ := sep_same_twist hW₁ (Or.inl ⟨rfl, rfl⟩) β hβ ψ ψ.2 χ χ.2
      refine ⟨fun i => g ^ e i, hroot e he0, fun heq => ?_⟩
      have := wtChar_zpow_eq_iff m 1 ψ χ e g heq
      apply zpow_ne_one_of_isGoodVal8 hg hm hq8 hgood 0
      convert this using 2
      rw [dot4_sub, dot4_smul, dot4_smul]
      ring
    · rcases Nat.lt_or_ge (a + 1) f with hlt | hge
      · obtain ⟨e, -, he0, huv, hu, hv⟩ := sep_nonzero hW₁ hW₁ β hβ ψ ψ.2 χ χ.2
        exact ⟨fun i => g ^ e i, hroot e he0, fun heq =>
          zpow_ne_one_of_mid hg hf hm ha2 (by omega) huv hu hv
            (wtChar_zpow_eq_iff m a ψ χ e g heq)⟩
      · obtain ⟨e, -, he0, hgood⟩ := sep_same_twist hW₁ (Or.inr ⟨rfl, rfl⟩) β hβ ψ ψ.2 χ χ.2
        refine ⟨fun i => g ^ e i, hroot e he0, hfrob (by omega) _ fun heq => ?_⟩
        rw [wtChar_zpow, wtChar_zpow] at heq
        apply zpow_ne_one_of_isGoodVal8 hg hm hq8 hgood 0
        have hx : (2 : ℤ) ^ 0 *
            (dot4 ((2 : ℤ) ^ 0 • (ψ : Fin 4 → ℤ) - (2 : ℤ) ^ 1 • (χ : Fin 4 → ℤ)) e * m) =
              (2 : ℤ) ^ 0 * (dot4 ψ e * m) - (2 : ℤ) ^ 1 * (dot4 χ e * m) := by
          rw [dot4_sub, dot4_smul, dot4_smul]
          ring
        rw [hx, zpow_sub, heq, mul_inv_cancel]
  · have hcases := isMinWt_cases hW₁ hW₂ hW
    rcases Nat.lt_or_ge a 2 with ha2 | ha2
    · interval_cases a
      · exact torusSep_mixed hm hq hcases (le_refl _ |>.trans zero_le_one) zero_le_one β hβ ψ χ
      · exact torusSep_mixed hm hq hcases le_rfl zero_le_one β hβ ψ χ
    · rcases Nat.lt_or_ge (a + 1) f with hlt | hge
      · obtain ⟨e, -, he0, huv, hu, hv⟩ := sep_nonzero hW₁ hW₂ β hβ ψ ψ.2 χ χ.2
        exact ⟨fun i => g ^ e i, hroot e he0, fun heq =>
          zpow_ne_one_of_mid hg hf hm ha2 (by omega) huv hu hv
            (wtChar_zpow_eq_iff m a ψ χ e g heq)⟩
      · obtain ⟨z, hz1, hz2⟩ := torusSep_mixed hm hq hcases zero_le_one le_rfl β hβ ψ χ
        exact ⟨z, hz1, hfrob (by omega) z hz2⟩

end Field

end CFSG.RankThree.GF2n.Stroth80.Ext1D4
