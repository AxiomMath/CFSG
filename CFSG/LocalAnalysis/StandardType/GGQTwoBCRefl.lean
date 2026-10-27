module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2x_sq (x : ZMod 3) (hx : x ≠ 0) : x * x = 1 := by
  have h : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide
  exact h x hx

private lemma ggQ2x_inv_eq_self (x : ZMod 3) (hx : x ≠ 0) : x⁻¹ = x := by
  have hxx : x * x = 1 := ggQ2x_sq x hx
  calc x⁻¹ = x⁻¹ * 1 := (mul_one _).symm
    _ = x⁻¹ * (x * x) := by rw [hxx]
    _ = (x⁻¹ * x) * x := by rw [mul_assoc]
    _ = 1 * x := by rw [inv_mul_cancel₀ hx]
    _ = x := one_mul x

private lemma ggQ2x_two_mul_neg (x : ZMod 3) : (2 : ZMod 3) * x = -x := by
  have h : ∀ y : ZMod 3, (2 : ZMod 3) * y = -y := by decide
  exact h x

private lemma ggQ2x_neg_mul (r s : ZMod 3) : (-r) * s = -(r * s) := by
  have h : ∀ r s : ZMod 3, (-r) * s = -(r * s) := by decide
  exact h r s

private lemma ggQ2x_dot_eq {n : ℕ} (c v : GGBCV n) : ggBCDot c v = c ⬝ᵥ v := by
  simp only [ggBCDot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, dotProduct]

private lemma ggQ2x_neg_smul {n : ℕ} (r : ZMod 3) (c : GGBCV n) : (-r) • c = -(r • c) := by
  funext i
  simp only [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact ggQ2x_neg_mul r (c i)

private lemma ggQ2x_hc {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ((2 / (c ⬝ᵥ c)) • ggBCDot c) c = 2 := by
  rw [LinearMap.smul_apply, ggQ2x_dot_eq, div_eq_mul_inv, ggQ2x_inv_eq_self (c ⬝ᵥ c) hc]
  rw [smul_eq_mul, ggQ2x_two_mul_neg, ggQ2x_neg_mul, ggQ2x_sq (c ⬝ᵥ c) hc]
  decide

private lemma ggQ2x_refl_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ v) * (c ⬝ᵥ c)) • c := by
  have key : ggBCRefl c hc v = v - (((2 / (c ⬝ᵥ c)) • ggBCDot c) v) • c :=
    @Module.reflection_apply (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup (ggBCModule n)
      c ((2 / (c ⬝ᵥ c)) • ggBCDot c) v (ggQ2x_hc c hc)
  have hs : ((2 / (c ⬝ᵥ c)) • ggBCDot c) v = -((c ⬝ᵥ v) * (c ⬝ᵥ c)) := by
    rw [LinearMap.smul_apply, ggQ2x_dot_eq, div_eq_mul_inv, ggQ2x_inv_eq_self (c ⬝ᵥ c) hc]
    rw [smul_eq_mul, ggQ2x_two_mul_neg, ggQ2x_neg_mul (c ⬝ᵥ c) (c ⬝ᵥ v),
      mul_comm (c ⬝ᵥ c) (c ⬝ᵥ v)]
  rw [key, hs, ggQ2x_neg_smul]
  abel

private lemma ggQ2x_dot_smul {n : ℕ} (a : ZMod 3) (v w : GGBCV n) :
    (a • v) ⬝ᵥ w = a * (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf

private lemma ggQ2x_dot_smul_right {n : ℕ} (a : ZMod 3) (v w : GGBCV n) :
    v ⬝ᵥ (a • w) = a * (v ⬝ᵥ w) := by
  simp only [dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring_nf

private lemma ggQ2x_single_apply_self {n : ℕ} (i : Fin n) (a : ZMod 3) :
    (Pi.single i a : GGBCV n) i = a := by
  simp [Pi.single_apply]

private lemma ggQ2x_single_apply_ne {n : ℕ} {i j : Fin n} (hij : j ≠ i) (a : ZMod 3) :
    (Pi.single i a : GGBCV n) j = 0 := by
  simp [Pi.single_apply, hij]

private lemma ggQ2x_refl_smul_single_self {n : ℕ} (k : Fin n) (a : ZMod 3) (ha : a ≠ 0)
    (hc : (a • Pi.single k 1 : GGBCV n) ⬝ᵥ (a • Pi.single k 1) ≠ 0) :
    ggBCRefl (a • Pi.single k 1) hc (Pi.single k 1) = (-1 : ZMod 3) • Pi.single k 1 := by
  have hcc : (a • Pi.single k 1 : GGBCV n) ⬝ᵥ (a • Pi.single k 1) = 1 := by
    rw [ggQ2x_dot_smul, ggQ2x_dot_smul_right, dotProduct_single_one,
      ggQ2x_single_apply_self, mul_one, ggQ2x_sq a ha]
  have hcf : (a • Pi.single k 1 : GGBCV n) ⬝ᵥ (Pi.single k 1) = a := by
    rw [ggQ2x_dot_smul, dotProduct_single_one, ggQ2x_single_apply_self, mul_one]
  rw [ggQ2x_refl_apply, hcc, hcf, mul_one, smul_smul, ggQ2x_sq a ha, one_smul]
  funext j
  by_cases hjk : j = k
  · subst hjk
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    decide
  · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same,
      ggQ2x_single_apply_ne hjk, smul_eq_mul, mul_zero, mul_one, add_zero]

private lemma ggQ2x_dot_pair {n : ℕ} (a b : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0)
    (k l : Fin n) (hkl : k ≠ l) :
    (a • Pi.single k 1 + b • Pi.single l 1 : GGBCV n) ⬝ᵥ
      (a • Pi.single k 1 + b • Pi.single l 1) = 2 := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add]
  simp only [ggQ2x_dot_smul, ggQ2x_dot_smul_right, dotProduct_single_one, Pi.smul_apply,
    smul_eq_mul, ggQ2x_single_apply_self, ggQ2x_single_apply_ne hkl,
    ggQ2x_single_apply_ne hkl.symm, mul_zero, mul_one, add_zero, zero_add]
  have h : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → a * a + b * b = 2 := by decide
  exact h a b ha hb

private lemma ggQ2x_pair_mixed (a b : ZMod 3) : (a * 2) * b = 2 * a * b := by
  have h : ∀ a b : ZMod 3, (a * 2) * b = 2 * a * b := by decide
  exact h a b

private lemma ggQ2x_pair_self_scalar (a : ZMod 3) (ha : a ≠ 0) :
    1 + (a * 2) * a = 0 := by
  have h : ∀ a : ZMod 3, a ≠ 0 → 1 + (a * 2) * a = 0 := by decide
  exact h a ha

private lemma ggQ2x_refl_smul_single_ne {n : ℕ} {i k : Fin n} (hik : i ≠ k) (a : ZMod 3)
    (ha : a ≠ 0)
    (hc : (a • Pi.single k 1 : GGBCV n) ⬝ᵥ (a • Pi.single k 1) ≠ 0) :
    ggBCRefl (a • Pi.single k 1) hc (Pi.single i 1) = (1 : ZMod 3) • Pi.single i 1 := by
  have hcc : (a • Pi.single k 1 : GGBCV n) ⬝ᵥ (a • Pi.single k 1) = 1 := by
    rw [ggQ2x_dot_smul, ggQ2x_dot_smul_right, dotProduct_single_one,
      ggQ2x_single_apply_self, mul_one, ggQ2x_sq a ha]
  have hcf : (a • Pi.single k 1 : GGBCV n) ⬝ᵥ (Pi.single i 1) = 0 := by
    rw [ggQ2x_dot_smul, dotProduct_single_one, ggQ2x_single_apply_ne hik, mul_zero]
  rw [ggQ2x_refl_apply, hcc, hcf, zero_mul, zero_smul, add_zero, one_smul]

private lemma ggQ2x_refl_pair_self {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (a b : ZMod 3)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : (a • Pi.single k 1 + b • Pi.single l 1 : GGBCV n) ⬝ᵥ
      (a • Pi.single k 1 + b • Pi.single l 1) ≠ 0) :
    ggBCRefl (a • Pi.single k 1 + b • Pi.single l 1) hc (Pi.single k 1) =
      (2 * a * b) • Pi.single l 1 := by
  have hcc := ggQ2x_dot_pair a b ha hb k l hkl
  have hcf : (a • Pi.single k 1 + b • Pi.single l 1 : GGBCV n) ⬝ᵥ (Pi.single k 1) = a := by
    rw [add_dotProduct, ggQ2x_dot_smul, ggQ2x_dot_smul, dotProduct_single_one,
      dotProduct_single_one, ggQ2x_single_apply_self, ggQ2x_single_apply_ne hkl,
      mul_one, mul_zero, add_zero]
  rw [ggQ2x_refl_apply, hcc, hcf]
  funext j
  by_cases hjl : j = l
  · subst hjl
    simp only [Pi.add_apply, Pi.smul_apply, ggQ2x_single_apply_self,
      ggQ2x_single_apply_ne hkl.symm, smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]
    rw [ggQ2x_pair_mixed]
  · by_cases hjk : j = k
    · subst hjk
      simp only [Pi.add_apply, Pi.smul_apply, ggQ2x_single_apply_self,
        ggQ2x_single_apply_ne hkl, smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]
      exact ggQ2x_pair_self_scalar a ha
    · simp only [Pi.add_apply, Pi.smul_apply, ggQ2x_single_apply_ne hjl,
        ggQ2x_single_apply_ne hjk, smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]

private lemma ggQ2x_pair_mixed_swap (a b : ZMod 3) : (b * 2) * a = 2 * a * b := by
  have h : ∀ a b : ZMod 3, (b * 2) * a = 2 * a * b := by decide
  exact h a b

private lemma ggQ2x_refl_pair_swap {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (a b : ZMod 3)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : (a • Pi.single k 1 + b • Pi.single l 1 : GGBCV n) ⬝ᵥ
      (a • Pi.single k 1 + b • Pi.single l 1) ≠ 0) :
    ggBCRefl (a • Pi.single k 1 + b • Pi.single l 1) hc (Pi.single l 1) =
      (2 * a * b) • Pi.single k 1 := by
  have hcc := ggQ2x_dot_pair a b ha hb k l hkl
  have hcf : (a • Pi.single k 1 + b • Pi.single l 1 : GGBCV n) ⬝ᵥ (Pi.single l 1) = b := by
    rw [add_dotProduct, ggQ2x_dot_smul, ggQ2x_dot_smul, dotProduct_single_one,
      dotProduct_single_one, ggQ2x_single_apply_self, ggQ2x_single_apply_ne hkl.symm,
      mul_one, mul_zero, zero_add]
  rw [ggQ2x_refl_apply, hcc, hcf]
  funext j
  by_cases hjk : j = k
  · rw [hjk]
    simp only [Pi.add_apply, Pi.smul_apply, ggQ2x_single_apply_self,
      ggQ2x_single_apply_ne hkl, smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]
    rw [ggQ2x_pair_mixed_swap]
  · by_cases hjl : j = l
    · rw [hjl]
      simp only [Pi.add_apply, Pi.smul_apply, ggQ2x_single_apply_self,
        ggQ2x_single_apply_ne hkl.symm, smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]
      exact ggQ2x_pair_self_scalar b hb
    · simp only [Pi.add_apply, Pi.smul_apply, ggQ2x_single_apply_ne hjk,
        ggQ2x_single_apply_ne hjl, smul_eq_mul, mul_zero, add_zero, zero_add, mul_one]

private lemma ggQ2x_refl_pair_other {n : ℕ} {k l i : Fin n} (hik : i ≠ k) (hil : i ≠ l)
    (hkl : k ≠ l) (a b : ZMod 3) (ha : a ≠ 0) (hb : b ≠ 0)
    (hc : (a • Pi.single k 1 + b • Pi.single l 1 : GGBCV n) ⬝ᵥ
      (a • Pi.single k 1 + b • Pi.single l 1) ≠ 0) :
    ggBCRefl (a • Pi.single k 1 + b • Pi.single l 1) hc (Pi.single i 1) =
      (1 : ZMod 3) • Pi.single i 1 := by
  have hcc := ggQ2x_dot_pair a b ha hb k l hkl
  have hcf : (a • Pi.single k 1 + b • Pi.single l 1 : GGBCV n) ⬝ᵥ (Pi.single i 1) = 0 := by
    rw [add_dotProduct, ggQ2x_dot_smul, ggQ2x_dot_smul, dotProduct_single_one,
      dotProduct_single_one, ggQ2x_single_apply_ne hik, ggQ2x_single_apply_ne hil,
      mul_zero, mul_zero, add_zero]
  rw [ggQ2x_refl_apply, hcc, hcf, zero_mul, zero_smul, add_zero, one_smul]

private def ggQ2x_supp {n : ℕ} (v : GGBCV n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i ≠ 0)

private lemma ggQ2x_supp_smul {n : ℕ} (a : ZMod 3) (ha : a ≠ 0) (v : GGBCV n) :
    ggQ2x_supp (a • v) = ggQ2x_supp v := by
  unfold ggQ2x_supp
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Pi.smul_apply, smul_eq_mul]
  rw [mul_ne_zero_iff]
  exact and_iff_right ha

private lemma ggQ2x_eq_sum_supp {n : ℕ} (v : GGBCV n) :
    v = ∑ i ∈ ggQ2x_supp v, v i • Pi.single i 1 := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  by_cases hj : j ∈ ggQ2x_supp v
  · rw [Finset.sum_eq_single j]
    · rw [ggQ2x_single_apply_self, mul_one]
    · intro b _ hbj
      rw [ggQ2x_single_apply_ne (Ne.symm hbj), mul_zero]
    · intro hjs
      exact absurd hj hjs
  · have hvj : v j = 0 := by
      by_contra h
      exact hj (by
        unfold ggQ2x_supp
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact h)
    rw [hvj, Finset.sum_eq_zero]
    · intro i hi
      have hij : i ≠ j := by rintro rfl; exact hj hi
      rw [ggQ2x_single_apply_ne (Ne.symm hij), mul_zero]

private lemma ggQ2x_wt_one {n : ℕ} {v : GGBCV n} (hv : ggBCWt v = 1) :
    ∃ (k : Fin n) (a : ZMod 3), a ≠ 0 ∧ v = a • Pi.single k 1 := by
  have hcard : (ggQ2x_supp v).card = 1 := hv
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hcard
  have hk_mem : k ∈ ggQ2x_supp v := by rw [hk]; exact Finset.mem_singleton_self k
  have hvk : v k ≠ 0 := by
    rw [ggQ2x_supp] at hk_mem
    simpa using hk_mem
  refine ⟨k, v k, hvk, ?_⟩
  calc v = ∑ i ∈ ggQ2x_supp v, v i • Pi.single i 1 := ggQ2x_eq_sum_supp v
    _ = v k • Pi.single k 1 := by rw [hk, Finset.sum_singleton]

private lemma ggQ2x_wt_two {n : ℕ} {v : GGBCV n} (hv : ggBCWt v = 2) :
    ∃ (k l : Fin n) (a b : ZMod 3), k ≠ l ∧ a ≠ 0 ∧ b ≠ 0 ∧
      v = a • Pi.single k 1 + b • Pi.single l 1 := by
  have hcard : (ggQ2x_supp v).card = 2 := hv
  obtain ⟨k, l, hkl, hk⟩ := Finset.card_eq_two.mp hcard
  have hk_mem : k ∈ ggQ2x_supp v := by rw [hk]; exact Finset.mem_insert_self k {l}
  have hl_mem : l ∈ ggQ2x_supp v := by
    rw [hk]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self l)
  have hvk : v k ≠ 0 := by
    rw [ggQ2x_supp] at hk_mem
    simpa using hk_mem
  have hvl : v l ≠ 0 := by
    rw [ggQ2x_supp] at hl_mem
    simpa using hl_mem
  refine ⟨k, l, v k, v l, hkl, hvk, hvl, ?_⟩
  calc v = ∑ i ∈ ggQ2x_supp v, v i • Pi.single i 1 := ggQ2x_eq_sum_supp v
    _ = v k • Pi.single k 1 + v l • Pi.single l 1 := by rw [hk, Finset.sum_pair hkl]

private def ggQ2x_Mon (n : ℕ) : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) where
  carrier := {t | ∃ (σ : Fin n ≃ Fin n) (ε : Fin n → ZMod 3),
    (∀ i, ε i ≠ 0) ∧ ∀ i, t (Pi.single i 1) = ε i • Pi.single (σ i) 1}
  one_mem' := ⟨1, fun _ => 1, fun _ => one_ne_zero, fun i => by simp⟩
  mul_mem' := by
    rintro t u ⟨σt, εt, hεt, ht⟩ ⟨σu, εu, hεu, hu⟩
    refine ⟨σu.trans σt, fun i => εu i * εt (σu i),
      fun i => mul_ne_zero (hεu i) (hεt (σu i)), fun i => ?_⟩
    rw [LinearEquiv.mul_apply, hu, map_smul, ht, smul_smul, Equiv.trans_apply]
  inv_mem' := by
    rintro t ⟨σ, ε, hε, ht⟩
    refine ⟨σ.symm, fun j => (ε (σ.symm j))⁻¹, fun j => inv_ne_zero (hε _), fun j => ?_⟩
    have h1 : t ((ε (σ.symm j))⁻¹ • Pi.single (σ.symm j) 1) = Pi.single j 1 := by
      rw [map_smul, ht, Equiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ (hε _), one_smul]
    rw [← h1]
    simp

private lemma ggQ2x_refl_mem_Mon {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0)
    (hroot : c ∈ ggBCRoots n) : ggBCRefl c hc ∈ ggQ2x_Mon n := by
  rcases hroot with ⟨h1, h2⟩
  have hc12 : ggBCWt c = 1 ∨ ggBCWt c = 2 := by omega
  rcases hc12 with hc1 | hc2
  · obtain ⟨k, a, ha, rfl⟩ := ggQ2x_wt_one hc1
    refine ⟨1, fun i => if i = k then -1 else 1, ?_, ?_⟩
    · intro i
      dsimp only
      by_cases h : i = k
      · rw [if_pos h]; decide
      · rw [if_neg h]; decide
    · intro i
      by_cases hik : i = k
      · rw [hik]
        rw [ggQ2x_refl_smul_single_self k a ha hc]
        simp
      · rw [ggQ2x_refl_smul_single_ne hik a ha hc]
        simp [hik]
  · obtain ⟨k, l, a, b, hkl, ha, hb, rfl⟩ := ggQ2x_wt_two hc2
    refine ⟨Equiv.swap k l, fun i => if i = k ∨ i = l then 2 * a * b else 1, ?_, ?_⟩
    · intro i
      by_cases h : i = k ∨ i = l
      · simp only [h, ↓reduceIte]
        exact mul_ne_zero (mul_ne_zero (by decide : (2 : ZMod 3) ≠ 0) ha) hb
      · simp only [h, ↓reduceIte]
        exact one_ne_zero
    · intro i
      by_cases hik : i = k
      · subst hik
        rw [ggQ2x_refl_pair_self hkl a b ha hb hc]
        simp [hkl]
      · by_cases hil : i = l
        · subst hil
          rw [ggQ2x_refl_pair_swap hkl a b ha hb hc]
          simp [hkl]
        · rw [ggQ2x_refl_pair_other hik hil hkl a b ha hb hc]
          rw [Equiv.swap_apply_of_ne_of_ne hik hil]
          simp [hik, hil]

private lemma ggQ2x_refl_orthogonal {n : ℕ} (d : GGBCV n) (hd : d ⬝ᵥ d ≠ 0)
    (v w : GGBCV n) :
    (ggBCRefl d hd v) ⬝ᵥ (ggBCRefl d hd w) = v ⬝ᵥ w := by
  rw [ggQ2x_refl_apply, ggQ2x_refl_apply]
  rw [add_dotProduct, dotProduct_add, dotProduct_add]
  simp only [ggQ2x_dot_smul, ggQ2x_dot_smul_right]
  rw [dotProduct_comm v d]
  have hsc : (d ⬝ᵥ w * d ⬝ᵥ d) * (d ⬝ᵥ v) + (d ⬝ᵥ v * d ⬝ᵥ d) * (d ⬝ᵥ w) +
      (d ⬝ᵥ v * d ⬝ᵥ d) * ((d ⬝ᵥ w * d ⬝ᵥ d) * (d ⬝ᵥ d)) = 0 := by
    have h : ∀ x y z : ZMod 3, x ≠ 0 → z * x * y + y * x * z + y * x * (z * x * x) = 0 := by
      decide
    exact h (d ⬝ᵥ d) (d ⬝ᵥ v) (d ⬝ᵥ w) hd
  linear_combination hsc

private lemma ggQ2x_W_le_Mon (n : ℕ) : ggBCW n ≤ ggQ2x_Mon n := by
  rw [ggBCW]
  apply (Subgroup.closure_le (ggQ2x_Mon n)).mpr
  rintro t ⟨c, hc, hcc, rfl⟩
  exact ggQ2x_refl_mem_Mon c hcc hc

private def ggQ2x_Orth (n : ℕ) : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) where
  carrier := {t | ∀ v w : GGBCV n, (t v) ⬝ᵥ (t w) = v ⬝ᵥ w}
  one_mem' := fun v w => rfl
  mul_mem' := by
    rintro t u ht hu v w
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ht, hu]
  inv_mem' := by
    rintro t ht v w
    have h := ht (t.symm v) (t.symm w)
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at h
    exact h.symm

private lemma ggQ2x_refl_mem_Orth {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hc ∈ ggQ2x_Orth n := fun v w => ggQ2x_refl_orthogonal c hc v w

private lemma ggQ2x_W_le_Orth (n : ℕ) : ggBCW n ≤ ggQ2x_Orth n := by
  rw [ggBCW]
  apply (Subgroup.closure_le (ggQ2x_Orth n)).mpr
  rintro t ⟨c, hc, hcc, rfl⟩
  exact ggQ2x_refl_mem_Orth c hcc

private lemma ggQ2x_supp_subset_pair {n : ℕ} (a : ZMod 3) (i j : Fin n) :
    ggQ2x_supp (a • Pi.single j 1 - Pi.single i 1 : GGBCV n) ⊆ {i, j} := by
  intro k hk
  rw [ggQ2x_supp] at hk
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk
  simp only [Finset.mem_insert, Finset.mem_singleton]
  by_contra hcon
  push Not at hcon
  obtain ⟨hki, hkj⟩ := hcon
  apply hk
  rw [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ggQ2x_single_apply_ne hkj,
    ggQ2x_single_apply_ne hki, mul_zero]
  decide

private lemma ggQ2x_orth_extract (x y z : ZMod 3)
    (h : (x - 2 * x) - (y * z - y * (2 * z)) = x) : y * z = 2 * x := by
  have hh : ∀ x y z : ZMod 3, (x - 2 * x) - (y * z - y * (2 * z)) = x → y * z = 2 * x := by
    decide
  exact hh x y z h

private lemma ggQ2x_solve (x y z : ZMod 3) (hz : z ≠ 0) (h : x * z = 2 * y) :
    x = 2 * z * y := by
  have hh : ∀ x y z : ZMod 3, z ≠ 0 → x * z = 2 * y → x = 2 * z * y := by decide
  exact hh x y z hz h

private lemma ggQ2x_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

theorem ggQ2_bc_W_refl (n : ℕ) (hn : 3 ≤ n) (t : GGBCV n ≃ₗ[ZMod 3] GGBCV n) (ht : t ∈ ggBCW n)
    (hr : IsReflLin t) : t ∈ ggBCReflSet (ggBCRoots n) := by
  obtain ⟨c, φ, hφc, ht_eq⟩ := hr
  obtain ⟨σ, ε, hε, htf⟩ := ggQ2x_W_le_Mon n ht
  have horth := ggQ2x_W_le_Orth n ht
  have htapply : ∀ v, t v = v - (φ v) • c := by
    intro v
    rw [ht_eq]
    exact @Module.reflection_apply (ZMod 3) (GGBCV n) (ZMod.commRing 3) Pi.addCommGroup
      (ggBCModule n) c φ v hφc
  have hkey : ∀ v, (φ v) * (c ⬝ᵥ c) = 2 * (v ⬝ᵥ c) := by
    intro v
    have h := horth v c
    rw [htapply v, htapply c, hφc] at h
    rw [sub_dotProduct, dotProduct_sub, dotProduct_sub] at h
    rw [ggQ2x_dot_smul, ggQ2x_dot_smul, ggQ2x_dot_smul_right, ggQ2x_dot_smul_right] at h
    exact ggQ2x_orth_extract (v ⬝ᵥ c) (φ v) (c ⬝ᵥ c) h
  have hcc_ne : c ⬝ᵥ c ≠ 0 := by
    intro hcc0
    have hc0 : c = 0 := by
      funext i
      have hv := hkey (Pi.single i 1)
      rw [hcc0, mul_zero, single_one_dotProduct] at hv
      exact (mul_eq_zero.mp hv.symm).resolve_left ggQ2x_two_ne_zero
    have hz : φ 0 = 0 := LinearMap.map_zero φ
    have hφ0 : φ 0 = 2 := hc0 ▸ hφc
    exact ggQ2x_two_ne_zero (hφ0.symm.trans hz)
  have hφv : ∀ v, φ v = (2 / (c ⬝ᵥ c)) * (c ⬝ᵥ v) := by
    intro v
    rw [div_eq_mul_inv, ggQ2x_inv_eq_self (c ⬝ᵥ c) hcc_ne]
    have hv := hkey v
    rw [dotProduct_comm v c] at hv
    exact ggQ2x_solve (φ v) (c ⬝ᵥ v) (c ⬝ᵥ c) hcc_ne hv
  have ht_refl : t = ggBCRefl c hcc_ne := by
    apply LinearEquiv.ext
    intro v
    rw [htapply v, hφv v, ggQ2x_refl_apply]
    have hs : (2 / (c ⬝ᵥ c)) * (c ⬝ᵥ v) = -((c ⬝ᵥ v) * (c ⬝ᵥ c)) := by
      rw [div_eq_mul_inv, ggQ2x_inv_eq_self (c ⬝ᵥ c) hcc_ne]
      rw [ggQ2x_two_mul_neg, ggQ2x_neg_mul (c ⬝ᵥ c) (c ⬝ᵥ v),
        mul_comm (c ⬝ᵥ c) (c ⬝ᵥ v)]
    rw [hs, ggQ2x_neg_smul]
    abel
  have hroot : c ∈ ggBCRoots n := by
    have hcne : c ≠ 0 := by
      intro hc0
      have hz : φ 0 = 0 := LinearMap.map_zero φ
      have hφ0 : φ 0 = 2 := hc0 ▸ hφc
      exact ggQ2x_two_ne_zero (hφ0.symm.trans hz)
    obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
      by_contra h
      push Not at h
      exact hcne (funext h)
    have hφi : φ (Pi.single i 1) ≠ 0 := by
      intro h0
      have hv := hkey (Pi.single i 1)
      rw [h0, zero_mul, single_one_dotProduct] at hv
      exact hi ((mul_eq_zero.mp hv.symm).resolve_left ggQ2x_two_ne_zero)
    have hD : t (Pi.single i 1) - Pi.single i 1 =
        -((φ (Pi.single i 1))) • c := by
      rw [htapply (Pi.single i 1)]
      have h : (Pi.single i 1 - (φ (Pi.single i 1)) • c) - Pi.single i 1 =
          -((φ (Pi.single i 1)) • c) := by abel
      rw [h]
      exact (neg_smul (φ (Pi.single i 1)) c).symm
    have hsub : ggQ2x_supp c ⊆ {i, σ i} := by
      have h1 : ggQ2x_supp c = ggQ2x_supp (t (Pi.single i 1) - Pi.single i 1) := by
        rw [hD]
        exact (ggQ2x_supp_smul (-(φ (Pi.single i 1))) (neg_ne_zero.mpr hφi) c).symm
      rw [h1, htf i]
      exact ggQ2x_supp_subset_pair (ε i) i (σ i)
    have hcard_le : (ggQ2x_supp c).card ≤ 2 := by
      calc (ggQ2x_supp c).card ≤ ({i, σ i} : Finset (Fin n)).card := Finset.card_le_card hsub
        _ ≤ 2 := Finset.card_le_two
    have hcard_ge : 1 ≤ (ggQ2x_supp c).card := by
      exact Finset.card_pos.mpr ⟨i, by
        rw [ggQ2x_supp]
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact hi⟩
    exact ⟨hcard_ge, hcard_le⟩
  exact ⟨c, hroot, hcc_ne, ht_refl⟩

private def ggQ2x_Fix0 (n : ℕ) [NeZero n] : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) where
  carrier := {u | u (Pi.single 0 1) = Pi.single 0 1}
  one_mem' := rfl
  mul_mem' := by
    rintro u v hu hv
    change (u * v) (Pi.single 0 1) = Pi.single 0 1
    rw [LinearEquiv.mul_apply, hv, hu]
  inv_mem' := by
    rintro u hu
    change u⁻¹ (Pi.single 0 1) = Pi.single 0 1
    conv_lhs => rw [← hu]
    simp

private lemma ggQ2x_lam1_le_W (n : ℕ) [NeZero n] :
    Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)) ≤ ggBCW n := by
  rw [ggBCW]
  apply (Subgroup.closure_le (ggBCW n)).mpr
  rintro u ⟨d, hd, hdd, rfl⟩
  exact Subgroup.subset_closure
    (show ggBCRefl d hdd ∈ ggBCReflSet (ggBCRoots n) from ⟨d, hd.1, hdd, rfl⟩)

private lemma ggQ2x_refl_mem_Fix0 {n : ℕ} [NeZero n] {d : GGBCV n} (hd : d ∈ ggBCRootsLam1 n)
    (hdd : d ⬝ᵥ d ≠ 0) : ggBCRefl d hdd ∈ ggQ2x_Fix0 n := by
  change ggBCRefl d hdd (Pi.single 0 1) = Pi.single 0 1
  rw [ggQ2x_refl_apply, dotProduct_single_one, hd.2, zero_mul, zero_smul, add_zero]

private lemma ggQ2x_closure_lam1_le_Fix0 (n : ℕ) [NeZero n] :
    Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n)) ≤ ggQ2x_Fix0 n := by
  apply (Subgroup.closure_le (ggQ2x_Fix0 n)).mpr
  rintro u ⟨d, hd, hdd, rfl⟩
  exact ggQ2x_refl_mem_Fix0 hd hdd

theorem ggQ2_bc_Lam1_refl (n : ℕ) [NeZero n] (hn : 5 ≤ n) (t : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (ht : t ∈ Subgroup.closure (ggBCReflSet (ggBCRootsLam1 n))) (hr : IsReflLin t) :
    t ∈ ggBCReflSet (ggBCRootsLam1 n) := by
  have htW : t ∈ ggBCW n := ggQ2x_lam1_le_W n ht
  obtain ⟨c, hc, hcc, ht_eq⟩ := ggQ2_bc_W_refl n (by omega) t htW hr
  have hfix : t (Pi.single 0 1) = Pi.single 0 1 := ggQ2x_closure_lam1_le_Fix0 n ht
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0] at hcc
    simp at hcc
  have hc0 : c 0 = 0 := by
    rw [ht_eq, ggQ2x_refl_apply, dotProduct_single_one] at hfix
    by_contra hne
    have hX : ((c 0) * (c ⬝ᵥ c)) • c = 0 := by
      have hh : Pi.single (0 : Fin n) 1 + ((c 0) * (c ⬝ᵥ c)) • c =
          Pi.single (0 : Fin n) 1 + 0 := by rw [hfix, add_zero]
      exact add_left_cancel hh
    exact hcne ((smul_eq_zero.mp hX).resolve_left (mul_ne_zero hne hcc))
  exact ⟨c, ⟨hc, hc0⟩, hcc, ht_eq⟩

private def ggQ2x_Perm (n : ℕ) : Subgroup (GGBCV n ≃ₗ[ZMod 3] GGBCV n) where
  carrier := {u | ∃ σ : Fin n ≃ Fin n, ∀ i, u (Pi.single i 1) = Pi.single (σ i) 1}
  one_mem' := ⟨1, fun i => by simp⟩
  mul_mem' := by
    rintro u v ⟨σ, hσ⟩ ⟨τ, hτ⟩
    refine ⟨τ.trans σ, fun i => ?_⟩
    rw [LinearEquiv.mul_apply, hτ, hσ, Equiv.trans_apply]
  inv_mem' := by
    rintro u ⟨σ, hσ⟩
    refine ⟨σ.symm, fun j => ?_⟩
    have h1 : u (Pi.single (σ.symm j) 1) = Pi.single j 1 := by
      rw [hσ, Equiv.apply_symm_apply]
    rw [← h1]
    simp

private lemma ggQ2x_sum_single {n : ℕ} (k : Fin n) (a : ZMod 3) :
    ∑ i, (a • Pi.single k 1 : GGBCV n) i = a := by
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  have h1 : (∑ i, (Pi.single k 1 : GGBCV n) i) = 1 := by
    rw [Finset.sum_eq_single k]
    · simp
    · intro j _ hj
      simp [Pi.single_apply, hj]
    · intro hk
      exact absurd (Finset.mem_univ k) hk
  rw [h1, mul_one]

private lemma ggQ2x_sum_pair {n : ℕ} (k l : Fin n) (a b : ZMod 3) :
    ∑ i, (a • Pi.single k 1 + b • Pi.single l 1 : GGBCV n) i = a + b := by
  simp only [Pi.add_apply]
  rw [Finset.sum_add_distrib, ggQ2x_sum_single, ggQ2x_sum_single]

private lemma ggQ2x_ab_of_two_ab {a b : ZMod 3} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : 2 * a * b = 1) : a + b = 0 := by
  have hh : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → 2 * a * b = 1 → a + b = 0 := by decide
  exact hh a b ha hb h

private lemma ggQ2x_refl_mem_Perm {n : ℕ} {d : GGBCV n} (hd : d ∈ ggBCRootsLamN n)
    (hdd : d ⬝ᵥ d ≠ 0) : ggBCRefl d hdd ∈ ggQ2x_Perm n := by
  obtain ⟨hwt, hsum⟩ := hd
  obtain ⟨k, l, a, b, hkl, ha, hb, hdeq⟩ := ggQ2x_wt_two hwt
  have hab : a + b = 0 := by
    rw [hdeq] at hsum
    rw [ggQ2x_sum_pair] at hsum
    exact hsum
  have h2ab : 2 * a * b = 1 := by
    have hh : ∀ a b : ZMod 3, a ≠ 0 → b ≠ 0 → a + b = 0 → 2 * a * b = 1 := by decide
    exact hh a b ha hb hab
  cases hdeq
  refine ⟨Equiv.swap k l, fun i => ?_⟩
  by_cases hik : i = k
  · rw [hik, ggQ2x_refl_pair_self hkl a b ha hb hdd, h2ab, one_smul, Equiv.swap_apply_left]
  · by_cases hil : i = l
    · rw [hil, ggQ2x_refl_pair_swap hkl a b ha hb hdd, h2ab, one_smul, Equiv.swap_apply_right]
    · rw [ggQ2x_refl_pair_other hik hil hkl a b ha hb hdd, one_smul,
        Equiv.swap_apply_of_ne_of_ne hik hil]

private lemma ggQ2x_closure_lamN_le_Perm (n : ℕ) :
    Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)) ≤ ggQ2x_Perm n := by
  apply (Subgroup.closure_le (ggQ2x_Perm n)).mpr
  rintro u ⟨d, hd, hdd, rfl⟩
  exact ggQ2x_refl_mem_Perm hd hdd

theorem ggQ2_bc_LamN_refl (n : ℕ) (hn : 5 ≤ n) (t : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (ht : t ∈ Subgroup.closure (ggBCReflSet (ggBCRootsLamN n))) (hr : IsReflLin t) :
    t ∈ ggBCReflSet (ggBCRootsLamN n) := by
  have hle : Subgroup.closure (ggBCReflSet (ggBCRootsLamN n)) ≤ ggBCW n := by
    rw [ggBCW]
    apply (Subgroup.closure_le (ggBCW n)).mpr
    rintro u ⟨d, hd, hdd, rfl⟩
    obtain ⟨hwt, hsum⟩ := hd
    have hroot : d ∈ ggBCRoots n :=
      ⟨le_trans (by decide : 1 ≤ 2) (le_of_eq hwt.symm), le_of_eq hwt⟩
    exact Subgroup.subset_closure ⟨d, hroot, hdd, rfl⟩
  have htW : t ∈ ggBCW n := hle ht
  obtain ⟨c, hc, hcc, ht_eq⟩ := ggQ2_bc_W_refl n (by omega) t htW hr
  obtain ⟨hc1, hc2⟩ := hc
  obtain ⟨σ, hσ⟩ := ggQ2x_closure_lamN_le_Perm n ht
  have hwt : ggBCWt c = 2 := by
    rcases (by omega : ggBCWt c = 1 ∨ ggBCWt c = 2) with h1 | h2
    · exfalso
      obtain ⟨k, a, ha, hceq⟩ := ggQ2x_wt_one h1
      subst hceq
      have h := hσ k
      rw [ht_eq] at h
      rw [ggQ2x_refl_smul_single_self k a ha hcc] at h
      have hk := congrFun h k
      rw [Pi.smul_apply, smul_eq_mul, ggQ2x_single_apply_self, mul_one] at hk
      by_cases hh : σ k = k
      · rw [hh, ggQ2x_single_apply_self] at hk
        exact absurd hk (by decide)
      · rw [ggQ2x_single_apply_ne (Ne.symm hh)] at hk
        exact absurd hk (by decide)
    · exact h2
  have hsum : ∑ i, c i = 0 := by
    obtain ⟨k, l, a, b, hkl, ha, hb, hceq⟩ := ggQ2x_wt_two hwt
    subst hceq
    have h := hσ k
    rw [ht_eq] at h
    rw [ggQ2x_refl_pair_self hkl a b ha hb hcc] at h
    have hl := congrFun h l
    rw [Pi.smul_apply, smul_eq_mul, ggQ2x_single_apply_self, mul_one] at hl
    have h2ab : 2 * a * b = 1 := by
      by_cases hh : σ k = l
      · rw [hh, ggQ2x_single_apply_self] at hl
        exact hl
      · rw [ggQ2x_single_apply_ne (Ne.symm hh)] at hl
        exact absurd hl (mul_ne_zero (mul_ne_zero ggQ2x_two_ne_zero ha) hb)
    rw [ggQ2x_sum_pair k l a b]
    exact ggQ2x_ab_of_two_ab ha hb h2ab
  exact ⟨c, ⟨hwt, hsum⟩, hcc, ht_eq⟩

end CFSG.StandardType

end

