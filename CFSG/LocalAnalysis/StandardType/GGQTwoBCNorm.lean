module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBCDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoBCRefl

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin

private lemma ggQ2x_dot_eq (n : ℕ) (c v : GGBCV n) : ggBCDot c v = c ⬝ᵥ v := by
  simp only [ggBCDot, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul]
  rfl

private lemma ggQ2x_coord (a b p q : ZMod 3) :
    a - (2 * p * q) * b = a + (p * q) * b := by
  revert a b p q; decide

private lemma ggQ2x_refl_apply {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (v : GGBCV n) :
    ggBCRefl c hc v = v + ((c ⬝ᵥ c) * (c ⬝ᵥ v)) • c := by
  have hcast : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide
  have hcc : c ⬝ᵥ c * (c ⬝ᵥ c) = 1 := hcast _ hc
  have hinv : (c ⬝ᵥ c)⁻¹ = c ⬝ᵥ c := inv_eq_of_mul_eq_one_right hcc
  change Module.preReflection c ((2 / (c ⬝ᵥ c)) • ggBCDot c) v =
    v + ((c ⬝ᵥ c) * (c ⬝ᵥ v)) • c
  change v - (((2 / (c ⬝ᵥ c)) • ggBCDot c) v) • c =
    v + ((c ⬝ᵥ c) * (c ⬝ᵥ v)) • c
  rw [div_eq_mul_inv, hinv]
  rw [show (((2 * (c ⬝ᵥ c)) • ggBCDot c) v) = (2 * (c ⬝ᵥ c)) * (c ⬝ᵥ v) by
    rw [LinearMap.smul_apply, ggQ2x_dot_eq, smul_eq_mul]]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  exact ggQ2x_coord (v i) (c i) (c ⬝ᵥ c) (c ⬝ᵥ v)


private lemma ggQ2x_wt_single_of_ne_zero {n : ℕ} (i : Fin n) (s : ZMod 3) (hs : s ≠ 0) :
    ggBCWt (Pi.single i s) = 1 := by
  unfold ggBCWt
  rw [Finset.card_eq_one]
  refine ⟨i, ?_⟩
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro hj
    by_contra hne
    exact hj (Pi.single_eq_of_ne (M := fun _ => ZMod 3) hne s)
  · rintro rfl
    rw [Pi.single_eq_same]
    exact hs


private lemma ggQ2x_wt_eq_one_iff {n : ℕ} {v : GGBCV n} :
    ggBCWt v = 1 ↔ ∃ i s, s ≠ 0 ∧ v = Pi.single i s := by
  constructor
  · intro hv
    unfold ggBCWt at hv
    obtain ⟨i, h⟩ := Finset.card_eq_one.mp hv
    refine ⟨i, v i, ?_, ?_⟩
    · have : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by
        rw [h]; exact Finset.mem_singleton_self i
      simpa using this
    · ext k
      by_cases hk : k = i
      · subst hk; rw [Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hk]
        have : k ∉ Finset.univ.filter (fun l => v l ≠ 0) := by
          rw [h]; simp [hk]
        simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using this
  · rintro ⟨i, s, hs, rfl⟩
    exact ggQ2x_wt_single_of_ne_zero i s hs

private lemma ggQ2x_wt_two {n : ℕ} {v : GGBCV n} (hv : ggBCWt v = 2) :
    ∃ i j s t, i ≠ j ∧ s ≠ 0 ∧ t ≠ 0 ∧ v = Pi.single i s + Pi.single j t := by
  unfold ggBCWt at hv
  obtain ⟨i, j, hij, h⟩ := Finset.card_eq_two.mp hv
  refine ⟨i, j, v i, v j, hij, ?_, ?_, ?_⟩
  · have : i ∈ Finset.univ.filter (fun k => v k ≠ 0) := by
      rw [h]; simp
    simpa using this
  · have : j ∈ Finset.univ.filter (fun k => v k ≠ 0) := by
      rw [h]; simp
    simpa using this
  · ext k
    by_cases hki : k = i
    · subst hki
      simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij]
    · by_cases hkj : k = j
      · subst hkj
        simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij), add_comm]
      · have hk : k ∉ Finset.univ.filter (fun l => v l ≠ 0) := by
          rw [h]; simp [hki, hkj]
        have hvk : v k = 0 := by
          simpa only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] using hk
        rw [hvk]
        simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hki,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkj]

private lemma ggQ2x_dot_single_self {n : ℕ} (i : Fin n) (s : ZMod 3) :
    (Pi.single i s) ⬝ᵥ (Pi.single i s) = s * s := by
  rw [single_dotProduct, Pi.single_eq_same]

private lemma ggQ2x_two_ss : ∀ s t : ZMod 3, s ≠ 0 → t ≠ 0 → s * s + t * t = (2 : ZMod 3) :=
  by decide

private lemma ggQ2x_dot_two_single {n : ℕ} (i j : Fin n) (s t : ZMod 3) (hij : i ≠ j) :
    (Pi.single i s + Pi.single j t) ⬝ᵥ (Pi.single i s + Pi.single j t) = s * s + t * t := by
  rw [add_dotProduct, dotProduct_add, dotProduct_add, ggQ2x_dot_single_self,
    ggQ2x_dot_single_self, single_dotProduct, dotProduct_single]
  rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hij t]
  revert s t
  decide

private lemma ggQ2x_dot_self_ne_zero_of_wt {n : ℕ} {c : GGBCV n}
    (h1 : 1 ≤ ggBCWt c) (h2 : ggBCWt c ≤ 2) : c ⬝ᵥ c ≠ 0 := by
  have hz : ∀ z : ZMod 3, z ≠ 0 → z * z ≠ 0 := by decide
  rcases (by omega : ggBCWt c = 1 ∨ ggBCWt c = 2) with h | h
  · obtain ⟨i, s, hs, rfl⟩ := ggQ2x_wt_eq_one_iff.mp h
    rw [ggQ2x_dot_single_self]
    exact hz s hs
  · obtain ⟨i, j, s, t, hij, hs, ht, rfl⟩ := ggQ2x_wt_two h
    rw [ggQ2x_dot_two_single i j s t hij]
    rw [ggQ2x_two_ss s t hs ht]
    decide


private lemma ggQ2x_iso_scalar : ∀ r d p q : ZMod 3, d * d = 1 →
    r + d * p * q + d * q * (p + d * p * d) = r := by decide

private lemma ggQ2x_refl_isometry {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) (x y : GGBCV n) :
    (ggBCRefl c hc x) ⬝ᵥ (ggBCRefl c hc y) = x ⬝ᵥ y := by
  have hcast : ∀ z : ZMod 3, z ≠ 0 → z * z = 1 := by decide
  have hdd : (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 := hcast _ hc
  rw [ggQ2x_refl_apply, ggQ2x_refl_apply]
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm (c : GGBCV n) x, dotProduct_comm (c : GGBCV n) y]
  rw [ggQ2x_iso_scalar (x ⬝ᵥ y) (c ⬝ᵥ c) (x ⬝ᵥ c) (y ⬝ᵥ c) hdd]


private lemma ggQ2x_conj_refl {n : ℕ} (b : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (hb : ∀ x y, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y)
    (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    b * ggBCRefl c hc * b.symm = ggBCRefl (b c) (by rw [hb]; exact hc) := by
  have hbc : (b c) ⬝ᵥ (b c) = c ⬝ᵥ c := hb c c
  ext v
  have hbv : (b c) ⬝ᵥ v = c ⬝ᵥ (b.symm v) := by
    conv_lhs => rw [← LinearEquiv.apply_symm_apply b v]
    rw [hb c (b.symm v)]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2x_refl_apply, ggQ2x_refl_apply,
    map_add, map_smul, LinearEquiv.apply_symm_apply]
  rw [hbc, hbv]


private lemma ggQ2x_single_smul {n : ℕ} (i : Fin n) (c : ZMod 3) :
    c • Pi.single i (1 : ZMod 3) = Pi.single i c := by
  ext j
  by_cases hj : j = i
  · subst hj; simp
  · simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj]

private noncomputable def ggQ2x_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    GGBCV n ≃ₗ[ZMod 3] GGBCV n where
  toFun v j := v (σ.symm j)
  invFun v j := v (σ j)
  map_add' x y := by ext j; simp [add_comm]
  map_smul' c x := by ext j; simp
  left_inv v := by ext j; simp
  right_inv v := by ext j; simp

@[simp] private lemma ggQ2x_perm_apply {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : GGBCV n)
    (j : Fin n) : ggQ2x_perm σ v j = v (σ.symm j) := rfl

private lemma ggQ2x_perm_single {n : ℕ} (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    ggQ2x_perm σ (Pi.single i (1 : ZMod 3)) = Pi.single (σ i) (1 : ZMod 3) := by
  ext j
  simp only [ggQ2x_perm_apply, Pi.single_apply]
  by_cases h : σ.symm j = i
  · rw [if_pos h, if_pos]
    rw [← h, Equiv.apply_symm_apply]
  · rw [if_neg h, if_neg]
    intro hj
    exact h (by rw [hj, Equiv.symm_apply_apply])

private lemma ggQ2x_perm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    ggQ2x_perm (σ * τ) = ggQ2x_perm σ * ggQ2x_perm τ := by
  ext v j
  simp only [ggQ2x_perm_apply, LinearEquiv.mul_apply]
  have h : (σ * τ).symm = τ.symm * σ.symm := mul_inv_rev σ τ
  rw [h]
  rfl


private lemma ggQ2x_sub_single_eq {n : ℕ} (x y : Fin n) :
    (Pi.single x (1 : ZMod 3) - Pi.single y 1 : GGBCV n) =
      Pi.single x (1 : ZMod 3) + Pi.single y (M := fun _ => ZMod 3) (-1) := by
  ext j
  simp only [Pi.sub_apply, Pi.add_apply, Pi.single_apply]
  split_ifs <;> decide

private lemma ggQ2x_dot_sub_single_left {n : ℕ} (x y : Fin n) (v : GGBCV n) :
    (Pi.single x (1 : ZMod 3) - Pi.single y 1) ⬝ᵥ v = v x - v y := by
  rw [sub_dotProduct, single_dotProduct, single_dotProduct]
  simp

private lemma ggQ2x_dot_sub_single {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    ((Pi.single x (1 : ZMod 3) - Pi.single y 1 : GGBCV n)) ⬝ᵥ
      (Pi.single x (1 : ZMod 3) - Pi.single y 1) = (2 : ZMod 3) := by
  rw [ggQ2x_sub_single_eq, ggQ2x_dot_two_single x y 1 (-1) hxy]
  decide

private lemma ggQ2x_dot_sub_single_ne {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    ((Pi.single x (1 : ZMod 3) - Pi.single y 1 : GGBCV n)) ⬝ᵥ
      (Pi.single x (1 : ZMod 3) - Pi.single y 1) ≠ 0 := by
  rw [ggQ2x_dot_sub_single x y hxy]; decide

private lemma ggQ2x_sub_single_apply {n : ℕ} (x y j : Fin n) :
    (Pi.single x (1 : ZMod 3) - Pi.single y 1 : GGBCV n) j =
      (if j = x then 1 else 0) - (if j = y then 1 else 0) := by
  simp [Pi.sub_apply, Pi.single_apply]

private lemma ggQ2x_swap_scalar_left :
    ∀ a b : ZMod 3, b = a + (2 * (a - b)) * 1 := by decide

private lemma ggQ2x_swap_scalar_right :
    ∀ a b : ZMod 3, a = b + (2 * (a - b)) * (-1) := by decide

private lemma ggQ2x_perm_swap {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    ggQ2x_perm (Equiv.swap x y) =
      ggBCRefl (Pi.single x 1 - Pi.single y 1) (ggQ2x_dot_sub_single_ne x y hxy) := by
  ext v j
  rw [ggQ2x_perm_apply, ggQ2x_refl_apply, ggQ2x_dot_sub_single x y hxy,
    ggQ2x_dot_sub_single_left x y v, Pi.add_apply, Pi.smul_apply,
    ggQ2x_sub_single_apply x y j]
  rw [Equiv.symm_swap]
  by_cases hx : j = x
  · rw [hx, Equiv.swap_apply_left, if_pos rfl, if_neg hxy]
    exact ggQ2x_swap_scalar_left (v x) (v y)
  · by_cases hy : j = y
    · rw [hy, Equiv.swap_apply_right, if_neg (Ne.symm hxy), if_pos rfl]
      exact ggQ2x_swap_scalar_right (v x) (v y)
    · rw [Equiv.swap_apply_of_ne_of_ne hx hy, if_neg hx, if_neg hy]
      simp


private lemma ggQ2x_wt_two_single {n : ℕ} (x y : Fin n) (a b : ZMod 3) (hxy : x ≠ y)
    (ha : a ≠ 0) (hb : b ≠ 0) :
    ggBCWt (Pi.single x a + Pi.single y b : GGBCV n) = 2 := by
  unfold ggBCWt
  have hset : Finset.univ.filter
      (fun k => (Pi.single x a + Pi.single y b : GGBCV n) k ≠ 0) = {x, y} := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · intro hk
      by_contra h
      push Not at h
      exact hk (by
        rw [Pi.add_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) h.1 a,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) h.2 b, zero_add])
    · rintro (rfl | rfl)
      · rw [Pi.add_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hxy b, add_zero]
        exact ha
      · rw [Pi.add_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hxy) a,
          Pi.single_eq_same, zero_add]
        exact hb
  rw [hset]
  simp [hxy]

private lemma ggQ2x_wt_sub_single {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    ggBCWt (Pi.single x (1 : ZMod 3) - Pi.single y 1) = 2 := by
  rw [ggQ2x_sub_single_eq]
  exact ggQ2x_wt_two_single x y 1 (-1) hxy one_ne_zero (by decide)

private lemma ggQ2x_sub_single_mem_roots {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    (Pi.single x (1 : ZMod 3) - Pi.single y 1 : GGBCV n) ∈ ggBCRoots n := by
  rw [ggBCRoots]
  simp only [Set.mem_setOf_eq]
  rw [ggQ2x_wt_sub_single x y hxy]
  decide

private lemma ggQ2x_perm_swap_mem_W {n : ℕ} (x y : Fin n) (hxy : x ≠ y) :
    ggQ2x_perm (Equiv.swap x y) ∈ ggBCW n := by
  rw [ggQ2x_perm_swap x y hxy]
  exact Subgroup.subset_closure
    ⟨_, ggQ2x_sub_single_mem_roots x y hxy, ggQ2x_dot_sub_single_ne x y hxy, rfl⟩

private lemma ggQ2x_perm_one {n : ℕ} : ggQ2x_perm (1 : Equiv.Perm (Fin n)) = 1 := by
  ext v j
  rfl

private lemma ggQ2x_perm_mem_W {n : ℕ} (σ : Equiv.Perm (Fin n)) : ggQ2x_perm σ ∈ ggBCW n := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · rw [ggQ2x_perm_one]; exact (ggBCW n).one_mem
  · intro f x y hxy hf
    rw [ggQ2x_perm_mul]
    exact mul_mem (ggQ2x_perm_swap_mem_W x y hxy) hf


private lemma ggQ2x_two_eq_neg_one : (2 : ZMod 3) = -1 := rfl

private lemma ggQ2x_zero_eq_neg_zero : (0 : ZMod 3) = -0 := rfl

private lemma ggQ2x_short_ne {n : ℕ} (i : Fin n) :
    (Pi.single i (1 : ZMod 3) : GGBCV n) ⬝ᵥ (Pi.single i (1 : ZMod 3)) ≠ 0 := by
  rw [ggQ2x_dot_single_self]; decide

private noncomputable def ggQ2x_short {n : ℕ} (i : Fin n) : GGBCV n ≃ₗ[ZMod 3] GGBCV n :=
  ggBCRefl (Pi.single i (1 : ZMod 3)) (ggQ2x_short_ne i)

private lemma ggQ2x_short_apply {n : ℕ} (i : Fin n) (v : GGBCV n) :
    ggQ2x_short i v = v + (v i) • Pi.single i (1 : ZMod 3) := by
  rw [ggQ2x_short, ggQ2x_refl_apply, ggQ2x_dot_single_self, single_one_dotProduct]
  rw [one_mul, one_mul]

private lemma ggQ2x_short_apply_self {n : ℕ} (i : Fin n) :
    ggQ2x_short i (Pi.single i (1 : ZMod 3)) = - Pi.single i (1 : ZMod 3) := by
  rw [ggQ2x_short_apply, Pi.single_eq_same, one_smul]
  ext j
  rw [Pi.add_apply, Pi.neg_apply]
  by_cases hj : j = i
  · subst hj; rw [Pi.single_eq_same]; exact ggQ2x_two_eq_neg_one
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hj, zero_add]; exact ggQ2x_zero_eq_neg_zero

private lemma ggQ2x_short_apply_of_ne {n : ℕ} (i j : Fin n) (hij : j ≠ i) :
    ggQ2x_short i (Pi.single j (1 : ZMod 3)) = Pi.single j (1 : ZMod 3) := by
  rw [ggQ2x_short_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij),
    zero_smul, add_zero]

private lemma ggQ2x_short_commute {n : ℕ} (i j : Fin n) :
    Commute (ggQ2x_short i) (ggQ2x_short j) := by
  by_cases hij : i = j
  · subst hij; exact Commute.refl _
  · have hji : j ≠ i := Ne.symm hij
    apply LinearEquiv.ext; intro v
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
    have hi : (ggQ2x_short j v) i = v i := by
      rw [ggQ2x_short_apply]
      simp [Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hji)]
    have hj : (ggQ2x_short i v) j = v j := by
      rw [ggQ2x_short_apply]
      simp [Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hij)]
    calc ggQ2x_short i (ggQ2x_short j v)
        = ggQ2x_short j v + ((ggQ2x_short j v) i) • Pi.single i (1 : ZMod 3) :=
          ggQ2x_short_apply i _
      _ = (v + (v j) • Pi.single j (1 : ZMod 3)) + (v i) • Pi.single i 1 := by
          rw [hi, ggQ2x_short_apply j v]
      _ = (v + (v i) • Pi.single i (1 : ZMod 3)) + (v j) • Pi.single j 1 := by abel
      _ = ggQ2x_short i v + ((ggQ2x_short i v) j) • Pi.single j (1 : ZMod 3) := by
          rw [hj, ggQ2x_short_apply i v]
      _ = ggQ2x_short j (ggQ2x_short i v) := (ggQ2x_short_apply j _).symm

private lemma ggQ2x_neg_one_mul : ∀ a : ZMod 3, (-1 : ZMod 3) * a = -a := by decide

private lemma ggQ2x_neg_one_mul_neg : ∀ a : ZMod 3, (-1 : ZMod 3) * (-a) = a := by decide

private lemma ggQ2x_neg_one_smul {n : ℕ} (x : GGBCV n) :
    (-1 : ZMod 3) • x = -x := by
  ext i
  rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact ggQ2x_neg_one_mul (x i)

private lemma ggQ2x_neg_one_smul_neg {n : ℕ} (x : GGBCV n) :
    (-1 : ZMod 3) • (-x) = x := by
  ext i
  rw [Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  exact ggQ2x_neg_one_mul_neg (x i)

private lemma ggQ2x_diag_mem_W_aux {n : ℕ} (k : ℕ) :
    ∀ (S : Finset (Fin n)) (b : GGBCV n ≃ₗ[ZMod 3] GGBCV n),
      S.card ≤ k →
      (∀ j, b (Pi.single j (1 : ZMod 3)) =
        (if j ∈ S then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3)) →
      b ∈ ggBCW n := by
  induction k with
  | zero =>
    intro S b hk hb
    have hScard : S.card = 0 := Nat.eq_zero_of_le_zero hk
    have hS : S = ∅ := Finset.card_eq_zero.mp hScard
    subst hS
    have hb1 : b = 1 := by
      apply (Pi.basisFun (ZMod 3) (Fin n)).ext'
      intro j
      rw [Pi.basisFun_apply, hb j]
      simp
    rw [hb1]; exact (ggBCW n).one_mem
  | succ k ih =>
    intro S b hk hb
    by_cases hle : S.card ≤ k
    · exact ih S b hle hb
    · have hpos : 0 < S.card := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp hpos
      have hcard : (S.erase i).card ≤ k := by
        rw [Finset.card_erase_of_mem hi]; omega
      have hb' : ∀ j, (ggQ2x_short i * b) (Pi.single j (1 : ZMod 3)) =
          (if j ∈ S.erase i then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3) := by
        intro j
        rw [LinearEquiv.mul_apply, hb j, map_smul]
        by_cases hji : j = i
        · subst hji
          rw [if_pos hi, ggQ2x_short_apply_self, if_neg (by simp)]
          calc (-1 : ZMod 3) • (-Pi.single j (1 : ZMod 3)) = Pi.single j 1 :=
                ggQ2x_neg_one_smul_neg _
            _ = (1 : ZMod 3) • Pi.single j (1 : ZMod 3) := (one_smul _ _).symm
        · rw [ggQ2x_short_apply_of_ne i j hji]
          by_cases hjS : j ∈ S
          · rw [if_pos hjS, if_pos (by rw [Finset.mem_erase]; exact ⟨hji, hjS⟩)]
          · rw [if_neg hjS, if_neg (by rw [Finset.mem_erase]; exact fun h => hjS h.2)]
      have hmem : ggQ2x_short i * b ∈ ggBCW n := ih (S.erase i) (ggQ2x_short i * b) hcard hb'
      have hshort : ggQ2x_short i ∈ ggBCW n := by
        rw [ggQ2x_short]
        exact Subgroup.subset_closure
          ⟨_, (by
            rw [ggBCRoots]
            simp only [Set.mem_setOf_eq]
            rw [ggQ2x_wt_single_of_ne_zero i 1 one_ne_zero]
            decide), ggQ2x_short_ne i, rfl⟩
      have hb_eq : b = (ggQ2x_short i)⁻¹ * (ggQ2x_short i * b) := by
        group
      rw [hb_eq]
      exact mul_mem (inv_mem hshort) hmem

private lemma ggQ2x_diag_mem_W {n : ℕ} (S : Finset (Fin n))
    (b : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (hb : ∀ j, b (Pi.single j (1 : ZMod 3)) =
      (if j ∈ S then (-1 : ZMod 3) else 1) • Pi.single j (1 : ZMod 3)) :
    b ∈ ggBCW n :=
  ggQ2x_diag_mem_W_aux S.card S b le_rfl hb




private lemma ggQ2x_sq_eq_one : ∀ e : ZMod 3, e ≠ 0 → e * e = 1 := by decide

private lemma ggQ2x_two_ne_zero : (2 : ZMod 3) ≠ 0 := by decide

private lemma ggQ2x_eq_one_or_neg_one : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide

private lemma ggQ2x_one_ne_neg_one : (1 : ZMod 3) ≠ -1 := by decide

private lemma ggQ2x_dad : ∀ d a : ZMod 3, d * d = 1 → (d * a) * d = a := by decide

private lemma ggQ2x_dot_single_ne {n : ℕ} (m : Fin n) (d : ZMod 3) (hd : d ≠ 0) :
    (Pi.single m d : GGBCV n) ⬝ᵥ Pi.single m d ≠ 0 := by
  rw [ggQ2x_dot_single_self]
  exact (by decide : ∀ z : ZMod 3, z ≠ 0 → z * z ≠ 0) d hd

private lemma ggQ2x_refl_single {n : ℕ} {c : GGBCV n} (hc : c ⬝ᵥ c ≠ 0) (k : Fin n) :
    ggBCRefl c hc (Pi.single k (1 : ZMod 3)) =
      Pi.single k (1 : ZMod 3) + ((c ⬝ᵥ c) * (c k)) • c := by
  rw [ggQ2x_refl_apply, dotProduct_single_one]

private lemma ggQ2x_two_mul_ne : ∀ e f : ZMod 3, e ≠ 0 → f ≠ 0 → (2 * e) * f ≠ 0 := by
  decide

private lemma ggQ2x_refl_single_mono {n : ℕ} {c : GGBCV n} (hc : c ⬝ᵥ c ≠ 0)
    (hroot : c ∈ ggBCRoots n) (k : Fin n) :
    ∃ m d, d ≠ 0 ∧ ggBCRefl c hc (Pi.single k (1 : ZMod 3)) = Pi.single m d := by
  have hw1 : 1 ≤ ggBCWt c := hroot.1
  have hw2 : ggBCWt c ≤ 2 := hroot.2
  rw [ggQ2x_refl_single]
  rcases (by omega : ggBCWt c = 1 ∨ ggBCWt c = 2) with hw | hw
  · obtain ⟨p, e, he, rfl⟩ := ggQ2x_wt_eq_one_iff.mp hw
    have he2 : e * e = 1 := ggQ2x_sq_eq_one e he
    rw [ggQ2x_dot_single_self]
    by_cases hkp : k = p
    · rw [hkp]
      refine ⟨p, 2, by decide, ?_⟩
      rw [Pi.single_eq_same, show (e * e) * e = e from by rw [he2, one_mul],
        ← ggQ2x_single_smul p e, smul_smul, he2, one_smul]
      rw [← Pi.single_add, show (1 : ZMod 3) + 1 = 2 from rfl]
    · refine ⟨k, 1, one_ne_zero, ?_⟩
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkp, mul_zero, zero_smul, add_zero]
  · obtain ⟨p, q, e, f, hpq, he, hf, rfl⟩ := ggQ2x_wt_two hw
    have he2 : e * e = 1 := ggQ2x_sq_eq_one e he
    rw [ggQ2x_dot_two_single p q e f hpq, ggQ2x_two_ss e f he hf]
    by_cases hkp : k = p
    · rw [hkp]
      refine ⟨q, (2 * e) * f, ggQ2x_two_mul_ne e f he hf, ?_⟩
      rw [Pi.add_apply, Pi.single_eq_same,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hpq, add_zero,
        ← ggQ2x_single_smul p e, ← ggQ2x_single_smul q f]
      rw [smul_add, smul_smul, smul_smul,
        show (2 * e) * e = 2 from by rw [mul_assoc, he2, mul_one],
        show (2 : ZMod 3) = 1 + 1 from rfl,
        show (1 : ZMod 3) + 1 = -1 from rfl,
        ggQ2x_neg_one_smul,
        ← ggQ2x_single_smul q ((-1) * e * f)]
      abel
    · by_cases hkq : k = q
      · rw [hkq]
        refine ⟨p, (2 * f) * e, ggQ2x_two_mul_ne f e hf he, ?_⟩
        rw [Pi.add_apply,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hpq), zero_add,
          Pi.single_eq_same, ← ggQ2x_single_smul p e, ← ggQ2x_single_smul q f]
        rw [smul_add, smul_smul, smul_smul,
          show (2 * f) * f = 2 from by rw [mul_assoc, ggQ2x_sq_eq_one f hf, mul_one],
          show (2 : ZMod 3) = 1 + 1 from rfl,
          show (1 : ZMod 3) + 1 = -1 from rfl,
          ggQ2x_neg_one_smul,
          ← ggQ2x_single_smul p ((-1) * f * e)]
        abel
      · refine ⟨k, 1, one_ne_zero, ?_⟩
        rw [Pi.add_apply, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkp,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hkq, add_zero, mul_zero, zero_smul,
          add_zero]

private lemma ggQ2x_short_eq_refl {n : ℕ} (m : Fin n) (d : ZMod 3) (hd : d ≠ 0)
    (hc : (Pi.single m d : GGBCV n) ⬝ᵥ Pi.single m d ≠ 0) :
    ggBCRefl (Pi.single m d) hc = ggQ2x_short m := by
  ext v j
  rw [ggQ2x_refl_apply, ggQ2x_short_apply]
  have hd2 : d * d = 1 := ggQ2x_sq_eq_one d hd
  have hdd : (Pi.single m d : GGBCV n) ⬝ᵥ (Pi.single m d) = 1 := by
    rw [ggQ2x_dot_single_self, hd2]
  have hdv : (Pi.single m d : GGBCV n) ⬝ᵥ v = d * v m := by
    rw [single_dotProduct]
  rw [hdd, hdv, one_mul, Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply]
  by_cases hjm : j = m
  · rw [hjm]
    rw [Pi.single_eq_same, Pi.single_eq_same]
    simp only [smul_eq_mul]
    rw [ggQ2x_dad d (v m) hd2, mul_one]
  · rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjm,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) hjm]
    simp

private lemma ggQ2x_short_mem_W {n : ℕ} (k : Fin n) : ggQ2x_short k ∈ ggBCW n := by
  rw [ggQ2x_short]
  exact Subgroup.subset_closure
    ⟨_, (by
      rw [ggBCRoots]
      simp only [Set.mem_setOf_eq]
      rw [ggQ2x_wt_single_of_ne_zero k 1 one_ne_zero]
      decide), ggQ2x_short_ne k, rfl⟩

private lemma ggQ2x_inv_self_of_isRefl {n : ℕ} {x : GGBCV n ≃ₗ[ZMod 3] GGBCV n}
    (hx : IsReflLin x) : x⁻¹ = x := by
  obtain ⟨cc, φ, h, rfl⟩ := hx
  exact Module.reflection_inv h

private lemma ggQ2x_refl_isRefl {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    IsReflLin (ggBCRefl c hc) := by
  refine ⟨c, (2 / (c ⬝ᵥ c)) • ggBCDot c, ?_, rfl⟩
  change (2 / (c ⬝ᵥ c)) • (ggBCDot c c) = 2
  rw [ggQ2x_dot_eq]
  change (2 / (c ⬝ᵥ c)) * (c ⬝ᵥ c) = 2
  field_simp

private lemma ggQ2x_short_isRefl {n : ℕ} (k : Fin n) : IsReflLin (ggQ2x_short k) := by
  rw [ggQ2x_short]
  exact ggQ2x_refl_isRefl _ _

private lemma ggQ2x_conj_reflection {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]
    (a : V ≃ₗ[ZMod 3] V) {ψ : Module.Dual (ZMod 3) V} {cc : V} (h : ψ cc = 2) :
    a * Module.reflection h * a.symm =
      Module.reflection (show (ψ.comp (a.symm : V →ₗ[ZMod 3] V)) (a cc) = 2 by
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
        exact h) := by
  ext w
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply,
    Module.reflection_apply (a.symm w) h, Module.reflection_apply w]
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private lemma ggQ2x_isReflLin_conj {n : ℕ} {t : GGBCV n ≃ₗ[ZMod 3] GGBCV n}
    (ht : IsReflLin t) (b : GGBCV n ≃ₗ[ZMod 3] GGBCV n) :
    IsReflLin (b * t * b.symm) := by
  obtain ⟨cc, ψ, hψ, rfl⟩ := ht
  refine ⟨b cc, ψ.comp (b.symm : GGBCV n →ₗ[ZMod 3] GGBCV n), ?_, ?_⟩
  · change ψ (b.symm (b cc)) = 2
    rw [LinearEquiv.symm_apply_apply]
    exact hψ
  · exact ggQ2x_conj_reflection b hψ

private lemma ggQ2x_perm_isometry {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    ∀ x y : GGBCV n, (ggQ2x_perm σ x) ⬝ᵥ (ggQ2x_perm σ y) = x ⬝ᵥ y := by
  intro x y
  have hx : ggQ2x_perm σ x = x ∘ σ.symm := by ext j; rfl
  have hy : ggQ2x_perm σ y = y ∘ σ.symm := by ext j; rfl
  rw [hx, hy, dotProduct, dotProduct]
  exact Equiv.sum_comp σ.symm (fun i => x i * y i)

private lemma ggQ2x_short_isometry {n : ℕ} (k : Fin n) :
    ∀ x y : GGBCV n, (ggQ2x_short k x) ⬝ᵥ (ggQ2x_short k y) = x ⬝ᵥ y := by
  intro x y
  rw [ggQ2x_short]
  exact ggQ2x_refl_isometry _ _ x y

private lemma ggQ2x_isometry_mul {n : ℕ} {b c : GGBCV n ≃ₗ[ZMod 3] GGBCV n}
    (hb : ∀ x y, (b x) ⬝ᵥ (b y) = x ⬝ᵥ y)
    (hc : ∀ x y, (c x) ⬝ᵥ (c y) = x ⬝ᵥ y) :
    ∀ x y, ((b * c) x) ⬝ᵥ ((b * c) y) = x ⬝ᵥ y := by
  intro x y
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hb, hc]

private lemma ggQ2x_isometry_one {n : ℕ} :
    ∀ x y : GGBCV n, ((1 : GGBCV n ≃ₗ[ZMod 3] GGBCV n) x) ⬝ᵥ
      ((1 : GGBCV n ≃ₗ[ZMod 3] GGBCV n) y) = x ⬝ᵥ y := by
  intro x y; rfl

private lemma ggQ2x_refl_proof_irrel {n : ℕ} (c : GGBCV n)
    (h1 h2 : c ⬝ᵥ c ≠ 0) : ggBCRefl c h1 = ggBCRefl c h2 := by
  ext v
  rfl

private lemma ggQ2x_add_self : ∀ a : ZMod 3, a + a = -a := by decide

private lemma ggQ2x_add_self_vec {n : ℕ} (c : GGBCV n) : c + c = -c := by
  ext m
  exact ggQ2x_add_self (c m)

private lemma ggQ2x_scalar_eigen : ∀ x mu c : ZMod 3, x + mu * c = -x → x = mu * c := by
  decide

private lemma ggQ2x_refl_self_neg {n : ℕ} (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0) :
    ggBCRefl c hc c = -c := by
  rw [ggQ2x_refl_apply]
  rw [show (c ⬝ᵥ c) * (c ⬝ᵥ c) = 1 from ggQ2x_sq_eq_one _ hc, one_smul]
  exact ggQ2x_add_self_vec c

private lemma ggQ2x_refl_eigen_neg {n : ℕ} (c x : GGBCV n) (hc : c ⬝ᵥ c ≠ 0)
    (h : ggBCRefl c hc x = -x) : ∃ lam : ZMod 3, x = lam • c := by
  refine ⟨(c ⬝ᵥ c) * (c ⬝ᵥ x), ?_⟩
  ext m
  have hm := congrArg (fun w : GGBCV n => w m) h
  rw [ggQ2x_refl_apply, Pi.add_apply, Pi.smul_apply, Pi.neg_apply] at hm
  exact ggQ2x_scalar_eigen (x m) ((c ⬝ᵥ c) * (c ⬝ᵥ x)) (c m) hm

private lemma ggQ2x_center_ne {n : ℕ} (i k : Fin n) (hik : k ≠ i) (ε : ZMod 3)
    (hε : ε ≠ 0) :
    (Pi.single i (1 : ZMod 3) + Pi.single k ε : GGBCV n) ⬝ᵥ
      (Pi.single i 1 + Pi.single k ε) ≠ 0 := by
  rw [ggQ2x_dot_two_single i k 1 ε (Ne.symm hik), ggQ2x_two_ss 1 ε one_ne_zero hε]
  exact ggQ2x_two_ne_zero

private lemma ggQ2x_center_inj {n : ℕ} (i k k' : Fin n) (ε ε' : ZMod 3)
    (hik : k ≠ i) (hik' : k' ≠ i) (hε : ε ≠ 0) (hε' : ε' ≠ 0)
    (hc1 : (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
      Pi.single k (M := fun _ => ZMod 3) ε : GGBCV n) ⬝ᵥ
      (Pi.single i (M := fun _ => ZMod 3) 1 + Pi.single k (M := fun _ => ZMod 3) ε) ≠ 0)
    (hc2 : (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
      Pi.single k' (M := fun _ => ZMod 3) ε' : GGBCV n) ⬝ᵥ
      (Pi.single i (M := fun _ => ZMod 3) 1 + Pi.single k' (M := fun _ => ZMod 3) ε') ≠ 0)
    (h : ggBCRefl (Pi.single i (M := fun _ => ZMod 3) 1 +
        Pi.single k (M := fun _ => ZMod 3) ε) hc1 =
      ggBCRefl (Pi.single i (M := fun _ => ZMod 3) 1 +
        Pi.single k' (M := fun _ => ZMod 3) ε') hc2) :
    k = k' ∧ ε = ε' := by
  have hself : ggBCRefl (Pi.single i (M := fun _ => ZMod 3) 1 +
      Pi.single k (M := fun _ => ZMod 3) ε) hc1
      (Pi.single i (M := fun _ => ZMod 3) 1 + Pi.single k (M := fun _ => ZMod 3) ε) =
      -(Pi.single i (1 : ZMod 3) + Pi.single k ε) := ggQ2x_refl_self_neg _ hc1
  have heig : ggBCRefl (Pi.single i (M := fun _ => ZMod 3) 1 +
      Pi.single k' (M := fun _ => ZMod 3) ε') hc2
      (Pi.single i (M := fun _ => ZMod 3) 1 + Pi.single k (M := fun _ => ZMod 3) ε) =
      -(Pi.single i (1 : ZMod 3) + Pi.single k ε) := by
    rw [← h]
    exact hself
  obtain ⟨lam, hlam⟩ := ggQ2x_refl_eigen_neg _ _ hc2 heig
  have hli : lam = 1 := by
    have := congrArg (fun w : GGBCV n => w i) hlam
    rw [Pi.smul_apply, Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hik), add_zero,
      Pi.add_apply, Pi.single_eq_same,
      Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hik'), add_zero, smul_eq_mul,
      mul_one] at this
    exact this.symm
  have hd : (Pi.single i (1 : ZMod 3) + Pi.single k ε : GGBCV n) =
      Pi.single i (1 : ZMod 3) + Pi.single k' ε' := by
    rw [hlam, hli, one_smul]
  have hcancel : (Pi.single k ε : GGBCV n) = Pi.single k' ε' := by
    have := congrArg (fun w : GGBCV n => w - Pi.single i (1 : ZMod 3)) hd
    simpa [add_sub_cancel_left] using this
  have hk : k = k' := by
    by_contra hne
    have := congrArg (fun w : GGBCV n => w k) hcancel
    rw [Pi.single_eq_same, Pi.single_eq_of_ne (M := fun _ => ZMod 3) hne] at this
    exact hε this
  subst hk
  refine ⟨rfl, ?_⟩
  have := congrArg (fun w : GGBCV n => w k) hcancel
  rwa [Pi.single_eq_same, Pi.single_eq_same] at this

private lemma ggQ2x_S1 {n : ℕ} (hn : 3 ≤ n) (a : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (ha : a ∈ Subgroup.normalizer (ggBCW n : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)))
    (k : Fin n) :
    a * ggQ2x_short k * a⁻¹ ∈ ggBCReflSet (ggBCRoots n) := by
  have hW : a * ggQ2x_short k * a⁻¹ ∈ ggBCW n :=
    ((Subgroup.mem_set_normalizer_iff.mp ha) (ggQ2x_short k)).mp (ggQ2x_short_mem_W k)
  have hR : IsReflLin (a * ggQ2x_short k * a⁻¹) :=
    ggQ2x_isReflLin_conj (ggQ2x_short_isRefl k) a
  exact ggQ2_bc_W_refl n hn _ hW hR

private lemma ggQ2x_mul_div (v ε : ZMod 3) (hv : v ≠ 0) : v * (ε / v) = ε := by
  field_simp

private lemma ggQ2x_perm_swap_apply_left {n : ℕ} (j k : Fin n) :
    ggQ2x_perm (Equiv.swap j k) (Pi.single j (1 : ZMod 3)) = Pi.single k 1 := by
  rw [ggQ2x_perm_single, Equiv.swap_apply_left]

private lemma ggQ2x_perm_swap_apply_of_ne {n : ℕ} (i j k : Fin n) (hij : i ≠ j)
    (hik : i ≠ k) :
    ggQ2x_perm (Equiv.swap j k) (Pi.single i (1 : ZMod 3)) = Pi.single i 1 := by
  rw [ggQ2x_perm_single, Equiv.swap_apply_of_ne_of_ne hij hik]

private lemma ggQ2x_short_or_one_self {n : ℕ} (i : Fin n) (u : ZMod 3) (hu : u ≠ 0) :
    (if u = -1 then ggQ2x_short i else 1) (Pi.single i (1 : ZMod 3)) =
      u • Pi.single i 1 := by
  by_cases h : u = -1
  · rw [if_pos h, ggQ2x_short_apply_self, h]
    exact (ggQ2x_neg_one_smul (Pi.single i (1 : ZMod 3))).symm
  · rw [if_neg h]
    rw [show u = 1 from by
      rcases ggQ2x_eq_one_or_neg_one u hu with h1 | h2
      · exact h1
      · exact absurd h2 h]
    rw [one_smul]; rfl

private lemma ggQ2x_short_or_one_ne {n : ℕ} (i k : Fin n) (hki : k ≠ i) (u : ZMod 3) :
    (if u = -1 then ggQ2x_short i else 1) (Pi.single k (1 : ZMod 3)) = Pi.single k 1 := by
  by_cases h : u = -1
  · rw [if_pos h]; exact ggQ2x_short_apply_of_ne i k hki
  · rw [if_neg h]; rfl

private lemma ggQ2x_S2a {n : ℕ} (w : GGBCV n ≃ₗ[ZMod 3] GGBCV n) (hw : w ∈ ggBCW n)
    (k : Fin n) :
    ∃ m, w * ggQ2x_short k * w⁻¹ = ggQ2x_short m := by
  have hgen : ∀ x ∈ ggBCReflSet (ggBCRoots n), ∀ k : Fin n, ∃ m,
      x * ggQ2x_short k * x⁻¹ = ggQ2x_short m := by
    rintro x ⟨cc, hcroot, hcx, rfl⟩ k
    obtain ⟨m, d, hd, hfm⟩ := ggQ2x_refl_single_mono hcx hcroot k
    refine ⟨m, ?_⟩
    change ggBCRefl cc hcx * ggBCRefl (Pi.single k (1 : ZMod 3)) (ggQ2x_short_ne k) *
      (ggBCRefl cc hcx).symm = ggQ2x_short m
    rw [ggQ2x_conj_refl (ggBCRefl cc hcx) (ggQ2x_refl_isometry cc hcx)
      (Pi.single k (1 : ZMod 3)) (ggQ2x_short_ne k)]
    simp only [hfm]
    exact ggQ2x_short_eq_refl m d hd _
  rw [ggBCW] at hw
  refine Subgroup.closure_induction_left
    (p := fun w _ => ∀ k : Fin n, ∃ m, w * ggQ2x_short k * w⁻¹ = ggQ2x_short m)
    ?_ ?_ ?_ hw k
  · intro k
    exact ⟨k, by rw [one_mul, inv_one, mul_one]⟩
  · intro x hx y hy hpy k
    obtain ⟨m, hm⟩ := hpy k
    obtain ⟨m', hm'⟩ := hgen x hx m
    refine ⟨m', ?_⟩
    rw [mul_inv_rev]
    calc x * y * ggQ2x_short k * y⁻¹ * x⁻¹
        = x * (y * ggQ2x_short k * y⁻¹) * x⁻¹ := by group
      _ = x * ggQ2x_short m * x⁻¹ := by rw [hm]
      _ = ggQ2x_short m' := hm'
  · intro x hx y hy hpy k
    have hxi : x⁻¹ = x := by
      obtain ⟨cc, hcroot, hcx, rfl⟩ := hx
      exact ggQ2x_inv_self_of_isRefl (ggQ2x_refl_isRefl cc hcx)
    rw [hxi]
    obtain ⟨m, hm⟩ := hpy k
    obtain ⟨m', hm'⟩ := hgen x hx m
    refine ⟨m', ?_⟩
    rw [mul_inv_rev]
    calc x * y * ggQ2x_short k * y⁻¹ * x⁻¹
        = x * (y * ggQ2x_short k * y⁻¹) * x⁻¹ := by group
      _ = x * ggQ2x_short m * x⁻¹ := by rw [hm]
      _ = ggQ2x_short m' := hm'

private lemma ggQ2x_S2b {n : ℕ} (hn : 3 ≤ n) (i j : Fin n) (hij : i ≠ j)
    (u v : ZMod 3) (hu : u ≠ 0) (hv : v ≠ 0)
    (hc : (Pi.single i (M := fun _ => ZMod 3) u +
      Pi.single j (M := fun _ => ZMod 3) v : GGBCV n) ⬝ᵥ
      (Pi.single i (M := fun _ => ZMod 3) u +
        Pi.single j (M := fun _ => ZMod 3) v) ≠ 0)
    (k : Fin n) (hk : k ≠ i) (ε : ZMod 3) (hε : ε ≠ 0)
    (hc' : (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
      Pi.single k (M := fun _ => ZMod 3) ε : GGBCV n) ⬝ᵥ
      (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
        Pi.single k (M := fun _ => ZMod 3) ε) ≠ 0) :
    ∃ w ∈ ggBCW n,
      w * ggBCRefl ((Pi.single i (M := fun _ => ZMod 3) u +
        Pi.single j (M := fun _ => ZMod 3) v : GGBCV n)) hc * w⁻¹ =
        ggBCRefl ((Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
          Pi.single k (M := fun _ => ZMod 3) ε : GGBCV n)) hc' := by
  let A : GGBCV n ≃ₗ[ZMod 3] GGBCV n := if u = -1 then ggQ2x_short i else 1
  let B : GGBCV n ≃ₗ[ZMod 3] GGBCV n := if ε / v = -1 then ggQ2x_short k else 1
  let P : GGBCV n ≃ₗ[ZMod 3] GGBCV n := ggQ2x_perm (Equiv.swap j k)
  let w : GGBCV n ≃ₗ[ZMod 3] GGBCV n := A * B * P
  have hPc : P (Pi.single i u + Pi.single j v) = Pi.single i u + Pi.single k v := by
    change ggQ2x_perm (Equiv.swap j k) (Pi.single i u + Pi.single j v) = _
    rw [map_add, ← ggQ2x_single_smul i u, ← ggQ2x_single_smul j v, map_smul, map_smul,
      ggQ2x_perm_swap_apply_of_ne i j k hij (Ne.symm hk), ggQ2x_perm_swap_apply_left,
      ggQ2x_single_smul, ggQ2x_single_smul]
  have hBc : B (Pi.single i u + Pi.single k v) = Pi.single i u + Pi.single k ε := by
    change (if ε / v = -1 then ggQ2x_short k else 1) (Pi.single i u + Pi.single k v) = _
    rw [map_add, ← ggQ2x_single_smul i u, ← ggQ2x_single_smul k v, map_smul, map_smul,
      ggQ2x_short_or_one_ne k i (Ne.symm hk),
      ggQ2x_short_or_one_self k (ε / v) (div_ne_zero hε hv),
      smul_smul, ggQ2x_mul_div v ε hv, ggQ2x_single_smul, ggQ2x_single_smul]
  have hAc : A (Pi.single i u + Pi.single k ε) = Pi.single i 1 + Pi.single k ε := by
    change (if u = -1 then ggQ2x_short i else 1) (Pi.single i u + Pi.single k ε) = _
    rw [map_add, ← ggQ2x_single_smul i u, ← ggQ2x_single_smul k ε, map_smul, map_smul,
      ggQ2x_short_or_one_self i u hu, ggQ2x_short_or_one_ne i k hk,
      smul_smul, ggQ2x_sq_eq_one u hu, one_smul, ggQ2x_single_smul]
  have hwc : w (Pi.single i u + Pi.single j v) = Pi.single i 1 + Pi.single k ε := by
    change (A * B * P) (Pi.single i u + Pi.single j v) = _
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hPc, hBc, hAc]
  have hA_iso : ∀ x y, (A x) ⬝ᵥ (A y) = x ⬝ᵥ y := by
    intro x y
    change ((if u = -1 then ggQ2x_short i else 1) x) ⬝ᵥ
      ((if u = -1 then ggQ2x_short i else 1) y) = x ⬝ᵥ y
    by_cases h : u = -1
    · rw [if_pos h]; exact ggQ2x_short_isometry i x y
    · rw [if_neg h]; exact ggQ2x_isometry_one x y
  have hB_iso : ∀ x y, (B x) ⬝ᵥ (B y) = x ⬝ᵥ y := by
    intro x y
    change ((if ε / v = -1 then ggQ2x_short k else 1) x) ⬝ᵥ
      ((if ε / v = -1 then ggQ2x_short k else 1) y) = x ⬝ᵥ y
    by_cases h : ε / v = -1
    · rw [if_pos h]; exact ggQ2x_short_isometry k x y
    · rw [if_neg h]; exact ggQ2x_isometry_one x y
  have hP_iso : ∀ x y, (P x) ⬝ᵥ (P y) = x ⬝ᵥ y :=
    ggQ2x_perm_isometry (Equiv.swap j k)
  have hw_iso : ∀ x y, (w x) ⬝ᵥ (w y) = x ⬝ᵥ y := by
    intro x y
    change ((A * B * P) x) ⬝ᵥ ((A * B * P) y) = x ⬝ᵥ y
    exact ggQ2x_isometry_mul (ggQ2x_isometry_mul hA_iso hB_iso) hP_iso x y
  refine ⟨w, ?_, ?_⟩
  · change (if u = -1 then ggQ2x_short i else 1) *
      (if ε / v = -1 then ggQ2x_short k else 1) * ggQ2x_perm (Equiv.swap j k) ∈ ggBCW n
    apply mul_mem
    · apply mul_mem
      · by_cases h : u = -1
        · rw [if_pos h]; exact ggQ2x_short_mem_W i
        · rw [if_neg h]; exact (ggBCW n).one_mem
      · by_cases h : ε / v = -1
        · rw [if_pos h]; exact ggQ2x_short_mem_W k
        · rw [if_neg h]; exact (ggBCW n).one_mem
    · exact ggQ2x_perm_mem_W (Equiv.swap j k)
  · rw [show w⁻¹ = w.symm from rfl, ggQ2x_conj_refl w hw_iso]
    simp only [hwc]

private lemma ggQ2x_S2c {n : ℕ} (hn : 3 ≤ n) (a : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (ha : a ∈ Subgroup.normalizer (ggBCW n : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)))
    (hlong : ∃ (k0 : Fin n) (c : GGBCV n) (hc : c ⬝ᵥ c ≠ 0),
      ggBCWt c = 2 ∧ a * ggQ2x_short k0 * a⁻¹ = ggBCRefl c hc) :
    False := by
  obtain ⟨k0, c0, hc0, hwt0, ht0⟩ := hlong
  obtain ⟨i, j, u, v, hij, hu, hv, hc0eq⟩ := ggQ2x_wt_two hwt0
  cases hc0eq
  classical
  have ha_inv : a⁻¹ ∈ Subgroup.normalizer (ggBCW n : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n)) :=
    inv_mem ha
  have hT : ∀ (k : Fin n) (hk : k ≠ i) (ε : ZMod 3) (hε : ε ≠ 0),
      ∃ m, a * ggQ2x_short m * a⁻¹ =
        ggBCRefl (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
          Pi.single k (M := fun _ => ZMod 3) ε) (ggQ2x_center_ne i k hk ε hε) := by
    intro k hk ε hε
    obtain ⟨w, hwW, hw⟩ := ggQ2x_S2b hn i j hij u v hu hv hc0 k hk ε hε
      (ggQ2x_center_ne i k hk ε hε)
    have hw' : a⁻¹ * w * a ∈ ggBCW n :=
      (Subgroup.mem_set_normalizer_iff.mp ha_inv w).mp hwW
    obtain ⟨m, hm⟩ := ggQ2x_S2a (a⁻¹ * w * a) hw' k0
    refine ⟨m, ?_⟩
    have ht0' : ggBCRefl (Pi.single i (M := fun _ => ZMod 3) u +
        Pi.single j (M := fun _ => ZMod 3) v) hc0 = a * ggQ2x_short k0 * a⁻¹ := ht0.symm
    calc a * ggQ2x_short m * a⁻¹
        = a * ((a⁻¹ * w * a) * ggQ2x_short k0 * (a⁻¹ * w * a)⁻¹) * a⁻¹ := by rw [hm]
      _ = w * (a * ggQ2x_short k0 * a⁻¹) * w⁻¹ := by group
      _ = w * ggBCRefl (Pi.single i (M := fun _ => ZMod 3) u +
            Pi.single j (M := fun _ => ZMod 3) v) hc0 * w⁻¹ := by rw [ht0']
      _ = ggBCRefl (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
            Pi.single k (M := fun _ => ZMod 3) ε) (ggQ2x_center_ne i k hk ε hε) := hw
  let f : {k : Fin n // k ≠ i} × {ε : ZMod 3 // ε ≠ 0} → Fin n := fun q =>
    Classical.choose (hT q.1.1 q.1.2 q.2.1 q.2.2)
  have hf : ∀ q : {k : Fin n // k ≠ i} × {ε : ZMod 3 // ε ≠ 0},
      a * ggQ2x_short (f q) * a⁻¹ =
        ggBCRefl (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
          Pi.single q.1.1 (M := fun _ => ZMod 3) q.2.1)
          (ggQ2x_center_ne i q.1.1 q.1.2 q.2.1 q.2.2) := fun q =>
    Classical.choose_spec (hT q.1.1 q.1.2 q.2.1 q.2.2)
  have hinj : Function.Injective f := by
    intro q q' hq
    have heq : ggBCRefl (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
        Pi.single q.1.1 (M := fun _ => ZMod 3) q.2.1)
        (ggQ2x_center_ne i q.1.1 q.1.2 q.2.1 q.2.2) =
        ggBCRefl (Pi.single i (M := fun _ => ZMod 3) (1 : ZMod 3) +
          Pi.single q'.1.1 (M := fun _ => ZMod 3) q'.2.1)
          (ggQ2x_center_ne i q'.1.1 q'.1.2 q'.2.1 q'.2.2) := by
      rw [← hf q, hq, hf q']
    obtain ⟨hk, he⟩ := ggQ2x_center_inj i q.1.1 q'.1.1 q.2.1 q'.2.1
      q.1.2 q'.1.2 q.2.2 q'.2.2 (ggQ2x_center_ne i q.1.1 q.1.2 q.2.1 q.2.2)
      (ggQ2x_center_ne i q'.1.1 q'.1.2 q'.2.1 q'.2.2) heq
    exact Prod.ext (Subtype.ext hk) (Subtype.ext he)
  have hcard := Fintype.card_le_of_injective f hinj
  have hcard1 : Fintype.card {k : Fin n // k ≠ i} = n - 1 := by
    rw [Fintype.card_subtype_compl (fun k : Fin n => k = i)]
    simp
  have hcard2 : Fintype.card {ε : ZMod 3 // ε ≠ 0} = 2 := by decide
  rw [Fintype.card_prod, hcard1, hcard2, Fintype.card_fin] at hcard
  omega

private lemma ggQ2x_eq_neg_self : ∀ x : ZMod 3, x = -x → x = 0 := by decide

private lemma ggQ2x_S3 {n : ℕ} {a : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (k j : Fin n)
    (h : a * ggQ2x_short k * a⁻¹ = ggQ2x_short j) :
    ∃ lam : ZMod 3, lam ≠ 0 ∧ a (Pi.single k (1 : ZMod 3)) = Pi.single j lam := by
  have hv : ggQ2x_short j (a (Pi.single k (1 : ZMod 3))) = - a (Pi.single k (1 : ZMod 3)) := by
    have h' : a * ggQ2x_short k = ggQ2x_short j * a := by
      have hh := congrArg (fun e => e * a) h
      rw [mul_assoc, mul_assoc, inv_mul_cancel, mul_one] at hh
      exact hh
    have h2 := congrArg (fun e => e (Pi.single k (1 : ZMod 3))) h'
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ggQ2x_short_apply_self] at h2
    rw [show a (-Pi.single k (1 : ZMod 3)) = - a (Pi.single k (1 : ZMod 3)) from by
      rw [show -Pi.single k (1 : ZMod 3) = (-1 : ZMod 3) • Pi.single k 1 from
        (ggQ2x_neg_one_smul _).symm, map_smul, ggQ2x_neg_one_smul]] at h2
    exact h2.symm
  refine ⟨a (Pi.single k (1 : ZMod 3)) j, ?_, ?_⟩
  · intro h0
    have hzero : a (Pi.single k (1 : ZMod 3)) = 0 := by
      ext m
      by_cases hm : m = j
      · rw [hm, Pi.zero_apply]; exact h0
      · have h3 := congrArg (fun w : GGBCV n => w m) hv
        rw [ggQ2x_short_apply, Pi.add_apply, Pi.smul_apply,
          Pi.single_eq_of_ne (M := fun _ => ZMod 3) hm, smul_zero, add_zero,
          Pi.neg_apply] at h3
        exact ggQ2x_eq_neg_self _ h3
    have hsingle : (Pi.single k (1 : ZMod 3) : GGBCV n) ≠ 0 := by
      intro hz
      have := congrFun hz k
      simp at this
    exact hsingle ((LinearEquiv.injective a) (by rw [hzero, map_zero]))
  · ext m
    by_cases hm : m = j
    · rw [hm, Pi.single_eq_same]
    · have h3 := congrArg (fun w : GGBCV n => w m) hv
      rw [ggQ2x_short_apply, Pi.add_apply, Pi.smul_apply,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hm, smul_zero, add_zero,
        Pi.neg_apply] at h3
      rw [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hm]
      exact ggQ2x_eq_neg_self _ h3

private lemma ggQ2x_perm_inv {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    (ggQ2x_perm σ).symm = ggQ2x_perm σ.symm := by
  ext v j
  rfl

private def ggQ2xMono {n : ℕ} (a : GGBCV n ≃ₗ[ZMod 3] GGBCV n) : Prop :=
  ∀ k, ∃ j lam, lam ≠ 0 ∧
    a (Pi.single k (1 : ZMod 3)) = Pi.single j lam

private lemma ggQ2x_S4 {n : ℕ} {a : GGBCV n ≃ₗ[ZMod 3] GGBCV n} (ha : ggQ2xMono a) :
    a ∈ ggBCW n := by
  classical
  choose jf cf hcf hjf using ha
  have hinj : Function.Injective jf := by
    intro i k hik
    by_contra hne
    have h1 : a (Pi.single i 1) = cf i • Pi.single (jf i) 1 := by
      rw [hjf i, ← ggQ2x_single_smul]
    have h2 : a (Pi.single k 1) = cf k • Pi.single (jf i) 1 := by
      rw [hjf k, hik, ← ggQ2x_single_smul]
    have heq : a (cf k • Pi.single i (1 : ZMod 3)) = a (cf i • Pi.single k 1) := by
      rw [map_smul, map_smul, h1, h2]
      exact smul_comm (cf k) (cf i) _
    have heq' : cf k • Pi.single i (1 : ZMod 3) = cf i • Pi.single k 1 :=
      LinearEquiv.injective a heq
    have hthis : cf k = 0 := by
      have h := congrArg (fun v : GGBCV n => v i) heq'
      simpa [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) hne] using h
    exact hcf k hthis
  have hsurj : Function.Surjective jf := Finite.injective_iff_surjective.mp hinj
  let σ : Equiv.Perm (Fin n) := Equiv.ofBijective jf ⟨hinj, hsurj⟩
  have hact : ∀ i, a (Pi.single i (1 : ZMod 3)) = cf i • Pi.single (σ i) 1 := by
    intro i
    rw [hjf i, ← ggQ2x_single_smul]
    rfl
  let P : GGBCV n ≃ₗ[ZMod 3] GGBCV n := ggQ2x_perm σ
  have hP : P ∈ ggBCW n := ggQ2x_perm_mem_W σ
  let b : GGBCV n ≃ₗ[ZMod 3] GGBCV n := a * P.symm
  have hbW : b ∈ ggBCW n := by
    refine ggQ2x_diag_mem_W (Finset.univ.filter (fun k => cf (σ.symm k) = -1)) b ?_
    intro k
    have hPinv : P.symm (Pi.single k (1 : ZMod 3)) = Pi.single (σ.symm k) (1 : ZMod 3) := by
      rw [show P.symm = ggQ2x_perm σ.symm from ggQ2x_perm_inv σ]
      exact ggQ2x_perm_single σ.symm k
    have hbact : b (Pi.single k (1 : ZMod 3)) = cf (σ.symm k) • Pi.single k (1 : ZMod 3) := by
      show (a * P.symm) (Pi.single k 1) = _
      rw [LinearEquiv.mul_apply, hPinv, hact, Equiv.apply_symm_apply]
    rw [hbact]
    rcases ggQ2x_eq_one_or_neg_one (cf (σ.symm k)) (hcf (σ.symm k)) with h1 | hm1
    · rw [h1, one_smul, if_neg, one_smul]
      rw [Finset.mem_filter]
      rintro ⟨-, h⟩
      rw [h1] at h
      exact ggQ2x_one_ne_neg_one h
    · rw [hm1, if_pos]
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hm1⟩
  have hPP : P.symm * P = 1 := by
    ext v
    rw [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]
    rfl
  have ha_eq : a = b * P := by
    show a = (a * P.symm) * P
    rw [mul_assoc, hPP, mul_one]
  rw [ha_eq]
  exact mul_mem hbW hP

theorem ggQ2_bc_normalizer (n : ℕ) (hn : 3 ≤ n) (a : GGBCV n ≃ₗ[ZMod 3] GGBCV n)
    (ha : a ∈ Subgroup.normalizer (ggBCW n : Set (GGBCV n ≃ₗ[ZMod 3] GGBCV n))) : a ∈ ggBCW n := by
  have hmono : ggQ2xMono a := by
    intro k
    obtain ⟨c, hcroot, hc, hceq⟩ := ggQ2x_S1 hn a ha k
    have hw1 : 1 ≤ ggBCWt c := hcroot.1
    have hw2 : ggBCWt c ≤ 2 := hcroot.2
    have hw : ggBCWt c = 1 := by
      by_contra hne
      have hw2' : ggBCWt c = 2 := by omega
      exact ggQ2x_S2c hn a ha ⟨k, c, hc, hw2', hceq⟩
    obtain ⟨m, d, hd, hcd⟩ := ggQ2x_wt_eq_one_iff.mp hw
    have hshort : a * ggQ2x_short k * a⁻¹ = ggQ2x_short m := by
      rw [hceq]
      simp only [hcd]
      exact ggQ2x_short_eq_refl m d hd _
    obtain ⟨lam, hlam, hact⟩ := ggQ2x_S3 k m hshort
    exact ⟨m, lam, hlam, hact⟩
  exact ggQ2x_S4 hmono

end CFSG.StandardType

end
