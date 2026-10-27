module

public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.LieType.BorelTits.CompleteFlag

public section

namespace CFSG.StandardType

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section WittCopy

private def ggPSUFP_herm {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} (x y : Fin n → F) : F := ∑ r, σ (x r) * y r

private theorem ggPSUFP_herm_single_single {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} (a b : Fin n) (x y : F) :
    ggPSUFP_herm σ (Pi.single a x) (Pi.single b y) = if a = b then σ x * y else 0 := by
  unfold ggPSUFP_herm
  split_ifs with hab
  · subst hab
    rw [Finset.sum_eq_single a (fun r _ hr => by simp [Pi.single_eq_of_ne hr]) (by simp)]
    simp
  · refine Finset.sum_eq_zero fun r _ => ?_
    by_cases hr : r = a
    · subst hr; simp [Pi.single_eq_of_ne hab]
    · simp [Pi.single_eq_of_ne hr]

private theorem ggPSUFP_herm_add_left {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} (x x' y : Fin n → F) :
    ggPSUFP_herm σ (x + x') y = ggPSUFP_herm σ x y + ggPSUFP_herm σ x' y := by
  simp only [ggPSUFP_herm, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem ggPSUFP_herm_add_right {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} (x y y' : Fin n → F) :
    ggPSUFP_herm σ x (y + y') = ggPSUFP_herm σ x y + ggPSUFP_herm σ x y' := by
  simp only [ggPSUFP_herm, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem ggPSUFP_herm_smul_left {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} (c : F) (x y : Fin n → F) :
    ggPSUFP_herm σ (c • x) y = σ c * ggPSUFP_herm σ x y := by
  simp only [ggPSUFP_herm, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

private theorem ggPSUFP_herm_smul_right {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} (c : F) (x y : Fin n → F) :
    ggPSUFP_herm σ x (c • y) = c * ggPSUFP_herm σ x y := by
  simp only [ggPSUFP_herm, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring

private def ggPSUFP_planeVec {F : Type*} [Field F] {n : ℕ} (k : ℕ) (hk : 2 * k + 1 < n) (x y : F) : Fin n → F :=
  Pi.single ⟨2 * k, by omega⟩ x + Pi.single ⟨2 * k + 1, hk⟩ y

private theorem ggPSUFP_herm_planeVec {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} {k k' : ℕ} (hk : 2 * k + 1 < n) (hk' : 2 * k' + 1 < n)
    (x y x' y' : F) :
    ggPSUFP_herm σ (ggPSUFP_planeVec k hk x y) (ggPSUFP_planeVec k' hk' x' y') =
      if k = k' then σ x * x' + σ y * y' else 0 := by
  simp only [ggPSUFP_planeVec, ggPSUFP_herm_add_left, ggPSUFP_herm_add_right, ggPSUFP_herm_single_single, Fin.mk.injEq]
  by_cases h : k = k'
  · subst h; simp
  · have h1 : ¬ 2 * k = 2 * k' := by omega
    have h2 : ¬ 2 * k = 2 * k' + 1 := by omega
    have h3 : ¬ 2 * k + 1 = 2 * k' := by omega
    simp [h, h1, h2, h3]

private theorem ggPSUFP_herm_planeVec_single {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} {k : ℕ} (hk : 2 * k + 1 < n) {a : Fin n}
    (ha : 2 * k + 1 < a.val) (x y z : F) :
    ggPSUFP_herm σ (ggPSUFP_planeVec k hk x y) (Pi.single a z) = 0 := by
  simp only [ggPSUFP_planeVec, ggPSUFP_herm_add_left, ggPSUFP_herm_single_single, Fin.ext_iff]
  have h1 : ¬ 2 * k = a.val := by omega
  have h2 : ¬ 2 * k + 1 = a.val := by omega
  simp [h1, h2]

private theorem ggPSUFP_herm_single_planeVec {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} {k : ℕ} (hk : 2 * k + 1 < n) {a : Fin n}
    (ha : 2 * k + 1 < a.val) (x y z : F) :
    ggPSUFP_herm σ (Pi.single a z) (ggPSUFP_planeVec k hk x y) = 0 := by
  simp only [ggPSUFP_planeVec, ggPSUFP_herm_add_right, ggPSUFP_herm_single_single, Fin.ext_iff]
  have h1 : ¬ a.val = 2 * k := by omega
  have h2 : ¬ a.val = 2 * k + 1 := by omega
  simp [h1, h2]

private noncomputable def ggPSUFP_wittCol {F : Type*} [Field F] (n : ℕ) (u ω : F) (c : Fin n) : Fin n → F :=
  if hc : c.val < n / 2 then ggPSUFP_planeVec c.val (by omega) 1 u
  else if hc' : n - n / 2 ≤ c.val then
    (1 - ω)⁻¹ • ggPSUFP_planeVec (n - 1 - c.val) (by omega) 1 (u * ω)
  else Pi.single ⟨n - 1, by omega⟩ 1

private theorem ggPSUFP_wittCol_of_lt {F : Type*} [Field F] {n : ℕ} (u ω : F) {c : Fin n} (hc : c.val < n / 2) :
    ggPSUFP_wittCol n u ω c = ggPSUFP_planeVec c.val (by omega) 1 u := by
  simp only [ggPSUFP_wittCol, hc, ↓reduceDIte]

private theorem ggPSUFP_wittCol_of_ge {F : Type*} [Field F] {n : ℕ} (u ω : F) {c : Fin n} (hc : n - n / 2 ≤ c.val) :
    ggPSUFP_wittCol n u ω c = (1 - ω)⁻¹ • ggPSUFP_planeVec (n - 1 - c.val) (by omega) 1 (u * ω) := by
  have hc0 : ¬ c.val < n / 2 := by omega
  simp only [ggPSUFP_wittCol, hc0, hc, ↓reduceDIte]

private theorem ggPSUFP_wittCol_mid {F : Type*} [Field F] {n : ℕ} (u ω : F) {c : Fin n} (hc : ¬ c.val < n / 2)
    (hc' : ¬ n - n / 2 ≤ c.val) :
    ggPSUFP_wittCol n u ω c = Pi.single ⟨n - 1, by omega⟩ 1 := by
  simp only [ggPSUFP_wittCol, hc, hc', ↓reduceDIte]

private theorem ggPSUFP_herm_wittCol {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} {u ω : F}
    (hu : σ u * u = -1) (hω : σ ω * ω = 1) (hω1 : ω ≠ 1) (a b : Fin n) :
    ggPSUFP_herm σ (ggPSUFP_wittCol n u ω a) (ggPSUFP_wittCol n u ω b) = if b.val = n - (a.val + 1) then 1 else 0 := by
  have hs : (1 - ω) ≠ 0 := sub_ne_zero.mpr (Ne.symm hω1)
  have ha := a.isLt
  have hb := b.isLt
  have hsσ : σ (1 - ω)⁻¹ * (1 - σ ω) = 1 := by
    rw [map_inv₀, show (1 - σ ω) = σ (1 - ω) by rw [map_sub, map_one]]
    exact inv_mul_cancel₀ (by rwa [Ne, map_eq_zero_iff _ σ.injective])
  have key1 : σ 1 * 1 + σ u * u = 0 := by rw [map_one, one_mul, hu]; ring
  have key2 : σ 1 * 1 + σ u * (u * ω) = 1 - ω := by
    rw [map_one, one_mul, ← mul_assoc, hu]; ring
  have key3 : σ 1 * 1 + σ (u * ω) * u = 1 - σ ω := by
    rw [map_one, one_mul, map_mul, mul_comm (σ u), mul_assoc, hu]; ring
  have key4 : σ 1 * 1 + σ (u * ω) * (u * ω) = 0 := by
    rw [map_one, one_mul, map_mul,
      show σ u * σ ω * (u * ω) = (σ u * u) * (σ ω * ω) by ring, hu, hω]; ring
  by_cases ha1 : a.val < n / 2
  · rw [ggPSUFP_wittCol_of_lt u ω ha1]
    by_cases hb1 : b.val < n / 2
    · rw [ggPSUFP_wittCol_of_lt u ω hb1, ggPSUFP_herm_planeVec]
      have : ¬ b.val = n - (a.val + 1) := by omega
      simp only [this, ↓reduceIte]
      split_ifs
      · exact key1
      · rfl
    · by_cases hb2 : n - n / 2 ≤ b.val
      · rw [ggPSUFP_wittCol_of_ge u ω hb2, ggPSUFP_herm_smul_right, ggPSUFP_herm_planeVec]
        by_cases hab : b.val = n - (a.val + 1)
        · have h' : a.val = n - 1 - b.val := by omega
          rw [ite_eq_left h', ite_eq_left hab, key2, inv_mul_cancel₀ hs]
        · have h' : ¬ a.val = n - 1 - b.val := by omega
          rw [ite_eq_right h', ite_eq_right hab, mul_zero]
      · have hab : ¬ b.val = n - (a.val + 1) := by omega
        rw [ggPSUFP_wittCol_mid u ω hb1 hb2, ggPSUFP_herm_planeVec_single σ _ (by simp; omega)]
        simp only [hab, ↓reduceIte]
  · by_cases ha2 : n - n / 2 ≤ a.val
    · rw [ggPSUFP_wittCol_of_ge u ω ha2, ggPSUFP_herm_smul_left]
      by_cases hb1 : b.val < n / 2
      · rw [ggPSUFP_wittCol_of_lt u ω hb1, ggPSUFP_herm_planeVec]
        by_cases hab : b.val = n - (a.val + 1)
        · have h' : n - 1 - a.val = b.val := by omega
          rw [ite_eq_left h', ite_eq_left hab, key3, hsσ]
        · have h' : ¬ n - 1 - a.val = b.val := by omega
          rw [ite_eq_right h', ite_eq_right hab, mul_zero]
      · by_cases hb2 : n - n / 2 ≤ b.val
        · rw [ggPSUFP_wittCol_of_ge u ω hb2, ggPSUFP_herm_smul_right, ggPSUFP_herm_planeVec]
          have hab : ¬ b.val = n - (a.val + 1) := by omega
          simp only [hab, ↓reduceIte]
          split_ifs
          · rw [key4, mul_zero, mul_zero]
          · rw [mul_zero, mul_zero]
        · have hab : ¬ b.val = n - (a.val + 1) := by omega
          rw [ggPSUFP_wittCol_mid u ω hb1 hb2, ggPSUFP_herm_planeVec_single σ _ (by simp; omega), mul_zero]
          simp only [hab, ↓reduceIte]
    · rw [ggPSUFP_wittCol_mid u ω ha1 ha2]
      by_cases hb1 : b.val < n / 2
      · have hab : ¬ b.val = n - (a.val + 1) := by omega
        rw [ggPSUFP_wittCol_of_lt u ω hb1, ggPSUFP_herm_single_planeVec σ _ (by simp; omega)]
        simp only [hab, ↓reduceIte]
      · by_cases hb2 : n - n / 2 ≤ b.val
        · have hab : ¬ b.val = n - (a.val + 1) := by omega
          rw [ggPSUFP_wittCol_of_ge u ω hb2, ggPSUFP_herm_smul_right, ggPSUFP_herm_single_planeVec σ _
            (by simp; omega), mul_zero]
          simp only [hab, ↓reduceIte]
        · have hab : b.val = n - (a.val + 1) := by omega
          rw [ggPSUFP_wittCol_mid u ω hb1 hb2, ggPSUFP_herm_single_single]
          simp only [hab, ↓reduceIte, map_one, one_mul]

private theorem ggPSUFP_wittMatrix_gram {F : Type*} [Field F] (σ : F ≃+* F) {n : ℕ} {u ω : F}
    (hu : σ u * u = -1) (hω : σ ω * ω = 1) (hω1 : ω ≠ 1) :
    conjTr σ (Matrix.of fun r c => ggPSUFP_wittCol n u ω c r) * (Matrix.of fun r c => ggPSUFP_wittCol n u ω c r) =
      antidiag n := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [conjTr, transpose_apply, map_apply, of_apply, antidiag, Fin.ext_iff, Fin.val_rev]
  exact ggPSUFP_herm_wittCol σ hu hω hω1 a b

end WittCopy

section FirstPlane

private theorem ggPSUFP_planeVec_apply_eq_zero_of_lt {K : Type} [Field K] {n k : ℕ} (hk : 2 * k + 1 < n)
    (x y : K) {i : Fin n} (hi : 2 * k + 1 < i.val) :
    ggPSUFP_planeVec (F := K) k hk x y i = 0 := by
  simp only [ggPSUFP_planeVec, Pi.add_apply]
  have h0 : ¬ 2 * k = i.val := by omega
  have h1 : ¬ 2 * k + 1 = i.val := by omega
  simp [Pi.single_eq_of_ne, Fin.ext_iff, h0, h1]

private theorem ggPSUFP_wittCol_apply_eq_zero {K : Type} [Field K] {n : ℕ} (hn : 3 ≤ n) (u ω : K) {i j : Fin n}
    (hj : j.val = 0 ∨ j.val = n - 1) (hi : 2 ≤ i.val) :
    ggPSUFP_wittCol n u ω j i = 0 := by
  rcases hj with hj | hj
  · rw [ggPSUFP_wittCol_of_lt u ω (show j.val < n / 2 by omega)]
    apply ggPSUFP_planeVec_apply_eq_zero_of_lt (k := j.val)
    omega
  · rw [ggPSUFP_wittCol_of_ge u ω (show n - n / 2 ≤ j.val by omega)]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [mul_eq_zero]
    right
    apply ggPSUFP_planeVec_apply_eq_zero_of_lt (k := n - 1 - j.val)
    omega

theorem ggPSUFP_exists_wittMatrix_firstPlane {K : Type} [Field K] [Finite K] {p f : ℕ}
    [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} (hn : 3 ≤ n) :
    ∃ P : GL (Fin n) K,
      conjTr (unitaryInvolution K p f) (P : Matrix (Fin n) (Fin n) K) *
        (P : Matrix (Fin n) (Fin n) K) = antidiag n ∧
      (∀ i j : Fin n, (j.val = 0 ∨ j.val = n - 1) → 2 ≤ i.val →
        (P : Matrix (Fin n) (Fin n) K) i j = 0) := by
  obtain ⟨u, hu⟩ := exists_norm_eq_neg_one (F := K) (p := p) (f := f) hK
  obtain ⟨ω, hω, hω1⟩ := exists_norm_eq_one_ne_one (F := K) (p := p) (f := f) hK
  let M : Matrix (Fin n) (Fin n) K :=
    Matrix.of fun r c => ggPSUFP_wittCol n u ω c r
  have hgram : conjTr (unitaryInvolution K p f) M * M = antidiag n :=
    ggPSUFP_wittMatrix_gram (unitaryInvolution K p f) (u := u) (ω := ω) hu hω hω1
  have hdet : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hgram
    rw [det_mul, h, mul_zero] at this
    exact det_antidiag_ne_zero n this.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero M hdet, hgram, ?_⟩
  intro i j hj hi
  exact ggPSUFP_wittCol_apply_eq_zero hn u ω hj hi

end FirstPlane

end CFSG.StandardType
