module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08CoreSwaps
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLDType

public section

namespace CFSG.StandardType

private theorem ggQ2s08k6_isSwap_mul_self {m : ℕ} {σ : Equiv.Perm (Fin m)} (h : σ.IsSwap) :
    σ * σ = 1 := by
  rcases h with ⟨x, y, hxy, rfl⟩
  exact Equiv.swap_mul_self x y

private theorem ggQ2s08k6_commute_of_sq_eq_one {G : Type*} [Group G] {x y : G}
    (hx : x * x = 1) (hy : y * y = 1) (h : (x * y) ^ 2 = 1) : x * y = y * x := by
  rw [pow_two] at h
  have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_left hx
  have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_left hy
  have h' : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_left h
  rw [← h', mul_inv_rev, hx', hy']

theorem ggQ2s08core_swap_coxeter {m ℓ : ℕ} (hℓ : 9 ≤ ℓ) (τ : Fin ℓ → Equiv.Perm (Fin m))
    (hsw : ∀ i, (τ i).IsSwap) (hne : ∀ i j, i ≠ j → τ i ≠ τ j) (M : CoxeterMatrix (Fin ℓ))
    (hM : M = CoxeterMatrix.A ℓ ∨ M = CoxeterMatrix.B ℓ ∨ M = ggCoxeterMatrixD ℓ)
    (hrel : ∀ i j, i ≠ j → (τ i * τ j) ^ M i j = 1)
    (hncomm : ∀ i j, i ≠ j → M i j ≠ 2 → τ i * τ j ≠ τ j * τ i) :
    M = CoxeterMatrix.A ℓ ∧ ∃ a : Fin (ℓ + 1) → Fin m, Function.Injective a ∧
      ∀ i : Fin ℓ, τ i = Equiv.swap (a i.castSucc) (a i.succ) := by
  rcases hM with hA | hB | hD
  ·
    rw [hA] at hrel hncomm ⊢
    have hadj : ∀ i j : Fin ℓ, (i : ℕ) + 1 = j → (τ i * τ j) ^ 3 = 1 := by
      intro i j hij
      have hneij : i ≠ j := by
        intro h
        rw [h] at hij
        omega
      have hrelij := hrel i j hneij
      have hMij : CoxeterMatrix.A ℓ i j = 3 := by
        simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hneij, if_pos (Or.inr hij)]
      rwa [hMij] at hrelij
    have hcomm : ∀ i j : Fin ℓ, (i : ℕ) + 2 ≤ j → τ i * τ j = τ j * τ i := by
      intro i j hij
      have hneij : i ≠ j := by
        intro h
        rw [h] at hij
        omega
      have hrelij := hrel i j hneij
      have hMij : CoxeterMatrix.A ℓ i j = 2 := by
        simp only [CoxeterMatrix.A, Matrix.of_apply, if_neg hneij,
          if_neg (by omega : ¬ ((j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j))]
      have h2 : (τ i * τ j) ^ 2 = 1 := by
        rwa [hMij] at hrelij
      exact ggQ2s08k6_commute_of_sq_eq_one (ggQ2s08k6_isSwap_mul_self (hsw i))
        (ggQ2s08k6_isSwap_mul_self (hsw j)) h2
    obtain ⟨a, ha_inj, ha_swap⟩ := ggQ2s08core_swap_path (by omega) τ hsw hne hadj hcomm
    exact ⟨rfl, a, ha_inj, ha_swap⟩
  ·
    rw [hB] at hrel hncomm
    exfalso
    let i : Fin ℓ := ⟨ℓ - 2, by omega⟩
    let j : Fin ℓ := ⟨ℓ - 1, by omega⟩
    have hij : i ≠ j := by
      intro h
      have hv : (i : ℕ) = (j : ℕ) := by rw [h]
      simp [i, j] at hv
      omega
    have hMij : CoxeterMatrix.B ℓ i j = 4 := by
      simp only [CoxeterMatrix.B, Matrix.of_apply, if_neg hij]
      rw [if_pos]
      right
      constructor <;> simp [i, j]
    have h4 : (τ i * τ j) ^ 4 = 1 := by
      have h := hrel i j hij
      rwa [hMij] at h
    have hcommij : τ i * τ j = τ j * τ i :=
      ggQ2s08core_no_four (hsw i) (hsw j) (hne i j hij) h4
    exact (hncomm i j hij (by rw [hMij]; norm_num)) hcommij
  ·
    rw [hD] at hrel hncomm
    exfalso
    let z : Fin ℓ := ⟨ℓ - 3, by omega⟩
    let a : Fin ℓ := ⟨ℓ - 4, by omega⟩
    let b : Fin ℓ := ⟨ℓ - 2, by omega⟩
    let c : Fin ℓ := ⟨ℓ - 1, by omega⟩
    have hzne : z ≠ a := by
      intro h
      have hv : (z : ℕ) = (a : ℕ) := by rw [h]
      simp [z, a] at hv
      omega
    have hzbe : z ≠ b := by
      intro h
      have hv : (z : ℕ) = (b : ℕ) := by rw [h]
      simp [z, b] at hv
      omega
    have hzce : z ≠ c := by
      intro h
      have hv : (z : ℕ) = (c : ℕ) := by rw [h]
      simp [z, c] at hv
      omega
    have habne : a ≠ b := by
      intro h
      have hv : (a : ℕ) = (b : ℕ) := by rw [h]
      simp [a, b] at hv
      omega
    have hacne : a ≠ c := by
      intro h
      have hv : (a : ℕ) = (c : ℕ) := by rw [h]
      simp [a, c] at hv
      omega
    have hbcne : b ≠ c := by
      intro h
      have hv : (b : ℕ) = (c : ℕ) := by rw [h]
      simp [b, c] at hv
      omega
    have hDza : CartanMatrix.D ℓ z a ≠ 0 := by
      simp only [CartanMatrix.D, Matrix.of_apply, z, a]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> omega
    have hDzb : CartanMatrix.D ℓ z b ≠ 0 := by
      simp only [CartanMatrix.D, Matrix.of_apply, z, b]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> omega
    have hDzc : CartanMatrix.D ℓ z c ≠ 0 := by
      simp only [CartanMatrix.D, Matrix.of_apply, z, c]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> omega
    have hDab : CartanMatrix.D ℓ a b = 0 := by
      simp only [CartanMatrix.D, Matrix.of_apply, a, b]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> omega
    have hDac : CartanMatrix.D ℓ a c = 0 := by
      simp only [CartanMatrix.D, Matrix.of_apply, a, c]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> omega
    have hDbc : CartanMatrix.D ℓ b c = 0 := by
      simp only [CartanMatrix.D, Matrix.of_apply, b, c]
      split_ifs with h1 h2 h3 h4 h5 h6 <;> omega
    have hMza : ggCoxeterMatrixD ℓ z a = 3 := by
      simp only [ggCoxeterMatrixD_apply, if_neg hzne, if_neg hDza]
    have hMzb : ggCoxeterMatrixD ℓ z b = 3 := by
      simp only [ggCoxeterMatrixD_apply, if_neg hzbe, if_neg hDzb]
    have hMzc : ggCoxeterMatrixD ℓ z c = 3 := by
      simp only [ggCoxeterMatrixD_apply, if_neg hzce, if_neg hDzc]
    have hMab : ggCoxeterMatrixD ℓ a b = 2 := by
      simp only [ggCoxeterMatrixD_apply, if_neg habne, if_pos hDab]
    have hMac : ggCoxeterMatrixD ℓ a c = 2 := by
      simp only [ggCoxeterMatrixD_apply, if_neg hacne, if_pos hDac]
    have hMbc : ggCoxeterMatrixD ℓ b c = 2 := by
      simp only [ggCoxeterMatrixD_apply, if_neg hbcne, if_pos hDbc]
    have h3a : (τ z * τ a) ^ 3 = 1 := by
      have h := hrel z a hzne
      rwa [hMza] at h
    have h3b : (τ z * τ b) ^ 3 = 1 := by
      have h := hrel z b hzbe
      rwa [hMzb] at h
    have h3c : (τ z * τ c) ^ 3 = 1 := by
      have h := hrel z c hzce
      rwa [hMzc] at h
    have hab' : τ a * τ b = τ b * τ a := by
      have h := hrel a b habne
      have h2 : (τ a * τ b) ^ 2 = 1 := by
        rwa [hMab] at h
      exact ggQ2s08k6_commute_of_sq_eq_one (ggQ2s08k6_isSwap_mul_self (hsw a))
        (ggQ2s08k6_isSwap_mul_self (hsw b)) h2
    have hac' : τ a * τ c = τ c * τ a := by
      have h := hrel a c hacne
      have h2 : (τ a * τ c) ^ 2 = 1 := by
        rwa [hMac] at h
      exact ggQ2s08k6_commute_of_sq_eq_one (ggQ2s08k6_isSwap_mul_self (hsw a))
        (ggQ2s08k6_isSwap_mul_self (hsw c)) h2
    have hbc' : τ b * τ c = τ c * τ b := by
      have h := hrel b c hbcne
      have h2 : (τ b * τ c) ^ 2 = 1 := by
        rwa [hMbc] at h
      exact ggQ2s08k6_commute_of_sq_eq_one (ggQ2s08k6_isSwap_mul_self (hsw b))
        (ggQ2s08k6_isSwap_mul_self (hsw c)) h2
    exact ggQ2s08core_no_fork (hsw z) (hsw a) (hsw b) (hsw c)
      (hne z a hzne) (hne z b hzbe) (hne z c hzce)
      (hne a b habne) (hne a c hacne) (hne b c hbcne)
      h3a h3b h3c hab' hac' hbc'

end CFSG.StandardType

end

