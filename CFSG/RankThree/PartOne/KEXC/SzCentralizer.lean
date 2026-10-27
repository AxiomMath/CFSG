module

public import CFSG.RankThree.PartOne.KE.SuzukiDescentSp

public section

namespace CFSG.RankThree.PartOne.KEXC

open Matrix CFSG.Blueprint CFSG.LieType.Ree CFSG.RankThree.PartOne.KE
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K L : Type} [Field K] [Field L] [CharP K 2] [Finite K] {a : ℕ}

omit [CharP K 2] [Finite K] in
theorem exists_suzukiS_mem (a : ℕ) (u v : K) :
    ∃ g : suzukiGroup a K, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = suzukiS a u v := by
  have hdet : (suzukiS a u v).det ≠ 0 := by
    have : (suzukiS a u v).det = 1 := by
      rw [Matrix.det_of_isLowerTriangular]
      · simp [suzukiS, Fin.prod_univ_four]
      · intro i j hij
        change i < j at hij
        fin_cases i <;> fin_cases j <;> first
          | (exfalso; revert hij; decide)
          | simp [suzukiS]
    rw [this]
    exact one_ne_zero
  exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiS a u v) hdet,
    Subgroup.subset_closure (Or.inl ⟨u, v, rfl⟩)⟩, rfl⟩

omit [CharP K 2] [Finite K] in
theorem exists_suzukiD_mem (a : ℕ) (l : Kˣ) :
    ∃ g : suzukiGroup a K, ((g : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) = suzukiD a l := by
  have hdet : (suzukiD a l).det ≠ 0 := by
    rw [suzukiD_eq, Matrix.det_diagonal, Fin.prod_univ_four]
    simp
  exact ⟨⟨Matrix.GeneralLinearGroup.mkOfDetNeZero (suzukiD a l) hdet,
    Subgroup.subset_closure (Or.inr (Or.inl ⟨l, rfl⟩))⟩, rfl⟩


omit [CharP K 2] [Finite K] in
theorem suzukiD_map_diagonal (a : ℕ) (l : Kˣ) (f : K →+* L) :
    (suzukiD a l).map f = Matrix.diagonal fun k : Fin 4 =>
      f (![(l : K) * (l : K) ^ 2 ^ a, (l : K) ^ 2 ^ a, ((l : K) ^ 2 ^ a)⁻¹,
        ((l : K) * (l : K) ^ 2 ^ a)⁻¹] k) := by
  rw [suzukiD_eq, Matrix.diagonal_map (map_zero f)]

omit [CharP K 2] [Finite K] in
theorem diag_mul_apply {M S : Matrix (Fin 4) (Fin 4) L} (hM : ∀ i j : Fin 4, i ≠ j → M i j = 0)
    (i j : Fin 4) : (M * S) i j = M i i * S i j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  intro k _ hk
  rw [hM i k (Ne.symm hk), zero_mul]
  intro h
  exact absurd (Finset.mem_univ i) h

omit [CharP K 2] [Finite K] in
theorem mul_diag_apply {M S : Matrix (Fin 4) (Fin 4) L} (hM : ∀ i j : Fin 4, i ≠ j → M i j = 0)
    (i j : Fin 4) : (S * M) i j = S i j * M j j := by
  rw [Matrix.mul_apply, Finset.sum_eq_single j]
  intro k _ hk
  rw [hM k j hk, mul_zero]
  intro h
  exact absurd (Finset.mem_univ j) h

theorem szEmbed_centralizer_trivial [CharP L 2] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (f : K →+* L) (Y : antiSp L)
    (hY : ∀ s : suzukiGroup a K, Y * szEmbed hK f s = szEmbed hK f s * Y) : Y = 1 := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨l, hl⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hordl : orderOf l = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hl, Nat.card_eq_fintype_card,
      Nat.card_eq_fintype_card, Fintype.card_units]
  have hnl : ∀ n : ℕ, n ≠ 0 → n < Nat.card K - 1 → l ^ n ≠ 1 := fun n hn hlt =>
    pow_ne_one_of_lt_orderOf hn (by rwa [hordl])
  have he2 : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hq : Nat.card K = 2 * (2 ^ a) * (2 ^ a) := by
    rw [hK, pow_succ, pow_mul', ← pow_mul]
    ring_nf
  have hlt0 : 2 * 2 ^ a + 3 < Nat.card K := by
    rw [hq]
    nlinarith [Nat.mul_le_mul he2 he2]
  have hlt : 2 ^ (a + 1) + 2 < Nat.card K - 1 := by
    rw [pow_succ]
    omega
  set M : Matrix (Fin 4) (Fin 4) L := glMat (Y : GL (Fin 4) L) with hM
  have hcomm : ∀ s : suzukiGroup a K,
      M * (glMat ((s : GL (Fin 4) K))).map f = (glMat ((s : GL (Fin 4) K))).map f * M := by
    intro s
    have h1 := congrArg (fun x : antiSp L => glMat (x : GL (Fin 4) L)) (hY s)
    simpa [glMat_szEmbed, Matrix.GeneralLinearGroup.coe_mul, hM] using h1
  obtain ⟨sD, hsD⟩ := exists_suzukiD_mem (K := K) a l
  have hD := hcomm sD
  have hsD' : glMat (sD : GL (Fin 4) K) = suzukiD a l := hsD
  rw [hsD', suzukiD_map_diagonal] at hD
  have hx0 : (l : K) ≠ 0 := Units.ne_zero l
  have hne1 : ∀ n : ℕ, n ≠ 0 → n < Nat.card K - 1 → (l : K) ^ n ≠ 1 := fun n hn hnlt h => by
    apply hnl n hn hnlt
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h]; rfl)
  have hm0 : (l : K) ^ 2 ^ a ≠ 0 := pow_ne_zero _ hx0
  have hf1 : (l : K) ≠ 1 := by
    have := hne1 1 one_ne_zero (by omega)
    rwa [pow_one] at this
  have hf2 : (l : K) * ((l : K) ^ 2 ^ a) ^ 2 ≠ 1 := by
    have := hne1 (1 + 2 ^ (a + 1)) (by omega) (by omega)
    rwa [pow_add, pow_one, pow_succ, pow_mul] at this
  have hf3 : ((l : K) * (l : K) ^ 2 ^ a) ^ 2 ≠ 1 := by
    have := hne1 (2 + 2 ^ (a + 1)) (by omega) (by omega)
    have e : ((l : K) * (l : K) ^ 2 ^ a) ^ 2 = (l : K) ^ (2 + 2 ^ (a + 1)) := by
      rw [mul_pow, ← pow_mul, pow_add, pow_succ]
      ring
    rwa [← e] at this
  have hf4 : ((l : K) ^ 2 ^ a) ^ 2 ≠ 1 := by
    have := hne1 (2 ^ (a + 1)) (by positivity) (by omega)
    rwa [pow_succ, pow_mul] at this
  set x : K := (l : K) with hxdef
  set m : K := x ^ 2 ^ a with hmdef
  have hdist0 : ∀ i j : Fin 4, i < j →
      (![x * m, m, m⁻¹, (x * m)⁻¹] i) ≠ (![x * m, m, m⁻¹, (x * m)⁻¹] j) := by
    intro i j hij h
    fin_cases i <;> fin_cases j <;> simp at hij h
    · apply hf1
      have : (x - 1) * m = 0 := by linear_combination h
      exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_right hm0)
    · apply hf2
      field_simp at h
      linear_combination h
    · apply hf3
      field_simp at h
      linear_combination h
    · apply hf4
      field_simp at h
      linear_combination h
    · apply hf2
      field_simp at h
      linear_combination h
    · apply hf1
      have h2 : m⁻¹ * (1 - x⁻¹) = 0 := by linear_combination h
      have h3 := (mul_eq_zero.1 h2).resolve_left (inv_ne_zero hm0)
      exact inv_eq_one.1 (sub_eq_zero.1 h3).symm
  have hdist : ∀ i j : Fin 4, i ≠ j →
      f (![x * m, m, m⁻¹, (x * m)⁻¹] i) ≠ f (![x * m, m, m⁻¹, (x * m)⁻¹] j) := by
    intro i j hij h
    have h' := f.injective h
    rcases lt_or_gt_of_ne hij with hlt' | hlt'
    · exact hdist0 i j hlt' h'
    · exact hdist0 j i hlt' h'.symm
  have hdiag : ∀ i j : Fin 4, i ≠ j → M i j = 0 := by
    intro i j hij
    have h1 := congrFun (congrFun hD i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : M i j * (f (![x * m, m, m⁻¹, (x * m)⁻¹] j) - f (![x * m, m, m⁻¹, (x * m)⁻¹] i)) =
        0 := by linear_combination h1
    rcases mul_eq_zero.1 h2 with h | h
    · exact h
    · exact absurd (sub_eq_zero.1 h).symm (hdist i j hij)
  obtain ⟨sS, hsS⟩ := exists_suzukiS_mem (K := K) a 1 0
  have hS := hcomm sS
  have hsS' : glMat (sS : GL (Fin 4) K) = suzukiS a 1 0 := hsS
  rw [hsS'] at hS
  have hrel : ∀ i j : Fin 4, suzukiS a (1 : K) (0 : K) i j = 1 → M i i = M j j := by
    intro i j h1
    have h2 := congrFun (congrFun hS i) j
    rw [diag_mul_apply hdiag, mul_diag_apply hdiag] at h2
    simp only [Matrix.map_apply] at h2
    rw [h1, map_one] at h2
    simpa using h2
  have h10 : M 1 1 = M 0 0 := hrel 1 0 (by simp [suzukiS])
  have h21 : M 2 2 = M 1 1 := hrel 2 1 (by simp [suzukiS])
  have h32 : M 3 3 = M 2 2 := hrel 3 2 (by simp [suzukiS])
  have hc : ∀ i : Fin 4, M i i = M 0 0 := by
    intro i
    fin_cases i
    · rfl
    · exact h10
    · exact h21.trans h10
    · exact h32.trans (h21.trans h10)
  have hMdiag : M = Matrix.diagonal (fun _ => M 0 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq, hc]
    · rw [hdiag i j hij, Matrix.diagonal_apply_ne _ hij]
  have hJ : M.transpose * minorJ L * M = minorJ L := mem_antiSp.1 Y.2
  have hcc : M 0 0 * M 0 0 = 1 := by
    have h1 := congrFun (congrFun hJ 0) 3
    rw [transpose_mul_minorJ_mul_apply, minorJ_apply] at h1
    rw [hdiag 1 0 (by decide), hdiag 2 0 (by decide), hdiag 3 0 (by decide), hdiag 0 3 (by decide),
      hdiag 2 3 (by decide), hdiag 1 3 (by decide), hc 3] at h1
    simpa using h1
  have h2 : (2 : L) = 0 := CharTwo.two_eq_zero
  have hc1 : M 0 0 = 1 := by
    have h3 : (M 0 0 - 1) * (M 0 0 - 1) = 0 := by linear_combination hcc + (1 - M 0 0) * h2
    exact sub_eq_zero.1 (mul_self_eq_zero.1 h3)
  have hM1 : M = 1 := by
    rw [hMdiag, hc1]
    exact Matrix.diagonal_one
  refine Subtype.ext (Units.ext ?_)
  exact hM1

end CFSG.RankThree.PartOne.KEXC
