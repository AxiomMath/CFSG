module

public import CFSG.LocalAnalysis.StandardType.PhanEReduction
import CFSG.LocalAnalysis.StandardType.PhanELiftGlue

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

abbrev IsEEdge {n : ℕ} (i j : Fin n) : Prop :=
  ((i : ℕ) = 0 ∧ (j : ℕ) = 2) ∨ ((i : ℕ) = 1 ∧ (j : ℕ) = 3) ∨ (2 ≤ (i : ℕ) ∧ (j : ℕ) = i + 1)

@[expose] def IsEShape {n : ℕ} (M : CoxeterMatrix (Fin n)) : Prop :=
  5 ≤ n ∧ ∀ i j : Fin n, i ≠ j →
    ((IsEEdge i j ∨ IsEEdge j i) → M i j = 3) ∧ (¬ (IsEEdge i j ∨ IsEEdge j i) → M i j = 2)

theorem isEShape_E₆ : IsEShape CoxeterMatrix.E₆ := by
  refine ⟨by norm_num, fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> decide

theorem isEShape_E₇ : IsEShape CoxeterMatrix.E₇ := by
  refine ⟨by norm_num, fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> decide

theorem isEShape_E₈ : IsEShape CoxeterMatrix.E₈ := by
  refine ⟨by norm_num, fun i j => ?_⟩
  fin_cases i <;> fin_cases j <;> decide

private def hmbFam_c {n : ℕ} (hn : 5 ≤ n) (k : ℕ) : Fin n :=
  ⟨min (if k = 0 then 0 else k + 1) (n - 1), by
    have : n - 1 < n := by omega
    exact lt_of_le_of_lt (min_le_right _ _) this⟩

private lemma hmbFam_c_zero {n : ℕ} (hn : 5 ≤ n) : (hmbFam_c hn 0 : ℕ) = 0 := by
  simp [hmbFam_c]

private lemma hmbFam_c_pos {n : ℕ} (hn : 5 ≤ n) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n - 2) :
    (hmbFam_c hn k : ℕ) = k + 1 := by
  have hk : k ≠ 0 := by omega
  have hmin : min (k + 1) (n - 1) = k + 1 := min_eq_left (by omega)
  simp [hmbFam_c, hk, hmin]

private lemma hmbFam_c_eq_zero {n : ℕ} (hn : 5 ≤ n) : hmbFam_c hn 0 = ⟨0, by omega⟩ :=
  Fin.ext (by rw [hmbFam_c_zero hn])

private lemma hmbFam_c_eq_mk {n : ℕ} (hn : 5 ≤ n) {k : ℕ} (h1 : 1 ≤ k) (h2 : k ≤ n - 2) :
    hmbFam_c hn k = ⟨k + 1, by omega⟩ :=
  Fin.ext (by rw [hmbFam_c_pos hn h1 h2])

private lemma hmbFam_c_val {n : ℕ} (hn : 5 ≤ n) {k : ℕ} (hk : k ≤ n - 2) :
    (hmbFam_c hn k : ℕ) = if k = 0 then 0 else k + 1 := by
  rcases eq_or_ne k 0 with rfl | hk0
  · simp [hmbFam_c_zero hn]
  · rw [hmbFam_c_pos hn (by omega) hk, if_neg hk0]

private lemma hmbFam_ne_of_isEEdge {n : ℕ} {i j : Fin n} (h : IsEEdge i j) : i ≠ j := by
  rintro rfl
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

private lemma hmbFam_isEEdge_of_lt {n : ℕ} {M : CoxeterMatrix (Fin n)} (hM : IsEShape M)
    {i j : Fin n} (hij : i < j) (hMij : M i j = 3) : IsEEdge i j := by
  have hne : i ≠ j := ne_of_lt hij
  have hor : IsEEdge i j ∨ IsEEdge j i := by
    by_contra h
    have h2 : M i j = 2 := (hM.2 i j hne).2 h
    omega
  rcases hor with h | h
  · exact h
  · exfalso
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega

private lemma hmbFam_adj {n : ℕ} (hn : 5 ≤ n) (i : ℕ) (hi : i < n - 2) :
    IsEEdge (hmbFam_c hn i) (hmbFam_c hn (i + 1)) := by
  by_cases hi0 : i = 0
  · subst i
    refine Or.inl ⟨hmbFam_c_zero hn, ?_⟩
    rw [show (0 + 1 : ℕ) = 1 from rfl]
    exact hmbFam_c_pos hn (by omega) (by omega)
  · have h1 : 1 ≤ i := by omega
    have hvi : (hmbFam_c hn i : ℕ) = i + 1 := hmbFam_c_pos hn h1 (by omega)
    have hvi1 : (hmbFam_c hn (i + 1) : ℕ) = i + 2 := by
      have := hmbFam_c_pos hn (k := i + 1) (by omega) (by omega)
      omega
    refine Or.inr (Or.inr ⟨?_, ?_⟩)
    · rw [hvi]; omega
    · rw [hvi1, hvi]

private lemma hmbFam_far_not {n : ℕ} (hn : 5 ≤ n) (i : ℕ) (hi : i + 1 < n - 2) :
    ¬ (IsEEdge (hmbFam_c hn i) (hmbFam_c hn (i + 2)) ∨
       IsEEdge (hmbFam_c hn (i + 2)) (hmbFam_c hn i)) := by
  by_cases hi0 : i = 0
  · subst i
    have h0 : (hmbFam_c hn 0 : ℕ) = 0 := hmbFam_c_zero hn
    have h2 : (hmbFam_c hn (0 + 2) : ℕ) = 3 := by
      rw [show (0 + 2 : ℕ) = 2 from rfl]
      exact hmbFam_c_pos hn (by omega) (by omega)
    rintro (h | h) <;> rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      simp only [h0] at ha hb <;> simp only [h2] at ha hb <;> omega
  · have h1 : 1 ≤ i := by omega
    have h0 : (hmbFam_c hn i : ℕ) = i + 1 := hmbFam_c_pos hn h1 (by omega)
    have h2 : (hmbFam_c hn (i + 2) : ℕ) = i + 3 := by
      have := hmbFam_c_pos hn (k := i + 2) (by omega) (by omega)
      omega
    rintro (h | h) <;> rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
      simp only [h0] at ha hb <;> simp only [h2] at ha hb <;> omega

private lemma hmbFam_not_adj_41 {n : ℕ} (hn : 5 ≤ n) :
    ¬ (IsEEdge (⟨4, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) ∨
       IsEEdge (⟨1, by omega⟩ : Fin n) (⟨4, by omega⟩ : Fin n)) := by
  rintro (h | h) <;> rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩ | ⟨ha, hb⟩ <;>
    simp only [Fin.val_mk] at ha hb <;> omega

theorem exists_phanFamilyE_of_isEShape {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) {n : ℕ} {M : CoxeterMatrix (Fin n)}
    (hM : IsEShape M) {X : Type} [Group X] {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanSL K p f M U W) :
    ∃ F : PhanFamilyE K p f M X, (∀ i, (F.ι i).range = U i) ∧ ∀ i, Function.Injective (F.ι i) := by
  classical
  have hMsh : IsEShape M := hM
  have hn : 5 ≤ n := hMsh.1
  have h3 : ∀ i j : Fin n, i ≠ j → (IsEEdge i j ∨ IsEEdge j i) → M i j = 3 :=
    fun i j hij h => (hMsh.2 i j hij).1 h
  have h2 : ∀ i j : Fin n, i ≠ j → ¬ (IsEEdge i j ∨ IsEEdge j i) → M i j = 2 :=
    fun i j hij h => (hMsh.2 i j hij).2 h
  let u : ℕ → Subgroup X := fun k => U (hmbFam_c hn k)
  let w : ℕ → Subgroup X := fun k => W (hmbFam_c hn k) (hmbFam_c hn (k + 1))
  have hpair : ∀ i, i < n - 2 → UnitaryBlockStandardPair K p f (w i) (u i) (u (i + 1)) := by
    intro i hi
    have hadj := hmbFam_adj hn i hi
    exact hW.pair (hmbFam_c hn i) (hmbFam_c hn (i + 1))
      (h3 _ _ (hmbFam_ne_of_isEEdge hadj) (Or.inl hadj))
  have hcommu : ∀ i, i + 1 < n - 2 → ∀ x ∈ u i, ∀ y ∈ u (i + 2), x * y = y * x := by
    intro i hi x hx y hy
    have hfar := hmbFam_far_not hn i hi
    have hne : hmbFam_c hn i ≠ hmbFam_c hn (i + 2) := by
      intro hh
      have hvv : (hmbFam_c hn i : ℕ) = (hmbFam_c hn (i + 2) : ℕ) := congrArg Fin.val hh
      rw [hmbFam_c_val hn (by omega), hmbFam_c_val hn (by omega)] at hvv
      by_cases h0 : i = 0
      · subst i; simp at hvv
      · simp [h0, show ¬ (i + 2 = 0) from by omega] at hvv
    exact hW.comm (hmbFam_c hn i) (hmbFam_c hn (i + 2)) (h2 _ _ hne hfar) x hx y hy
  obtain ⟨θc, hθc⟩ := coherent_chain hK (autExtends hK) u w (n - 2) hpair hcommu
  have hM13 : M ⟨1, by omega⟩ ⟨3, by omega⟩ = 3 :=
    h3 _ _ (by intro h; have := congrArg Fin.val h; simp at this)
      (Or.inl (Or.inr (Or.inl ⟨rfl, rfl⟩)))
  obtain ⟨θ₀, -, hk₀, h12_0, h23_0⟩ :=
    pair_normalize (hW.pair ⟨1, by omega⟩ ⟨3, by omega⟩ hM13)
  obtain ⟨hkθc2, -, hθc2_12, hθc2_23, -⟩ := hθc 2 (by omega)
  have hc2 : hmbFam_c hn 2 = ⟨3, by omega⟩ := hmbFam_c_eq_mk hn (by omega) (by omega)
  have hc3 : hmbFam_c hn 3 = ⟨4, by omega⟩ := hmbFam_c_eq_mk hn (by omega) (by omega)
  have hu2 : u 2 = U ⟨3, by omega⟩ := by simp only [u, hc2]
  have hu3 : u 3 = U ⟨4, by omega⟩ := by simp only [u, hc3]
  obtain ⟨θ₁₃, hk₁₃, -, hb12₁₃, hb23₁₃, hcomp₁₃⟩ :=
    exists_glue_mirror hK (θ₁ := θc 2) (θ₂ := θ₀) hkθc2 hk₀
      (by rw [hθc2_12, hu2, h23_0])
      (by
        rw [hθc2_23, hu3, h12_0]
        exact hW.comm ⟨4, by omega⟩ ⟨1, by omega⟩
          (h2 _ _ (by intro h; have := congrArg Fin.val h; simp at this) (hmbFam_not_adj_41 hn)))
  have hb12₁₃' : (B12 K p f).map θ₁₃ = U ⟨1, by omega⟩ := hb12₁₃.trans h12_0
  have hb23₁₃' : (B23 K p f).map θ₁₃ = U ⟨3, by omega⟩ := hb23₁₃.trans h23_0
  let ι : Fin n → (Su K p f 2 →* X) := fun i =>
    if (i : ℕ) = 0 then (θc 0).comp (embSUid (unitaryInvolution K p f) 2)
    else if (i : ℕ) = 1 then θ₁₃.comp (embSUid (unitaryInvolution K p f) 2)
    else (θc ((i : ℕ) - 2)).comp (embSUid (unitaryInvolution K p f) 0)
  let θ : Fin n → Fin n → (Su K p f 3 →* X) := fun i j =>
    if (i : ℕ) = 0 ∧ (j : ℕ) = 2 then θc 0
    else if (i : ℕ) = 1 ∧ (j : ℕ) = 3 then θ₁₃
    else if 2 ≤ (i : ℕ) ∧ (j : ℕ) = i + 1 then θc ((i : ℕ) - 1)
    else 1
  have hι : ∀ i : Fin n, (ι i).range = U i ∧ Function.Injective (ι i) := by
    intro i
    rcases eq_or_ne (i : ℕ) 0 with hi0 | hi0
    · have hιi : ι i = (θc 0).comp (embSUid (unitaryInvolution K p f) 2) := by
        simp only [ι]
        rw [if_pos hi0]
      obtain ⟨hk0', -, h12_0', h23_0', -⟩ := hθc 0 (by omega)
      have hu0 : u 0 = U ⟨0, by omega⟩ := by
        simp only [u]
        rw [hmbFam_c_eq_zero hn]
      have hUi : U i = U ⟨0, by omega⟩ := congrArg U (Fin.ext hi0)
      obtain ⟨hi₂, hr₂, -, -⟩ :=
        pair_block_inj hK hk0' (h12_0'.trans (hu0.trans hUi.symm)) h23_0'
      exact ⟨by simpa [hιi] using hr₂, by simpa [hιi] using hi₂⟩
    · rcases eq_or_ne (i : ℕ) 1 with hi1 | hi1
      · have hιi : ι i = θ₁₃.comp (embSUid (unitaryInvolution K p f) 2) := by
          simp only [ι]
          rw [if_neg hi0, if_pos hi1]
        have hUi : U i = U ⟨1, by omega⟩ := congrArg U (Fin.ext hi1)
        obtain ⟨hi₂, hr₂, -, -⟩ :=
          pair_block_inj hK hk₁₃ (hb12₁₃'.trans hUi.symm) hb23₁₃'
        exact ⟨by simpa [hιi] using hr₂, by simpa [hιi] using hi₂⟩
      · have hi2 : 2 ≤ (i : ℕ) := by omega
        have hk : (i : ℕ) - 2 < n - 2 := by omega
        obtain ⟨hkk, -, h12k, h23k, -⟩ := hθc ((i : ℕ) - 2) hk
        have hck1 : hmbFam_c hn (((i : ℕ) - 2) + 1) = i := by
          apply Fin.ext
          rw [hmbFam_c_pos hn (by omega) (by omega)]
          omega
        have huk1 : u (((i : ℕ) - 2) + 1) = U i := by simp only [u, hck1]
        obtain ⟨-, -, hi₂, hr₂⟩ := pair_block_inj hK hkk h12k (h23k.trans huk1)
        have hιi : ι i = (θc ((i : ℕ) - 2)).comp (embSUid (unitaryInvolution K p f) 0) := by
          simp only [ι]
          rw [if_neg hi0, if_neg hi1]
        exact ⟨by simpa [hιi] using hr₂, by simpa [hιi] using hi₂⟩
  have hleft : ∀ i j : Fin n, i < j → M i j = 3 →
      (θ i j).comp (embSUid (unitaryInvolution K p f) 2) = ι i := by
    intro i j hij hMij
    rcases hmbFam_isEEdge_of_lt hM hij hMij with ⟨hi0, hj2⟩ | ⟨hi1, hj3⟩ | ⟨hi2, hjsucc⟩
    · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hj : j = ⟨2, by omega⟩ := Fin.ext hj2
      rw [hi, hj]
      simp [θ, ι]
    · have hi : i = ⟨1, by omega⟩ := Fin.ext hi1
      have hj : j = ⟨3, by omega⟩ := Fin.ext hj3
      rw [hi, hj]
      simp [θ, ι]
    · have h0 : (i : ℕ) ≠ 0 := by omega
      have h1 : (i : ℕ) ≠ 1 := by omega
      have hθij : θ i j = θc ((i : ℕ) - 1) := by
        simp only [θ]
        rw [if_neg (by rintro ⟨h, -⟩; exact h0 h),
            if_neg (by rintro ⟨h, -⟩; exact h1 h),
            if_pos ⟨hi2, hjsucc⟩]
      have hιi : ι i = (θc ((i : ℕ) - 2)).comp (embSUid (unitaryInvolution K p f) 0) := by
        simp only [ι]
        rw [if_neg h0, if_neg h1]
      rw [hθij, hιi]
      have hk : (i : ℕ) - 2 < n - 2 := by omega
      have hk1 : ((i : ℕ) - 2) + 1 < n - 2 := by omega
      have hchain := (hθc ((i : ℕ) - 2) hk).2.2.2.2 hk1
      have harith : (i : ℕ) - 1 = ((i : ℕ) - 2) + 1 := by omega
      rw [harith, hchain]
  have hright : ∀ i j : Fin n, i < j → M i j = 3 →
      (θ i j).comp (embSUid (unitaryInvolution K p f) 0) = ι j := by
    intro i j hij hMij
    rcases hmbFam_isEEdge_of_lt hM hij hMij with ⟨hi0, hj2⟩ | ⟨hi1, hj3⟩ | ⟨hi2, hjsucc⟩
    · have hi : i = ⟨0, by omega⟩ := Fin.ext hi0
      have hj : j = ⟨2, by omega⟩ := Fin.ext hj2
      rw [hi, hj]
      simp [θ, ι]
    · have hi : i = ⟨1, by omega⟩ := Fin.ext hi1
      have hj : j = ⟨3, by omega⟩ := Fin.ext hj3
      rw [hi, hj]
      have hchain1 : (θc 2).comp (embSUid (unitaryInvolution K p f) 2) =
          (θc 1).comp (embSUid (unitaryInvolution K p f) 0) :=
        (hθc 1 (by omega)).2.2.2.2 (by omega)
      simp [θ, ι]
      rw [hcomp₁₃, hchain1]
    · have h0 : (i : ℕ) ≠ 0 := by omega
      have h1 : (i : ℕ) ≠ 1 := by omega
      have hj0 : (j : ℕ) ≠ 0 := by omega
      have hj1 : (j : ℕ) ≠ 1 := by omega
      have hθij : θ i j = θc ((i : ℕ) - 1) := by
        simp only [θ]
        rw [if_neg (by rintro ⟨h, -⟩; exact h0 h),
            if_neg (by rintro ⟨h, -⟩; exact h1 h),
            if_pos ⟨hi2, hjsucc⟩]
      have hιj : ι j = (θc ((j : ℕ) - 2)).comp (embSUid (unitaryInvolution K p f) 0) := by
        simp only [ι]
        rw [if_neg hj0, if_neg hj1]
      rw [hθij, hιj]
      have harith : (j : ℕ) - 2 = (i : ℕ) - 1 := by omega
      rw [harith]
  have hcomm : ∀ i j : Fin n, M i j = 2 → ∀ a b, ι i a * ι j b = ι j b * ι i a := by
    intro i j hMij a b
    exact hW.comm i j hMij _ ((hι i).1 ▸ ⟨a, rfl⟩) _ ((hι j).1 ▸ ⟨b, rfl⟩)
  exact ⟨⟨ι, θ, hleft, hright, hcomm⟩, fun i => (hι i).1, fun i => (hι i).2⟩

end CFSG.ClassicalInvolution.Phan.PhanE
