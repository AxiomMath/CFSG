module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrLine
public import CFSG.GroupTheory.WeirSylow.UniqueE27Orthogonal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped Matrix

def s16c11_fr_bound3 {m : ℕ} (hm : m = 3 ∨ m = 4) : 3 ≤ m := by
  rcases hm with rfl | rfl <;> decide

@[expose] def s16c11_fr_emb (m : ℕ) (hm : 3 ≤ m) : S16C11FrIdx (m - 2) → S16C11FrIdx m
  | Sum.inl i => Sum.inl ⟨i.1 + 2, by omega⟩
  | Sum.inr (Sum.inl i) => Sum.inr (Sum.inl ⟨i.1 + 2, by omega⟩)
  | Sum.inr (Sum.inr k) => Sum.inr (Sum.inr k)

@[expose] def s16c11_fr_A (m : ℕ) (h : 3 ≤ m) (i : Fin 2) : S16C11FrIdx m :=
  Sum.inl ⟨i.1, by omega⟩

@[expose] def s16c11_fr_B (m : ℕ) (h : 3 ≤ m) (i : Fin 2) : S16C11FrIdx m :=
  Sum.inr (Sum.inl ⟨i.1, by omega⟩)

@[expose] def s16c11_fr_A_inj {m : ℕ} (hm : 3 ≤ m) : Function.Injective (s16c11_fr_A m hm) := by
  intro a i h
  rw [s16c11_fr_A, s16c11_fr_A, Sum.inl.injEq, Fin.mk.injEq] at h
  exact Fin.ext h

@[expose] def s16c11_fr_B_inj {m : ℕ} (hm : 3 ≤ m) : Function.Injective (s16c11_fr_B m hm) := by
  intro a i h
  rw [s16c11_fr_B, s16c11_fr_B, Sum.inr.injEq, Sum.inl.injEq, Fin.mk.injEq] at h
  exact Fin.ext h

theorem s16c11_fr_A_ne {m : ℕ} (hm : 3 ≤ m) {a i : Fin 2} (h : a ≠ i) :
    s16c11_fr_A m hm a ≠ s16c11_fr_A m hm i :=
  fun hc => h (s16c11_fr_A_inj hm hc)

theorem s16c11_fr_B_ne {m : ℕ} (hm : 3 ≤ m) {b i : Fin 2} (h : b ≠ i) :
    s16c11_fr_B m hm b ≠ s16c11_fr_B m hm i :=
  fun hc => h (s16c11_fr_B_inj hm hc)

@[expose] def s16c11_fr_Eb (m : ℕ) (hm : m = 3 ∨ m = 4) (i : Fin 2) : S16C11FrVec m :=
  Pi.single (s16c11_fr_A m (s16c11_fr_bound3 hm) i) 1

theorem s16c11_fr_fin_two_eq (i : Fin 2) : i = 0 ∨ i = 1 := by
  rcases (by omega : i.1 = 0 ∨ i.1 = 1) with h | h
  · exact Or.inl (Fin.ext h)
  · exact Or.inr (Fin.ext h)

theorem s16c11_fr_emb_injective {m : ℕ} (hm : 3 ≤ m) :
    Function.Injective (s16c11_fr_emb m hm) := by
  rintro (i | (j | k)) (i' | (j' | k')) hab
  · simp only [s16c11_fr_emb, Sum.inl.injEq, Fin.mk.injEq] at hab
    exact congrArg Sum.inl (Fin.ext (by omega))
  · exact absurd hab (by simp [s16c11_fr_emb])
  · exact absurd hab (by simp [s16c11_fr_emb])
  · exact absurd hab (by simp [s16c11_fr_emb])
  · simp only [s16c11_fr_emb, Sum.inr.injEq, Sum.inl.injEq, Fin.mk.injEq] at hab
    exact congrArg (fun x => Sum.inr (Sum.inl x)) (Fin.ext (by omega))
  · exact absurd hab (by simp [s16c11_fr_emb])
  · exact absurd hab (by simp [s16c11_fr_emb])
  · exact absurd hab (by simp [s16c11_fr_emb])
  · simp only [s16c11_fr_emb, Sum.inr.injEq] at hab
    exact congrArg (fun x => Sum.inr (Sum.inr x)) hab

theorem s16c11_fr_Eb_zero {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_fr_Eb m hm 0 = s16c11FrE m 0 := by
  rcases hm with rfl | rfl <;> rfl

theorem s16c11_fr_Eb_one {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_fr_Eb m hm 1 = s16c11FrE m 1 := by
  rcases hm with rfl | rfl <;> rfl

theorem s16c11_fr_isK_Eb {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hM : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w) (i : Fin 2) :
    M *ᵥ s16c11_fr_Eb m hm i = s16c11_fr_Eb m hm i := by
  rcases s16c11_fr_fin_two_eq i with rfl | rfl
  · rw [s16c11_fr_Eb_zero]
    exact hM (s16c11FrE m 0) (by simp [s16c11FrLine])
  · rw [s16c11_fr_Eb_one]
    exact hM (s16c11FrE m 1) (by simp [s16c11FrLine])

theorem s16c11_fr_emb_ne_A {m : ℕ} (hm : 3 ≤ m)
    (r : S16C11FrIdx (m - 2)) (i : ℕ) (hi : i < 2) :
    s16c11_fr_emb m hm r ≠ Sum.inl (⟨i, by omega⟩ : Fin (m - 1)) := by
  rcases r with a | a
  · intro hc
    simp only [s16c11_fr_emb, Sum.inl.injEq, Fin.mk.injEq] at hc
    omega
  · rcases a with b | c <;> intro hc <;> simp only [s16c11_fr_emb] at hc <;>
      exact absurd hc (by simp)

theorem s16c11_fr_isK_apply_A {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hM : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w) (i : Fin 2) (r : S16C11FrIdx (m - 2)) :
    M (s16c11_fr_emb m (s16c11_fr_bound3 hm) r) (s16c11_fr_A m (s16c11_fr_bound3 hm) i) = 0 := by
  have h := congrFun (s16c11_fr_isK_Eb hm hM i) (s16c11_fr_emb m (s16c11_fr_bound3 hm) r)
  dsimp only [s16c11_fr_Eb] at h
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at h
  have hne : s16c11_fr_emb m (s16c11_fr_bound3 hm) r ≠ s16c11_fr_A m (s16c11_fr_bound3 hm) i := by
    rw [s16c11_fr_A]
    exact s16c11_fr_emb_ne_A (s16c11_fr_bound3 hm) r i.1 i.2
  rwa [Pi.single_eq_of_ne hne] at h

theorem s16c11_fr_Q_three (v : S16C11FrVec 3) :
    S16C11FrQ 3 v =
      v (s16c11_fr_A 3 (by decide) 0) * v (s16c11_fr_B 3 (by decide) 0) +
      v (s16c11_fr_A 3 (by decide) 1) * v (s16c11_fr_B 3 (by decide) 1) +
      S16C11FrQ 1 (v ∘ s16c11_fr_emb 3 (by decide)) := by
  dsimp only [S16C11FrQ, StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
  rw [Fin.sum_univ_two, Fin.sum_univ_zero]
  simp only [Function.comp_apply, s16c11_fr_emb, one_mul, s16c11_fr_A, s16c11_fr_B]
  simp
  ring

theorem s16c11_fr_Q_four (v : S16C11FrVec 4) :
    S16C11FrQ 4 v =
      v (s16c11_fr_A 4 (by decide) 0) * v (s16c11_fr_B 4 (by decide) 0) +
      v (s16c11_fr_A 4 (by decide) 1) * v (s16c11_fr_B 4 (by decide) 1) +
      S16C11FrQ 2 (v ∘ s16c11_fr_emb 4 (by decide)) := by
  dsimp only [S16C11FrQ, StatedQuadMinus, CFSG.MatrixModel.minusQuadCore]
  rw [Fin.sum_univ_three, Fin.sum_univ_one]
  simp only [Function.comp_apply, s16c11_fr_emb, one_mul, s16c11_fr_A, s16c11_fr_B]
  simp
  ring

theorem s16c11_fr_Q_decomp {m : ℕ} (hm : m = 3 ∨ m = 4) (v : S16C11FrVec m) :
    S16C11FrQ m v =
      v (s16c11_fr_A m (s16c11_fr_bound3 hm) 0) * v (s16c11_fr_B m (s16c11_fr_bound3 hm) 0) +
      v (s16c11_fr_A m (s16c11_fr_bound3 hm) 1) * v (s16c11_fr_B m (s16c11_fr_bound3 hm) 1) +
      S16C11FrQ (m - 2) (v ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm)) := by
  rcases hm with rfl | rfl
  · exact s16c11_fr_Q_three v
  · exact s16c11_fr_Q_four v

theorem s16c11_fr_Eb_apply_emb {m : ℕ} (hm : m = 3 ∨ m = 4) (i : Fin 2)
    (c : S16C11FrIdx (m - 2)) :
    s16c11_fr_Eb m hm i (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) = 0 := by
  have hne : s16c11_fr_emb m (s16c11_fr_bound3 hm) c
      ≠ s16c11_fr_A m (s16c11_fr_bound3 hm) i := by
    rw [s16c11_fr_A]
    exact s16c11_fr_emb_ne_A (s16c11_fr_bound3 hm) c i.1 i.2
  simp only [s16c11_fr_Eb, Pi.single_eq_of_ne hne]

theorem s16c11_fr_Q_add_Eb {m : ℕ} (hm : m = 3 ∨ m = 4) (v : S16C11FrVec m) (i : Fin 2) :
    S16C11FrQ m (v + s16c11_fr_Eb m hm i) =
      S16C11FrQ m v + v (s16c11_fr_B m (s16c11_fr_bound3 hm) i) := by
  rw [s16c11_fr_Q_decomp hm (v + s16c11_fr_Eb m hm i), s16c11_fr_Q_decomp hm v]
  have hcomp : (v + s16c11_fr_Eb m hm i) ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm) =
      v ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm) := by
    funext c
    simp only [Function.comp_apply, Pi.add_apply, s16c11_fr_Eb_apply_emb, add_zero]
  rw [hcomp]
  rcases s16c11_fr_fin_two_eq i with rfl | rfl <;>
    simp [Pi.add_apply, s16c11_fr_Eb, s16c11_fr_A, s16c11_fr_B] <;>
    ring

theorem s16c11_fr_Q_zero {m : ℕ} : S16C11FrQ m (0 : S16C11FrVec m) = 0 := by
  simp only [S16C11FrQ, StatedQuadMinus, CFSG.MatrixModel.minusQuadCore, Pi.zero_apply,
    mul_zero, zero_mul, add_zero, Finset.sum_const_zero]
  ring

theorem s16c11_fr_Q_Eb {m : ℕ} (hm : m = 3 ∨ m = 4) (i : Fin 2) :
    S16C11FrQ m (s16c11_fr_Eb m hm i) = 0 := by
  have h := s16c11_fr_Q_add_Eb hm (0 : S16C11FrVec m) i
  simpa [s16c11_fr_Q_zero] using h

def s16c11_fr_pol (m : ℕ) (v w : S16C11FrVec m) : ZMod 2 :=
  S16C11FrQ m (v + w) + S16C11FrQ m v + S16C11FrQ m w

theorem s16c11_fr_pol_Eb {m : ℕ} (hm : m = 3 ∨ m = 4) (v : S16C11FrVec m) (i : Fin 2) :
    s16c11_fr_pol m v (s16c11_fr_Eb m hm i) =
      v (s16c11_fr_B m (s16c11_fr_bound3 hm) i) := by
  have h := s16c11_fr_Q_add_Eb hm v i
  have hz := s16c11_fr_Q_Eb hm i
  have h2 : S16C11FrQ m v + S16C11FrQ m v = 0 := CharTwo.add_self_eq_zero _
  simp only [s16c11_fr_pol, h, hz]
  rw [show (S16C11FrQ m v + v (s16c11_fr_B m (s16c11_fr_bound3 hm) i)) +
      S16C11FrQ m v + 0
      = (S16C11FrQ m v + S16C11FrQ m v) +
        v (s16c11_fr_B m (s16c11_fr_bound3 hm) i) by abel]
  rw [h2, zero_add]

theorem s16c11_fr_pol_mulVec {m : ℕ}
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hQ : ∀ v : S16C11FrVec m, S16C11FrQ m (M *ᵥ v) = S16C11FrQ m v)
    (v w : S16C11FrVec m) :
    s16c11_fr_pol m (M *ᵥ v) (M *ᵥ w) = s16c11_fr_pol m v w := by
  simp only [s16c11_fr_pol, ← Matrix.mulVec_add, hQ]

theorem s16c11_fr_emb_ne_B {m : ℕ} (hm : 3 ≤ m)
    (c : S16C11FrIdx (m - 2)) (i : ℕ) (hi : i < 2) :
    s16c11_fr_emb m hm c ≠ Sum.inr (Sum.inl (⟨i, by omega⟩ : Fin (m - 1))) := by
  rcases c with a | a
  · intro hc
    simp only [s16c11_fr_emb] at hc
    exact absurd hc (by simp)
  · rcases a with b | c' <;> intro hc <;> simp only [s16c11_fr_emb] at hc
    · simp only [Sum.inr.injEq, Sum.inl.injEq, Fin.mk.injEq] at hc
      omega
    · exact absurd hc (by simp)

theorem s16c11_fr_apply_B {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hQ : ∀ v : S16C11FrVec m, S16C11FrQ m (M *ᵥ v) = S16C11FrQ m v)
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w)
    (i : Fin 2) (c : S16C11FrIdx (m - 2)) :
    M (s16c11_fr_B m (s16c11_fr_bound3 hm) i) (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) = 0 := by
  let e : S16C11FrVec m := Pi.single (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) 1
  have h1 : M (s16c11_fr_B m (s16c11_fr_bound3 hm) i) (s16c11_fr_emb m (s16c11_fr_bound3 hm) c)
      = (M *ᵥ e) (s16c11_fr_B m (s16c11_fr_bound3 hm) i) := by
    simp only [e, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [h1, ← s16c11_fr_pol_Eb hm (M *ᵥ e) i]
  rw [← s16c11_fr_isK_Eb hm hK i]
  rw [s16c11_fr_pol_mulVec hQ]
  rw [s16c11_fr_pol_Eb hm e i]
  have hne : s16c11_fr_B m (s16c11_fr_bound3 hm) i
      ≠ s16c11_fr_emb m (s16c11_fr_bound3 hm) c := by
    intro hc
    exact s16c11_fr_emb_ne_B (s16c11_fr_bound3 hm) c i.1 i.2 hc.symm
  simp only [e, Pi.single_eq_of_ne hne]

theorem s16c11_fr_eq_A_or_B_of_not_mem {m : ℕ} (hm : 3 ≤ m) {x : S16C11FrIdx m}
    (hx : x ∉ (Finset.univ.image (s16c11_fr_emb m hm) : Finset (S16C11FrIdx m))) :
    (∃ i : Fin 2, x = s16c11_fr_A m hm i) ∨ (∃ i : Fin 2, x = s16c11_fr_B m hm i) := by
  rcases x with a | a
  · by_cases h : a.1 < 2
    · exact Or.inl ⟨⟨a.1, h⟩, rfl⟩
    · exfalso
      apply hx
      refine Finset.mem_image.mpr ⟨Sum.inl ⟨a.1 - 2, by omega⟩, Finset.mem_univ _, ?_⟩
      simp only [s16c11_fr_emb]
      apply congrArg Sum.inl
      apply Fin.ext
      show (a.1 - 2) + 2 = a.1
      omega
  · rcases a with b | k
    · by_cases h : b.1 < 2
      · exact Or.inr ⟨⟨b.1, h⟩, rfl⟩
      · exfalso
        apply hx
        refine Finset.mem_image.mpr
          ⟨Sum.inr (Sum.inl ⟨b.1 - 2, by omega⟩), Finset.mem_univ _, ?_⟩
        simp only [s16c11_fr_emb]
        apply congrArg (fun z => Sum.inr (Sum.inl z))
        apply Fin.ext
        show (b.1 - 2) + 2 = b.1
        omega
    · exfalso
      apply hx
      exact Finset.mem_image.mpr ⟨Sum.inr (Sum.inr k), Finset.mem_univ _, rfl⟩

@[expose] def s16c11_fr_block (m : ℕ) (hm : m = 3 ∨ m = 4)
    (M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) :
    Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2) :=
  M.submatrix (s16c11_fr_emb m (s16c11_fr_bound3 hm)) (s16c11_fr_emb m (s16c11_fr_bound3 hm))

theorem s16c11_fr_block_mul {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M N : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hM : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w)
    (hN : ∀ w ∈ s16c11FrLine m, N *ᵥ w = w)
    (hNq : ∀ v : S16C11FrVec m, S16C11FrQ m (N *ᵥ v) = S16C11FrQ m v) :
    s16c11_fr_block m hm (M * N) =
      s16c11_fr_block m hm M * s16c11_fr_block m hm N := by
  ext r c
  simp only [s16c11_fr_block, Matrix.submatrix_apply, Matrix.mul_apply]
  let f : S16C11FrIdx m → ZMod 2 :=
    fun k => M (s16c11_fr_emb m (s16c11_fr_bound3 hm) r) k
      * N k (s16c11_fr_emb m (s16c11_fr_bound3 hm) c)
  have hinj : Function.Injective (s16c11_fr_emb m (s16c11_fr_bound3 hm)) :=
    s16c11_fr_emb_injective (s16c11_fr_bound3 hm)
  have hsum : ∑ k, f k = ∑ k ∈ Finset.univ.image (s16c11_fr_emb m (s16c11_fr_bound3 hm)), f k := by
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro x _ hx
    rcases s16c11_fr_eq_A_or_B_of_not_mem (s16c11_fr_bound3 hm) hx with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · dsimp only [f]
      rw [show M (s16c11_fr_emb m (s16c11_fr_bound3 hm) r)
          (s16c11_fr_A m (s16c11_fr_bound3 hm) i) = 0 from
        s16c11_fr_isK_apply_A hm hM i r, zero_mul]
    · dsimp only [f]
      rw [show N (s16c11_fr_B m (s16c11_fr_bound3 hm) i)
          (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) = 0 from
        s16c11_fr_apply_B hm hNq hN i c, mul_zero]
  rw [hsum, Finset.sum_image hinj.injOn]

@[expose] noncomputable def s16c11_fr_extend (m : ℕ) (hm : m = 3 ∨ m = 4) (v : S16C11FrVec (m -
    2)) :
    S16C11FrVec m :=
  Function.extend (s16c11_fr_emb m (s16c11_fr_bound3 hm)) v 0

theorem s16c11_fr_extend_apply {m : ℕ} (hm : m = 3 ∨ m = 4) (v : S16C11FrVec (m - 2))
    (c : S16C11FrIdx (m - 2)) :
    s16c11_fr_extend m hm v (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) = v c := by
  rw [s16c11_fr_extend]
  exact Function.Injective.extend_apply (s16c11_fr_emb_injective _) v 0 c

theorem s16c11_fr_extend_eq_zero {m : ℕ} (hm : m = 3 ∨ m = 4) (v : S16C11FrVec (m - 2))
    {k : S16C11FrIdx m}
    (hk : k ∉ (Finset.univ.image (s16c11_fr_emb m (s16c11_fr_bound3 hm)) :
      Finset (S16C11FrIdx m))) :
    s16c11_fr_extend m hm v k = 0 := by
  rw [s16c11_fr_extend]
  exact Function.extend_apply' (f := s16c11_fr_emb m (s16c11_fr_bound3 hm)) v 0 k (by
    rw [Finset.mem_image] at hk
    exact fun ⟨a, ha⟩ => hk ⟨a, Finset.mem_univ a, ha⟩)

theorem s16c11_fr_Q_extend {m : ℕ} (hm : m = 3 ∨ m = 4) (v : S16C11FrVec (m - 2)) :
    S16C11FrQ m (s16c11_fr_extend m hm v) = S16C11FrQ (m - 2) v := by
  rw [s16c11_fr_Q_decomp hm (s16c11_fr_extend m hm v)]
  have hcomp : (s16c11_fr_extend m hm v) ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm) = v := by
    funext c
    simp only [Function.comp_apply, s16c11_fr_extend_apply]
  have hA : ∀ i : Fin 2, s16c11_fr_extend m hm v (s16c11_fr_A m (s16c11_fr_bound3 hm) i) = 0 := by
    intro i
    refine s16c11_fr_extend_eq_zero hm v ?_
    intro hmem
    obtain ⟨c, -, hc⟩ := Finset.mem_image.mp hmem
    rw [s16c11_fr_A] at hc
    exact s16c11_fr_emb_ne_A (s16c11_fr_bound3 hm) c i.1 i.2 hc
  rw [hA 0, hA 1, hcomp]
  ring

theorem s16c11_fr_mulVec_extend_comp {m : ℕ} (hm : m = 3 ∨ m = 4)
    (M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) (v : S16C11FrVec (m - 2)) :
    (M *ᵥ s16c11_fr_extend m hm v) ∘ s16c11_fr_emb m (s16c11_fr_bound3 hm) =
      s16c11_fr_block m hm M *ᵥ v := by
  funext c
  simp only [Function.comp_apply, s16c11_fr_block, Matrix.submatrix_apply, Matrix.mulVec,
    dotProduct]
  rw [show (∑ k, M (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) k
        * s16c11_fr_extend m hm v k)
      = ∑ k ∈ Finset.univ.image (s16c11_fr_emb m (s16c11_fr_bound3 hm)),
          M (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) k * s16c11_fr_extend m hm v k from
    (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by
      rw [s16c11_fr_extend_eq_zero hm v hk, mul_zero])).symm]
  rw [Finset.sum_image (s16c11_fr_emb_injective (s16c11_fr_bound3 hm)).injOn]
  refine Finset.sum_congr rfl fun c' _ => ?_
  rw [s16c11_fr_extend_apply]

theorem s16c11_fr_block_isometry {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hQ : ∀ v : S16C11FrVec m, S16C11FrQ m (M *ᵥ v) = S16C11FrQ m v)
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w) (v : S16C11FrVec (m - 2)) :
    S16C11FrQ (m - 2) (s16c11_fr_block m hm M *ᵥ v) = S16C11FrQ (m - 2) v := by
  have hB : ∀ i : Fin 2,
      (M *ᵥ s16c11_fr_extend m hm v) (s16c11_fr_B m (s16c11_fr_bound3 hm) i) = 0 := by
    intro i
    simp only [Matrix.mulVec, dotProduct]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k ∈ Finset.univ.image (s16c11_fr_emb m (s16c11_fr_bound3 hm))
    · obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hk
      rw [s16c11_fr_apply_B hm hQ hK i c, zero_mul]
    · rw [s16c11_fr_extend_eq_zero hm v hk, mul_zero]
  have h1 : S16C11FrQ (m - 2) (s16c11_fr_block m hm M *ᵥ v)
      = S16C11FrQ m (M *ᵥ s16c11_fr_extend m hm v) := by
    rw [s16c11_fr_Q_decomp hm (M *ᵥ s16c11_fr_extend m hm v), hB 0, hB 1,
      s16c11_fr_mulVec_extend_comp hm M v]
    ring
  rw [h1, hQ, s16c11_fr_Q_extend]

@[expose] def s16c11_fr_partFwd (m : ℕ) (hm : 3 ≤ m) :
    (S16C11FrIdx (m - 2) ⊕ Fin 2 ⊕ Fin 2) → S16C11FrIdx m
  | Sum.inl c => s16c11_fr_emb m hm c
  | Sum.inr (Sum.inl i) => s16c11_fr_A m hm i
  | Sum.inr (Sum.inr i) => s16c11_fr_B m hm i

@[expose] def s16c11_fr_partInv (m : ℕ) (hm : 3 ≤ m) :
    S16C11FrIdx m → (S16C11FrIdx (m - 2) ⊕ Fin 2 ⊕ Fin 2)
  | Sum.inl i => if h : i.1 < 2 then Sum.inr (Sum.inl ⟨i.1, h⟩)
      else Sum.inl (Sum.inl ⟨i.1 - 2, by omega⟩)
  | Sum.inr (Sum.inl i) => if h : i.1 < 2 then Sum.inr (Sum.inr ⟨i.1, h⟩)
      else Sum.inl (Sum.inr (Sum.inl ⟨i.1 - 2, by omega⟩))
  | Sum.inr (Sum.inr k) => Sum.inl (Sum.inr (Sum.inr k))

theorem s16c11_fr_part_left (m : ℕ) (hm : 3 ≤ m) :
    Function.LeftInverse (s16c11_fr_partInv m hm) (s16c11_fr_partFwd m hm) := by
  rintro ((i | (j | k)) | (a | b))
  · simp only [s16c11_fr_partFwd, s16c11_fr_partInv, s16c11_fr_emb]
    rw [dif_neg (by omega)]
    simp
  · simp only [s16c11_fr_partFwd, s16c11_fr_partInv, s16c11_fr_emb]
    rw [dif_neg (by omega)]
    simp
  · rfl
  · simp only [s16c11_fr_partFwd, s16c11_fr_partInv, s16c11_fr_A]
    rw [dif_pos a.2]
  · simp only [s16c11_fr_partFwd, s16c11_fr_partInv, s16c11_fr_B]
    rw [dif_pos b.2]

theorem s16c11_fr_part_right (m : ℕ) (hm : 3 ≤ m) :
    Function.RightInverse (s16c11_fr_partInv m hm) (s16c11_fr_partFwd m hm) := by
  rintro (i | (j | k))
  · by_cases h : i.1 < 2
    · simp only [s16c11_fr_partInv, dif_pos h, s16c11_fr_partFwd, s16c11_fr_A]
    · simp only [s16c11_fr_partInv, dif_neg h, s16c11_fr_partFwd, s16c11_fr_emb]
      apply congrArg Sum.inl
      apply Fin.ext
      show (i.1 - 2) + 2 = i.1
      omega
  · by_cases h : j.1 < 2
    · simp only [s16c11_fr_partInv, dif_pos h, s16c11_fr_partFwd, s16c11_fr_B]
    · simp only [s16c11_fr_partInv, dif_neg h, s16c11_fr_partFwd, s16c11_fr_emb]
      apply congrArg (fun z => Sum.inr (Sum.inl z))
      apply Fin.ext
      show (j.1 - 2) + 2 = j.1
      omega
  · rfl

@[expose] noncomputable def s16c11_fr_part (m : ℕ) (hm : 3 ≤ m) :
    (S16C11FrIdx (m - 2) ⊕ Fin 2 ⊕ Fin 2) ≃ S16C11FrIdx m :=
  Equiv.mk (s16c11_fr_partFwd m hm) (s16c11_fr_partInv m hm)
    (s16c11_fr_part_left m hm) (s16c11_fr_part_right m hm)

theorem s16c11_fr_part_inl {m : ℕ} (hm : 3 ≤ m) (c : S16C11FrIdx (m - 2)) :
    s16c11_fr_part m hm (Sum.inl c) = s16c11_fr_emb m hm c := rfl

theorem s16c11_fr_part_inr_inl {m : ℕ} (hm : 3 ≤ m) (i : Fin 2) :
    s16c11_fr_part m hm (Sum.inr (Sum.inl i)) = s16c11_fr_A m hm i := rfl

theorem s16c11_fr_part_inr_inr {m : ℕ} (hm : 3 ≤ m) (i : Fin 2) :
    s16c11_fr_part m hm (Sum.inr (Sum.inr i)) = s16c11_fr_B m hm i := rfl

@[expose] noncomputable def s16c11_fr_diag (m : ℕ)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2)) :
    Matrix (S16C11FrIdx (m - 2) ⊕ Fin 2 ⊕ Fin 2)
      (S16C11FrIdx (m - 2) ⊕ Fin 2 ⊕ Fin 2) (ZMod 2) :=
  Matrix.fromBlocks h 0 0 (Matrix.fromBlocks 1 0 0 1)

@[expose] noncomputable def s16c11_fr_hat (m : ℕ) (hm : 3 ≤ m)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2)) :
    Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2) :=
  (Matrix.reindex (s16c11_fr_part m hm) (s16c11_fr_part m hm)) (s16c11_fr_diag m h)

theorem s16c11_fr_hat_apply {m : ℕ} (hm : 3 ≤ m)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))
    (x x' : S16C11FrIdx (m - 2) ⊕ Fin 2 ⊕ Fin 2) :
    s16c11_fr_hat m hm h (s16c11_fr_part m hm x) (s16c11_fr_part m hm x') =
      s16c11_fr_diag m h x x' := by
  rw [s16c11_fr_hat, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

theorem s16c11_fr_hat_emb {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))
    (r c : S16C11FrIdx (m - 2)) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm) h
      (s16c11_fr_emb m (s16c11_fr_bound3 hm) r)
      (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) = h r c := by
  rw [← s16c11_fr_part_inl (s16c11_fr_bound3 hm) r,
    ← s16c11_fr_part_inl (s16c11_fr_bound3 hm) c, s16c11_fr_hat_apply,
    s16c11_fr_diag, Matrix.fromBlocks_apply₁₁]

theorem s16c11_fr_hat_A_row {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))
    (i : Fin 2) (x : S16C11FrIdx (m - 2) ⊕ Fin 2 ⊕ Fin 2) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm) h
      (s16c11_fr_A m (s16c11_fr_bound3 hm) i) (s16c11_fr_part m (s16c11_fr_bound3 hm) x) =
      s16c11_fr_diag m h (Sum.inr (Sum.inl i)) x := by
  rw [← s16c11_fr_part_inr_inl (s16c11_fr_bound3 hm) i, s16c11_fr_hat_apply]

theorem s16c11_fr_hat_B_row {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))
    (i : Fin 2) (x : S16C11FrIdx (m - 2) ⊕ Fin 2 ⊕ Fin 2) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm) h
      (s16c11_fr_B m (s16c11_fr_bound3 hm) i) (s16c11_fr_part m (s16c11_fr_bound3 hm) x) =
      s16c11_fr_diag m h (Sum.inr (Sum.inr i)) x := by
  rw [← s16c11_fr_part_inr_inr (s16c11_fr_bound3 hm) i, s16c11_fr_hat_apply]

theorem s16c11_fr_block_one {m : ℕ} (hm : m = 3 ∨ m = 4) :
    s16c11_fr_block m hm (1 : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) = 1 := by
  ext r c
  simp only [s16c11_fr_block, Matrix.submatrix_apply, Matrix.one_apply,
    (s16c11_fr_emb_injective (s16c11_fr_bound3 hm)).eq_iff]

theorem s16c11_fr_K_mul_inv_coe {m : ℕ} (g : ↥(s16c11FrK m)) :
    ((((g : ↥(S16C11FrO m)) : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) *
      ((((g⁻¹ : ↥(s16c11FrK m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2))) = 1 := by
  simp

@[expose] noncomputable def s16c11_fr_blockUnit {m : ℕ} (hm : m = 3 ∨ m = 4) (g : ↥(s16c11FrK m)) :
    (Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))ˣ :=
  Units.mkOfMulEqOne (s16c11_fr_block m hm
      (((g : ↥(S16C11FrO m)) : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)))
    (s16c11_fr_block m hm
      ((((g⁻¹ : ↥(s16c11FrK m)) : ↥(S16C11FrO m)) :
        Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
        Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)))
    (by
      rw [← s16c11_fr_block_mul hm g.2 (g⁻¹).2
        (fun v => CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore (g⁻¹).1.2 v)]
      rw [s16c11_fr_K_mul_inv_coe g]
      exact s16c11_fr_block_one hm)

theorem s16c11_fr_blockUnit_mem {m : ℕ} (hm : m = 3 ∨ m = 4) (g : ↥(s16c11FrK m)) :
    (s16c11_fr_blockUnit hm g : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) ∈
      S16C11FrO (m - 2) := by
  refine Subgroup.subset_closure fun v => ?_
  rw [s16c11_fr_blockUnit, Units.val_mkOfMulEqOne]
  exact s16c11_fr_block_isometry hm
    (fun w => CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore g.1.2 w) g.2 v

@[expose] noncomputable def s16c11_fr_leviHom {m : ℕ} (hm : m = 3 ∨ m = 4) :
    ↥(s16c11FrK m) →* ↥(S16C11FrO (m - 2)) :=
  MonoidHom.mk' (fun g => ⟨s16c11_fr_blockUnit hm g, s16c11_fr_blockUnit_mem hm g⟩)
    (fun g h => by
      refine Subtype.ext (Units.ext ?_)
      simp only [Subgroup.coe_mul, Units.val_mul, s16c11_fr_blockUnit,
        Units.val_mkOfMulEqOne]
      rw [s16c11_fr_block_mul hm g.2 h.2
        (fun v => CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore h.1.2 v)])

theorem s16c11_fr_hat_row_C_zero {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))
    (c : S16C11FrIdx (m - 2)) {k : S16C11FrIdx m}
    (hk : k ∉ (Finset.univ.image (s16c11_fr_emb m (s16c11_fr_bound3 hm)) :
      Finset (S16C11FrIdx m))) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm) h (s16c11_fr_emb m (s16c11_fr_bound3 hm) c) k = 0 := by
  set x := (s16c11_fr_part m (s16c11_fr_bound3 hm)).symm k with hx
  have hk' : s16c11_fr_part m (s16c11_fr_bound3 hm) x = k := Equiv.apply_symm_apply _ _
  rw [← hk', ← s16c11_fr_part_inl (s16c11_fr_bound3 hm) c, s16c11_fr_hat_apply]
  rcases x with c' | (a | b)
  · exfalso
    apply hk
    rw [← hk', s16c11_fr_part_inl]
    exact Finset.mem_image.mpr ⟨c', Finset.mem_univ _, rfl⟩
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

theorem s16c11_fr_hat_row_A_eval {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))
    (i : Fin 2) (j : S16C11FrIdx m) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm) h (s16c11_fr_A m (s16c11_fr_bound3 hm) i) j =
      (Pi.single (s16c11_fr_A m (s16c11_fr_bound3 hm) i)
        (1 : ZMod 2) : S16C11FrIdx m → ZMod 2) j := by
  set x := (s16c11_fr_part m (s16c11_fr_bound3 hm)).symm j with hx
  have hj : s16c11_fr_part m (s16c11_fr_bound3 hm) x = j := Equiv.apply_symm_apply _ _
  rw [← hj, s16c11_fr_hat_A_row hm h i]
  rcases x with c | (a | b)
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    rw [s16c11_fr_part_inl, s16c11_fr_A,
      Pi.single_eq_of_ne (s16c11_fr_emb_ne_A (s16c11_fr_bound3 hm) c i.1 i.2)]
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
      Matrix.one_apply]
    by_cases hia : i = a
    · rw [if_pos hia]
      rw [s16c11_fr_part_inr_inl,
        show s16c11_fr_A m (s16c11_fr_bound3 hm) a =
          s16c11_fr_A m (s16c11_fr_bound3 hm) i from
        congrArg (s16c11_fr_A m (s16c11_fr_bound3 hm)) hia.symm, Pi.single_eq_same]
    · rw [if_neg hia]
      rw [s16c11_fr_part_inr_inl,
        Pi.single_eq_of_ne (s16c11_fr_A_ne (s16c11_fr_bound3 hm) (fun h => hia h.symm))]
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₂,
      Matrix.zero_apply]
    rw [s16c11_fr_part_inr_inr, Pi.single_eq_of_ne (by simp [s16c11_fr_A, s16c11_fr_B])]

theorem s16c11_fr_hat_row_B_eval {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))
    (i : Fin 2) (j : S16C11FrIdx m) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm) h (s16c11_fr_B m (s16c11_fr_bound3 hm) i) j =
      (Pi.single (s16c11_fr_B m (s16c11_fr_bound3 hm) i)
        (1 : ZMod 2) : S16C11FrIdx m → ZMod 2) j := by
  set x := (s16c11_fr_part m (s16c11_fr_bound3 hm)).symm j with hx
  have hj : s16c11_fr_part m (s16c11_fr_bound3 hm) x = j := Equiv.apply_symm_apply _ _
  rw [← hj, s16c11_fr_hat_B_row hm h i]
  rcases x with c | (a | b)
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
    rw [s16c11_fr_part_inl, s16c11_fr_B,
      Pi.single_eq_of_ne (s16c11_fr_emb_ne_B (s16c11_fr_bound3 hm) c i.1 i.2)]
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
    rw [s16c11_fr_part_inr_inl, Pi.single_eq_of_ne (by simp [s16c11_fr_A, s16c11_fr_B])]
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₂,
      Matrix.one_apply]
    by_cases hib : i = b
    · rw [if_pos hib]
      rw [s16c11_fr_part_inr_inr,
        show s16c11_fr_B m (s16c11_fr_bound3 hm) b =
          s16c11_fr_B m (s16c11_fr_bound3 hm) i from
        congrArg (s16c11_fr_B m (s16c11_fr_bound3 hm)) hib.symm, Pi.single_eq_same]
    · rw [if_neg hib]
      rw [s16c11_fr_part_inr_inr,
        Pi.single_eq_of_ne (s16c11_fr_B_ne (s16c11_fr_bound3 hm) (fun h => hib h.symm))]

theorem s16c11_fr_hat_col_A {m : ℕ} (hm : m = 3 ∨ m = 4)
    (h : Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))
    (i : Fin 2) (j : S16C11FrIdx m) :
    s16c11_fr_hat m (s16c11_fr_bound3 hm) h j (s16c11_fr_A m (s16c11_fr_bound3 hm) i) =
      s16c11_fr_Eb m hm i j := by
  set x := (s16c11_fr_part m (s16c11_fr_bound3 hm)).symm j with hx
  have hj : s16c11_fr_part m (s16c11_fr_bound3 hm) x = j := Equiv.apply_symm_apply _ _
  rw [← hj, ← s16c11_fr_part_inr_inl (s16c11_fr_bound3 hm) i, s16c11_fr_Eb,
    s16c11_fr_hat_apply]
  rcases x with c | (a | b)
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]
    rw [s16c11_fr_part_inl, s16c11_fr_A,
      Pi.single_eq_of_ne (s16c11_fr_emb_ne_A (s16c11_fr_bound3 hm) c i.1 i.2)]
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
      Matrix.one_apply]
    by_cases hai : a = i
    · rw [if_pos hai]
      rw [s16c11_fr_part_inr_inl,
        show s16c11_fr_A m (s16c11_fr_bound3 hm) a =
          s16c11_fr_A m (s16c11_fr_bound3 hm) i from
        congrArg (s16c11_fr_A m (s16c11_fr_bound3 hm)) hai, Pi.single_eq_same]
    · rw [if_neg hai]
      rw [s16c11_fr_part_inr_inl,
        Pi.single_eq_of_ne (s16c11_fr_A_ne (s16c11_fr_bound3 hm) hai)]
  · simp only [s16c11_fr_diag, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁,
      Matrix.zero_apply]
    rw [s16c11_fr_part_inr_inr,
      Pi.single_eq_of_ne (by simp [s16c11_fr_A, s16c11_fr_B])]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
