module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11OrthFrLeviA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open scoped Matrix

def s16c11_frSwapD (m : ℕ) :
    (Fin 2 ⊕ (S16C11FrIdx (m - 2) ⊕ Fin 2)) → (S16C11FrIdx (m - 2) ⊕ (Fin 2 ⊕ Fin 2))
  | Sum.inl a => Sum.inr (Sum.inl a)
  | Sum.inr (Sum.inl c) => Sum.inl c
  | Sum.inr (Sum.inr b) => Sum.inr (Sum.inr b)

def s16c11_frSwapDinv (m : ℕ) :
    (S16C11FrIdx (m - 2) ⊕ (Fin 2 ⊕ Fin 2)) → (Fin 2 ⊕ (S16C11FrIdx (m - 2) ⊕ Fin 2))
  | Sum.inl c => Sum.inr (Sum.inl c)
  | Sum.inr (Sum.inl a) => Sum.inl a
  | Sum.inr (Sum.inr b) => Sum.inr (Sum.inr b)

theorem s16c11_frSwapD_left (m : ℕ) :
    Function.LeftInverse (s16c11_frSwapDinv m) (s16c11_frSwapD m) := by
  rintro (a | (c | b)) <;> rfl

theorem s16c11_frSwapD_right (m : ℕ) :
    Function.RightInverse (s16c11_frSwapDinv m) (s16c11_frSwapD m) := by
  rintro (c | (a | b)) <;> rfl

@[expose] noncomputable def s16c11_frPartACB (m : ℕ) (hm : 3 ≤ m) :
    (Fin 2 ⊕ (S16C11FrIdx (m - 2) ⊕ Fin 2)) ≃ S16C11FrIdx m :=
  (Equiv.mk (s16c11_frSwapD m) (s16c11_frSwapDinv m)
    (s16c11_frSwapD_left m) (s16c11_frSwapD_right m)).trans (s16c11_fr_part m hm)

theorem s16c11_frPartACB_A {m : ℕ} (hm : 3 ≤ m) (a : Fin 2) :
    s16c11_frPartACB m hm (Sum.inl a) = s16c11_fr_A m hm a := by
  change s16c11_fr_part m hm (s16c11_frSwapD m (Sum.inl a)) = s16c11_fr_A m hm a
  rw [show s16c11_frSwapD m (Sum.inl a) = Sum.inr (Sum.inl a) from rfl,
    s16c11_fr_part_inr_inl]

theorem s16c11_frPartACB_C {m : ℕ} (hm : 3 ≤ m) (c : S16C11FrIdx (m - 2)) :
    s16c11_frPartACB m hm (Sum.inr (Sum.inl c)) = s16c11_fr_emb m hm c := by
  change s16c11_fr_part m hm (s16c11_frSwapD m (Sum.inr (Sum.inl c))) = s16c11_fr_emb m hm c
  rw [show s16c11_frSwapD m (Sum.inr (Sum.inl c)) = Sum.inl c from rfl, s16c11_fr_part_inl]

theorem s16c11_frPartACB_B {m : ℕ} (hm : 3 ≤ m) (b : Fin 2) :
    s16c11_frPartACB m hm (Sum.inr (Sum.inr b)) = s16c11_fr_B m hm b := by
  change s16c11_fr_part m hm (s16c11_frSwapD m (Sum.inr (Sum.inr b))) = s16c11_fr_B m hm b
  rw [show s16c11_frSwapD m (Sum.inr (Sum.inr b)) = Sum.inr (Sum.inr b) from rfl,
    s16c11_fr_part_inr_inr]

theorem s16c11_fr_apply_BB {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hQ : ∀ v : S16C11FrVec m, S16C11FrQ m (M *ᵥ v) = S16C11FrQ m v)
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w) (i j : Fin 2) :
    M (s16c11_fr_B m (s16c11_fr_bound3 hm) i) (s16c11_fr_B m (s16c11_fr_bound3 hm) j) =
      if i = j then 1 else 0 := by
  have h1 : M (s16c11_fr_B m (s16c11_fr_bound3 hm) i)
      (s16c11_fr_B m (s16c11_fr_bound3 hm) j) =
      (M *ᵥ Pi.single (s16c11_fr_B m (s16c11_fr_bound3 hm) j) (1 : ZMod 2))
        (s16c11_fr_B m (s16c11_fr_bound3 hm) i) := by
    rw [Matrix.mulVec_single_one, Matrix.col_apply]
  rw [h1, ← s16c11_fr_pol_Eb hm (M *ᵥ Pi.single (s16c11_fr_B m (s16c11_fr_bound3 hm) j)
      (1 : ZMod 2)) i, ← s16c11_fr_isK_Eb hm hK i, s16c11_fr_pol_mulVec hQ,
    s16c11_fr_pol_Eb hm (Pi.single (s16c11_fr_B m (s16c11_fr_bound3 hm) j) (1 : ZMod 2)) i]
  by_cases hij : i = j
  · rw [if_pos hij]
    rw [show s16c11_fr_B m (s16c11_fr_bound3 hm) i =
        s16c11_fr_B m (s16c11_fr_bound3 hm) j from
      congrArg (s16c11_fr_B m (s16c11_fr_bound3 hm)) hij, Pi.single_eq_same]
  · rw [if_neg hij, Pi.single_eq_of_ne]
    intro hc
    exact hij (s16c11_fr_B_inj (s16c11_fr_bound3 hm) hc)

theorem s16c11_fr_isK_apply_AA {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w) (i j : Fin 2) :
    M (s16c11_fr_A m (s16c11_fr_bound3 hm) i) (s16c11_fr_A m (s16c11_fr_bound3 hm) j) =
      if i = j then 1 else 0 := by
  have h := congrFun (s16c11_fr_isK_Eb hm hK j) (s16c11_fr_A m (s16c11_fr_bound3 hm) i)
  rw [s16c11_fr_Eb, Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h]
  by_cases hij : i = j
  · rw [if_pos hij]
    rw [show s16c11_fr_A m (s16c11_fr_bound3 hm) i =
        s16c11_fr_A m (s16c11_fr_bound3 hm) j from
      congrArg (s16c11_fr_A m (s16c11_fr_bound3 hm)) hij, Pi.single_eq_same]
  · rw [if_neg hij, Pi.single_eq_of_ne]
    intro hc
    exact hij (s16c11_fr_A_inj (s16c11_fr_bound3 hm) hc)

theorem s16c11_fr_isK_apply_BA {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w) (b a : Fin 2) :
    M (s16c11_fr_B m (s16c11_fr_bound3 hm) b) (s16c11_fr_A m (s16c11_fr_bound3 hm) a) = 0 := by
  have h := congrFun (s16c11_fr_isK_Eb hm hK a) (s16c11_fr_B m (s16c11_fr_bound3 hm) b)
  rw [s16c11_fr_Eb, Matrix.mulVec_single_one, Matrix.col_apply] at h
  rw [h]
  rw [Pi.single_eq_of_ne]
  intro hc
  rw [s16c11_fr_A, s16c11_fr_B] at hc
  exact absurd hc (by simp)

theorem s16c11_fr_block_CC {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hblock : s16c11_fr_block m hm M = 1) (c c' : S16C11FrIdx (m - 2)) :
    M (s16c11_fr_emb m (s16c11_fr_bound3 hm) c)
      (s16c11_fr_emb m (s16c11_fr_bound3 hm) c') = if c = c' then 1 else 0 := by
  have h := congrFun (congrFun hblock c) c'
  rw [s16c11_fr_block, Matrix.submatrix_apply] at h
  rw [h, Matrix.one_apply]

def s16c11_frWeightD (m : ℕ) : (Fin 2 ⊕ (S16C11FrIdx (m - 2) ⊕ Fin 2)) → ℕ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

noncomputable def s16c11_frWeight (m : ℕ) (hm : 3 ≤ m) : S16C11FrIdx m → ℕ :=
  s16c11_frWeightD m ∘ (s16c11_frPartACB m hm).symm

theorem s16c11_frWeight_lt_three {m : ℕ} (hm : 3 ≤ m) (i : S16C11FrIdx m) :
    s16c11_frWeight m hm i < 3 := by
  obtain ⟨x, rfl⟩ := (s16c11_frPartACB m hm).surjective i
  rcases x with a | (c | b) <;>
    simp only [s16c11_frWeight, Function.comp_apply, Equiv.symm_apply_apply, s16c11_frWeightD]
    <;> omega

theorem s16c11_fr_kernel_entry {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w)
    (hQ : ∀ v : S16C11FrVec m, S16C11FrQ m (M *ᵥ v) = S16C11FrQ m v)
    (hblock : s16c11_fr_block m hm M = 1) (i j : S16C11FrIdx m)
    (hij : s16c11_frWeight m (s16c11_fr_bound3 hm) j ≤
      s16c11_frWeight m (s16c11_fr_bound3 hm) i) :
    M i j = if i = j then 1 else 0 := by
  obtain ⟨x, rfl⟩ := (s16c11_frPartACB m (s16c11_fr_bound3 hm)).surjective i
  obtain ⟨y, rfl⟩ := (s16c11_frPartACB m (s16c11_fr_bound3 hm)).surjective j
  simp only [s16c11_frWeight, Function.comp_apply, Equiv.symm_apply_apply] at hij
  rcases x with a | (c | b) <;> rcases y with a' | (c' | b')
  · simp only [s16c11_frWeightD] at hij
    conv_lhs => rw [s16c11_frPartACB_A, s16c11_frPartACB_A]
    rw [s16c11_fr_isK_apply_AA hm hK a a']
    by_cases haa : a = a'
    · rw [if_pos haa,
        if_pos (congrArg (s16c11_frPartACB m (s16c11_fr_bound3 hm)) (congrArg Sum.inl haa))]
    · rw [if_neg haa, if_neg (fun hc =>
        haa ((s16c11_frPartACB m (s16c11_fr_bound3 hm)).injective hc |> Sum.inl.inj))]
  · simp only [s16c11_frWeightD] at hij; omega
  · simp only [s16c11_frWeightD] at hij; omega
  · simp only [s16c11_frWeightD] at hij
    conv_lhs => rw [s16c11_frPartACB_C, s16c11_frPartACB_A]
    rw [s16c11_fr_isK_apply_A hm hK a' c, if_neg (fun hc =>
      absurd ((s16c11_frPartACB m (s16c11_fr_bound3 hm)).injective hc) (by simp))]
  · simp only [s16c11_frWeightD] at hij
    conv_lhs => rw [s16c11_frPartACB_C, s16c11_frPartACB_C]
    rw [s16c11_fr_block_CC hm hblock c c']
    by_cases hcc : c = c'
    · rw [if_pos hcc,
        if_pos (congrArg (s16c11_frPartACB m (s16c11_fr_bound3 hm))
          (congrArg Sum.inr (congrArg Sum.inl hcc)))]
    · rw [if_neg hcc, if_neg (fun hc =>
        hcc ((s16c11_frPartACB m (s16c11_fr_bound3 hm)).injective hc
          |> Sum.inr.inj |> Sum.inl.inj))]
  · simp only [s16c11_frWeightD] at hij; omega
  · simp only [s16c11_frWeightD] at hij
    conv_lhs => rw [s16c11_frPartACB_B, s16c11_frPartACB_A]
    rw [s16c11_fr_isK_apply_BA hm hK b a', if_neg (fun hc =>
      absurd ((s16c11_frPartACB m (s16c11_fr_bound3 hm)).injective hc) (by simp))]
  · simp only [s16c11_frWeightD] at hij
    conv_lhs => rw [s16c11_frPartACB_B, s16c11_frPartACB_C]
    rw [s16c11_fr_apply_B hm hQ hK b c', if_neg (fun hc =>
      absurd ((s16c11_frPartACB m (s16c11_fr_bound3 hm)).injective hc) (by simp))]
  · simp only [s16c11_frWeightD] at hij
    conv_lhs => rw [s16c11_frPartACB_B, s16c11_frPartACB_B]
    rw [s16c11_fr_apply_BB hm hQ hK b b']
    by_cases hbb : b = b'
    · rw [if_pos hbb,
        if_pos (congrArg (s16c11_frPartACB m (s16c11_fr_bound3 hm))
          (congrArg Sum.inr (congrArg Sum.inr hbb)))]
    · rw [if_neg hbb, if_neg (fun hc =>
        hbb ((s16c11_frPartACB m (s16c11_fr_bound3 hm)).injective hc
          |> Sum.inr.inj |> Sum.inr.inj))]

theorem s16c11_fr_kernel_sub_entry {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w)
    (hQ : ∀ v : S16C11FrVec m, S16C11FrQ m (M *ᵥ v) = S16C11FrQ m v)
    (hblock : s16c11_fr_block m hm M = 1) {i j : S16C11FrIdx m}
    (hij : ¬ s16c11_frWeight m (s16c11_fr_bound3 hm) i <
      s16c11_frWeight m (s16c11_fr_bound3 hm) j) : (M - 1) i j = 0 := by
  rw [Matrix.sub_apply, s16c11_fr_kernel_entry hm hK hQ hblock i j (not_lt.1 hij),
    Matrix.one_apply, sub_self]

theorem s16c11_fr_kernel_nilpotent {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w)
    (hQ : ∀ v : S16C11FrVec m, S16C11FrQ m (M *ᵥ v) = S16C11FrQ m v)
    (hblock : s16c11_fr_block m hm M = 1) : (M - 1) ^ 3 = 0 := by
  rw [show (M - 1) ^ 3 = (M - 1) * ((M - 1) * (M - 1)) from by
    rw [show (3:ℕ) = 2 + 1 from rfl, pow_succ, pow_two, mul_assoc]]
  ext i l
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hij : s16c11_frWeight m (s16c11_fr_bound3 hm) i <
      s16c11_frWeight m (s16c11_fr_bound3 hm) j
  · rw [Matrix.mul_apply]
    rw [Finset.sum_eq_zero (fun k _ => ?_), mul_zero]
    by_cases hjk : s16c11_frWeight m (s16c11_fr_bound3 hm) j <
        s16c11_frWeight m (s16c11_fr_bound3 hm) k
    · rw [s16c11_fr_kernel_sub_entry hm hK hQ hblock (i := k) (j := l) (by
        intro hkl
        have hi := s16c11_frWeight_lt_three (s16c11_fr_bound3 hm) i
        have hl := s16c11_frWeight_lt_three (s16c11_fr_bound3 hm) l
        omega), mul_zero]
    · rw [s16c11_fr_kernel_sub_entry hm hK hQ hblock (i := j) (j := k) hjk, zero_mul]
  · rw [s16c11_fr_kernel_sub_entry hm hK hQ hblock (i := i) (j := j) hij, zero_mul]

theorem s16c11_fr_kernel_pow_four {m : ℕ} (hm : m = 3 ∨ m = 4)
    {M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)}
    (hK : ∀ w ∈ s16c11FrLine m, M *ᵥ w = w)
    (hQ : ∀ v : S16C11FrVec m, S16C11FrQ m (M *ᵥ v) = S16C11FrQ m v)
    (hblock : s16c11_fr_block m hm M = 1) : M ^ 4 = 1 := by
  have hN3 : (M - 1) ^ 3 = 0 := s16c11_fr_kernel_nilpotent hm hK hQ hblock
  have hN4 : (M - 1) ^ 4 = 0 := by
    rw [show (4:ℕ) = 3 + 1 from rfl, pow_succ, hN3, zero_mul]
  have h4 : (1 + (M - 1)) ^ 4 = 1 + (M - 1) ^ 4 := by
    have hcomm : Commute (1 : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) (M - 1) :=
      Commute.one_left _
    have h := hcomm.add_pow_prime_pow_eq Nat.prime_two 2
    rw [show (2:ℕ) ^ 2 = 4 from rfl, one_pow] at h
    have h2z : (2 : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2)) = 0 := by
      ext i j
      simp [CharTwo.two_eq_zero]
    simpa [h2z, zero_mul, zero_add] using h
  rw [show M = 1 + (M - 1) from by abel, h4, hN4, add_zero]

theorem s16c11_fr_levi_kernel {m : ℕ} (hm : m = 3 ∨ m = 4) :
    IsPGroup 2 ↥(s16c11_fr_leviHom hm).ker := by
  intro g
  refine ⟨2, ?_⟩
  change g ^ 4 = 1
  let M : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2) :=
    (((g.1.1 : ↥(S16C11FrO m)) : Matrix.GeneralLinearGroup (S16C11FrIdx m) (ZMod 2)) :
      Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2))
  have hM : M ^ 4 = 1 := by
    have hblock : s16c11_fr_block m hm M = 1 := by
      have h1 : ((s16c11_fr_blockUnit hm g.1 :
          Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) :
          Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2)) = 1 := by
        have := congrArg (fun x : ↥(S16C11FrO (m - 2)) =>
          ((x : Matrix.GeneralLinearGroup (S16C11FrIdx (m - 2)) (ZMod 2)) :
            Matrix (S16C11FrIdx (m - 2)) (S16C11FrIdx (m - 2)) (ZMod 2))) g.2
        simpa only [s16c11_fr_leviHom, MonoidHom.mk'_apply, Subgroup.coe_one, Units.val_one]
          using this
      rw [s16c11_fr_blockUnit, Units.val_mkOfMulEqOne] at h1
      exact h1
    exact s16c11_fr_kernel_pow_four hm g.1.2
      (fun v => CFSG.GroupTheory.WeirSylow.apply_mulVec_of_mem_isometryCore g.1.1.2 v) hblock
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_pow, Subgroup.coe_pow, Subgroup.coe_pow, Units.val_pow_eq_pow_val]
  change M ^ 4 = (1 : Matrix (S16C11FrIdx m) (S16C11FrIdx m) (ZMod 2))
  rw [hM]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
