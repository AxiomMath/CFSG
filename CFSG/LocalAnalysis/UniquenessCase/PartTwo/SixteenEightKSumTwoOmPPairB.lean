module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumTwoOmPPairA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3GoodOrthPair
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open Matrix

variable {K : Type} [Field K] {m : ℕ}

private theorem s16k_conj_mulVec {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (g f : GL ι K) (v : ι → K) :
    (((g⁻¹ * f * g : GL ι K) : Matrix ι ι K)) *ᵥ
        (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) =
      ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ (((f : GL ι K) : Matrix ι ι K) *ᵥ v) := by
  change (g⁻¹ * f * g) • (g⁻¹ • v) = g⁻¹ • (f • v)
  rw [mul_smul]
  conv_lhs => arg 2; rw [← mul_smul, mul_inv_cancel, one_smul]
  rw [mul_smul]

private theorem s16k_swap_swap {α β : Type} (r : α ⊕ β) : Sum.swap (Sum.swap r) = r := by
  cases r <;> rfl

theorem s16k_exists_group_fixing_base {K : Type} [Field K] [Finite K] [CharP K 2]
    {m : ℕ} (hm : 4 ≤ m) (i0 : Fin m) {base z : Fin m ⊕ Fin m → K}
    (hbase : ∀ v : Fin m ⊕ Fin m → K, v (Sum.inl i0) = 0 → v (Sum.inr i0) = 0 →
      base ⬝ᵥ (plusM m K *ᵥ v) = 0) :
    ∃ F : Subgroup (GL (Fin m ⊕ Fin m) K), F ≤ StatedOmega (StatedQuadPlus m K) ∧
      IsPGroup 3 ↥F ∧ ¬ IsCyclic ↥F ∧
      ∀ f ∈ F, (f : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ base = base ∧
        (f : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ z = z := by
  classical
  set c₀ : K := z (Sum.inl i0) with hc₀
  set d₀ : K := z (Sum.inr i0) with hd₀
  set w : Fin m ⊕ Fin m → K :=
    z - c₀ • (Pi.single (Sum.inl i0) 1) - d₀ • (Pi.single (Sum.inr i0) 1) with hw
  have hzdecomp : z = c₀ • (Pi.single (Sum.inl i0) 1) + d₀ • (Pi.single (Sum.inr i0) 1) + w := by
    rw [hw]; abel
  have hw_inl : w (Sum.inl i0) = 0 := by
    rw [hw]; simp [hc₀, hd₀]
  have hw_inr : w (Sum.inr i0) = 0 := by
    rw [hw]; simp [hc₀, hd₀]
  have hzw : ∀ v : Fin m ⊕ Fin m → K, v (Sum.inl i0) = 0 → v (Sum.inr i0) = 0 →
      z ⬝ᵥ (plusM m K *ᵥ v) = w ⬝ᵥ (plusM m K *ᵥ v) := by
    intro v hv1 hv2
    rw [hzdecomp]
    simp only [add_dotProduct, smul_dotProduct, s16k_single_inl_dot, s16k_single_inr_dot,
      hv1, hv2, smul_eq_mul, mul_zero, zero_add]
  by_cases hw0 : w = 0
  · obtain ⟨i, j, hij, hi0, _, hj0, _⟩ := s16k_exists_two_ne hm i0 i0
    have ha : StatedQuadPlus m K (plusA i) = 1 := Q_plusA i
    have hb : StatedQuadPlus m K (plusB i j) = 1 := Q_plusB hij
    have hc : StatedQuadPlus m K (plusA j) = 1 := Q_plusA j
    have hd : StatedQuadPlus m K (s16k_plusD (K := K) i j) = 1 := s16k_Q_plusD hij
    have hab : plusA i ⬝ᵥ (plusM m K *ᵥ plusB i j) = 1 := B_plus hij
    have hcd : plusA j ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 1 := s16k_B_plusD hij
    have hac : plusA i ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := s16k_dot_plusA_plusA hij
    have had : plusA i ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 0 :=
      s16k_dot_plusA_plusD hij
    have hbc : plusB i j ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := s16k_dot_plusB_plusA hij
    have hbd : plusB i j ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 0 :=
      s16k_dot_plusB_plusD hij
    have hAi : (plusA i : Fin m ⊕ Fin m → K) (Sum.inl i0) = 0 :=
      plusA_apply_eq_zero (by simpa [plusIdx] using hi0.symm)
    have hAi' : (plusA i : Fin m ⊕ Fin m → K) (Sum.inr i0) = 0 :=
      plusA_apply_eq_zero (by simpa [plusIdx] using hi0.symm)
    have hAj : (plusA j : Fin m ⊕ Fin m → K) (Sum.inl i0) = 0 :=
      plusA_apply_eq_zero (by simpa [plusIdx] using hj0.symm)
    have hAj' : (plusA j : Fin m ⊕ Fin m → K) (Sum.inr i0) = 0 :=
      plusA_apply_eq_zero (by simpa [plusIdx] using hj0.symm)
    have hB : (plusB i j : Fin m ⊕ Fin m → K) (Sum.inl i0) = 0 :=
      plusB_apply_eq_zero (by simpa [plusIdx] using hi0.symm) (by simpa [plusIdx] using hj0.symm)
    have hB' : (plusB i j : Fin m ⊕ Fin m → K) (Sum.inr i0) = 0 :=
      plusB_apply_eq_zero (by simpa [plusIdx] using hi0.symm) (by simpa [plusIdx] using hj0.symm)
    have hD : (s16k_plusD (K := K) i j) (Sum.inl i0) = 0 :=
      s16k_plusD_apply_eq_zero (by simpa [plusIdx] using hi0.symm)
        (by simpa [plusIdx] using hj0.symm)
    have hD' : (s16k_plusD (K := K) i j) (Sum.inr i0) = 0 :=
      s16k_plusD_apply_eq_zero (by simpa [plusIdx] using hi0.symm)
        (by simpa [plusIdx] using hj0.symm)
    obtain ⟨F, hFΓ, hFp, hFc, hFfix⟩ :=
      s16t3_exists_pair_omega isQuadWith_plus ha hb hc hd hab hcd hac had hbc hbd
    refine ⟨F, hFΓ, hFp, hFc, ?_⟩
    intro f hf
    have hza : z ⬝ᵥ (plusM m K *ᵥ plusA i) = 0 := by
      rw [hzw _ hAi hAi', hw0]; simp
    have hzb : z ⬝ᵥ (plusM m K *ᵥ plusB i j) = 0 := by
      rw [hzw _ hB hB', hw0]; simp
    have hzc : z ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := by
      rw [hzw _ hAj hAj', hw0]; simp
    have hzd : z ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 0 := by
      rw [hzw _ hD hD', hw0]; simp
    exact ⟨hFfix base (hbase _ hAi hAi') (hbase _ hB hB') (hbase _ hAj hAj')
        (hbase _ hD hD') f hf, hFfix z hza hzb hzc hzd f hf⟩
  · obtain ⟨r, hr⟩ := Function.ne_iff.mp hw0
    have hri0 : plusIdx r ≠ i0 := by
      intro h
      rcases r with c | c
      · have hc : c = i0 := by simpa [plusIdx] using h
        rw [hc] at hr
        exact hr hw_inl
      · have hc : c = i0 := by simpa [plusIdx] using h
        rw [hc] at hr
        exact hr hw_inr
    obtain ⟨i, j, hij, hi0, hir, hj0, hjr⟩ := s16k_exists_two_ne hm i0 (plusIdx r)
    set wc : Fin m ⊕ Fin m → K := Pi.single (Sum.swap r) 1 with hwc
    have hwcQ : StatedQuadPlus m K wc = 0 := by rw [hwc]; exact Q_single _
    have hwcw : w ⬝ᵥ (plusM m K *ᵥ wc) ≠ 0 := by
      rw [hwc, dot_plusM_single]; exact hr
    have ha : StatedQuadPlus m K (plusA i) = 1 := Q_plusA i
    have hb : StatedQuadPlus m K (plusB i j) = 1 := Q_plusB hij
    have hc : StatedQuadPlus m K (plusA j) = 1 := Q_plusA j
    have hd : StatedQuadPlus m K (s16k_plusD (K := K) i j) = 1 := s16k_Q_plusD hij
    have hab : plusA i ⬝ᵥ (plusM m K *ᵥ plusB i j) = 1 := B_plus hij
    have hcd : plusA j ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 1 := s16k_B_plusD hij
    have hac : plusA i ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := s16k_dot_plusA_plusA hij
    have had : plusA i ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 0 :=
      s16k_dot_plusA_plusD hij
    have hbc : plusB i j ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := s16k_dot_plusB_plusA hij
    have hbd : plusB i j ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 0 :=
      s16k_dot_plusB_plusD hij
    have hAi : (plusA i : Fin m ⊕ Fin m → K) (Sum.inl i0) = 0 :=
      plusA_apply_eq_zero (by simpa [plusIdx] using hi0.symm)
    have hAi' : (plusA i : Fin m ⊕ Fin m → K) (Sum.inr i0) = 0 :=
      plusA_apply_eq_zero (by simpa [plusIdx] using hi0.symm)
    have hAj : (plusA j : Fin m ⊕ Fin m → K) (Sum.inl i0) = 0 :=
      plusA_apply_eq_zero (by simpa [plusIdx] using hj0.symm)
    have hAj' : (plusA j : Fin m ⊕ Fin m → K) (Sum.inr i0) = 0 :=
      plusA_apply_eq_zero (by simpa [plusIdx] using hj0.symm)
    have hB : (plusB i j : Fin m ⊕ Fin m → K) (Sum.inl i0) = 0 :=
      plusB_apply_eq_zero (by simpa [plusIdx] using hi0.symm) (by simpa [plusIdx] using hj0.symm)
    have hB' : (plusB i j : Fin m ⊕ Fin m → K) (Sum.inr i0) = 0 :=
      plusB_apply_eq_zero (by simpa [plusIdx] using hi0.symm) (by simpa [plusIdx] using hj0.symm)
    have hD : (s16k_plusD (K := K) i j) (Sum.inl i0) = 0 :=
      s16k_plusD_apply_eq_zero (by simpa [plusIdx] using hi0.symm)
        (by simpa [plusIdx] using hj0.symm)
    have hD' : (s16k_plusD (K := K) i j) (Sum.inr i0) = 0 :=
      s16k_plusD_apply_eq_zero (by simpa [plusIdx] using hi0.symm)
        (by simpa [plusIdx] using hj0.symm)
    have hwc_a : wc ⬝ᵥ (plusM m K *ᵥ plusA i) = 0 := by
      rw [hwc, single_dot_plusM, s16k_swap_swap]
      exact plusA_apply_eq_zero hir.symm
    have hwc_b : wc ⬝ᵥ (plusM m K *ᵥ plusB i j) = 0 := by
      rw [hwc, single_dot_plusM, s16k_swap_swap]
      exact plusB_apply_eq_zero hir.symm hjr.symm
    have hwc_c : wc ⬝ᵥ (plusM m K *ᵥ plusA j) = 0 := by
      rw [hwc, single_dot_plusM, s16k_swap_swap]
      exact plusA_apply_eq_zero hjr.symm
    have hwc_d : wc ⬝ᵥ (plusM m K *ᵥ s16k_plusD (K := K) i j) = 0 := by
      rw [hwc, single_dot_plusM, s16k_swap_swap]
      exact s16k_plusD_apply_eq_zero hir.symm hjr.symm
    have hwc_inl : wc (Sum.inl i0) = 0 := by
      rw [hwc, Pi.single_apply, if_neg]
      intro h
      have h1 := congrArg Sum.swap h
      rw [s16k_swap_swap] at h1
      exact hri0 (by rw [← h1]; simp [plusIdx])
    have hwc_inr : wc (Sum.inr i0) = 0 := by
      rw [hwc, Pi.single_apply, if_neg]
      intro h
      have h1 := congrArg Sum.swap h
      rw [s16k_swap_swap] at h1
      exact hri0 (by rw [← h1]; simp [plusIdx])
    obtain ⟨b₁, b₁', b₂, b₂', hb₁eq, hb₁'eq, hb₂eq, hb₂'eq,
      h1, h1', h11, h2, h2', h22, h12, h12', h1'2, h1'2', hv1, hv1', hv2, hv2'⟩ :=
      s16k_pairs_of_singular_explicit isQuadWith_plus ha hb hab hc hd hcd hac had hbc hbd
        hwcQ hwc_a hwc_b hwc_c hwc_d hwcw
    have hb₁_inl : b₁ (Sum.inl i0) = 0 := by rw [hb₁eq]; simp [hAi, hwc_inl]
    have hb₁_inr : b₁ (Sum.inr i0) = 0 := by rw [hb₁eq]; simp [hAi', hwc_inr]
    have hb₁'_inl : b₁' (Sum.inl i0) = 0 := by rw [hb₁'eq]; simp [hB, hwc_inl]
    have hb₁'_inr : b₁' (Sum.inr i0) = 0 := by rw [hb₁'eq]; simp [hB', hwc_inr]
    have hb₂_inl : b₂ (Sum.inl i0) = 0 := by rw [hb₂eq]; simp [hAj, hwc_inl]
    have hb₂_inr : b₂ (Sum.inr i0) = 0 := by rw [hb₂eq]; simp [hAj', hwc_inr]
    have hb₂'_inl : b₂' (Sum.inl i0) = 0 := by rw [hb₂'eq]; simp [hD, hwc_inl]
    have hb₂'_inr : b₂' (Sum.inr i0) = 0 := by rw [hb₂'eq]; simp [hD', hwc_inr]
    have hz₁ : z ⬝ᵥ (plusM m K *ᵥ b₁) = 0 := by
      rw [hzw b₁ hb₁_inl hb₁_inr, hv1]
    have hz₁' : z ⬝ᵥ (plusM m K *ᵥ b₁') = 0 := by
      rw [hzw b₁' hb₁'_inl hb₁'_inr, hv1']
    have hz₂ : z ⬝ᵥ (plusM m K *ᵥ b₂) = 0 := by
      rw [hzw b₂ hb₂_inl hb₂_inr, hv2]
    have hz₂' : z ⬝ᵥ (plusM m K *ᵥ b₂') = 0 := by
      rw [hzw b₂' hb₂'_inl hb₂'_inr, hv2']
    have hbase₁ : base ⬝ᵥ (plusM m K *ᵥ b₁) = 0 := by
      rw [hb₁eq, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
        hbase (plusA i) hAi hAi', hbase wc hwc_inl hwc_inr]
      simp
    have hbase₁' : base ⬝ᵥ (plusM m K *ᵥ b₁') = 0 := by
      rw [hb₁'eq, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
        hbase (plusB i j) hB hB', hbase wc hwc_inl hwc_inr]
      simp
    have hbase₂ : base ⬝ᵥ (plusM m K *ᵥ b₂) = 0 := by
      rw [hb₂eq, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
        hbase (plusA j) hAj hAj', hbase wc hwc_inl hwc_inr]
      simp
    have hbase₂' : base ⬝ᵥ (plusM m K *ᵥ b₂') = 0 := by
      rw [hb₂'eq, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, dotProduct_smul,
        hbase (s16k_plusD (K := K) i j) hD hD', hbase wc hwc_inl hwc_inr]
      simp
    obtain ⟨F, hFΓ, hFp, hFc, hFfix⟩ :=
      s16t3_exists_pair_omega isQuadWith_plus h1 h1' h2 h2' h11 h22 h12 h12' h1'2 h1'2'
    exact ⟨F, hFΓ, hFp, hFc, fun f hf =>
      ⟨hFfix base hbase₁ hbase₁' hbase₂ hbase₂' f hf,
        hFfix z hz₁ hz₁' hz₂ hz₂' f hf⟩⟩

theorem s16k_conj_group {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    (Γ : Subgroup (GL ι K)) {F : Subgroup (GL ι K)} (hF : F ≤ Γ) {g : GL ι K} (hg : g ∈ Γ)
    (hFp : IsPGroup 3 ↥F) (hFc : ¬ IsCyclic ↥F)
    {v w : ι → K} (hfix : ∀ f ∈ F, (f : Matrix ι ι K) *ᵥ v = v ∧
      (f : Matrix ι ι K) *ᵥ w = w) :
    ∃ F' : Subgroup (GL ι K), F' ≤ Γ ∧ IsPGroup 3 ↥F' ∧ ¬ IsCyclic ↥F' ∧
      ∀ f' ∈ F', (f' : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) =
          ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v ∧
        (f' : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) =
          ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w := by
  refine ⟨F.map (MulAut.conj g⁻¹).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hx
    change (MulAut.conj g⁻¹) f ∈ Γ
    rw [MulAut.conj_apply, inv_inv]
    exact Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (hF hf)) hg
  · exact hFp.of_equiv (Subgroup.equivMapOfInjective F (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective)
  · intro hcyc
    exact hFc ((Subgroup.equivMapOfInjective F (MulAut.conj g⁻¹).toMonoidHom
      (MulAut.conj g⁻¹).injective).isCyclic.mpr hcyc)
  · intro f' hf'
    obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp hf'
    refine ⟨?_, ?_⟩
    · change (((MulAut.conj g⁻¹) f : GL ι K) : Matrix ι ι K) *ᵥ
          (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v) = ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ v
      rw [MulAut.conj_apply, inv_inv, s16k_conj_mulVec, (hfix f hf).1]
    · change (((MulAut.conj g⁻¹) f : GL ι K) : Matrix ι ι K) *ᵥ
          (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) = ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w
      rw [MulAut.conj_apply, inv_inv, s16k_conj_mulVec, (hfix f hf).2]

theorem s16k_fix_two {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ} (hm : 4 ≤ m)
    {u z : Fin m ⊕ Fin m → K} (hu : u ≠ 0) :
    ∃ F : Subgroup (GL (Fin m ⊕ Fin m) K), F ≤ StatedOmega (StatedQuadPlus m K) ∧
      IsPGroup 3 ↥F ∧ ¬ IsCyclic ↥F ∧
      ∀ f ∈ F, (f : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u = u ∧
        (f : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ z = z := by
  let i0 : Fin m := ⟨0, by omega⟩
  by_cases hQu : StatedQuadPlus m K u = 0
  · have he0 : (Pi.single (Sum.inl i0) 1 : Fin m ⊕ Fin m → K) ≠ 0 := by
      intro h
      have := congrFun h (Sum.inl i0)
      simp at this
    have hxy : CFSG.LieType.Universal.Spin.quadPlus m K u =
        CFSG.LieType.Universal.Spin.quadPlus m K
          (Pi.single (Sum.inl i0) 1 : Fin m ⊕ Fin m → K) := by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus, hQu, Q_single]
    obtain ⟨A, hA, hAu⟩ := CFSG.ClassicalGroups.Orthogonal.statedOmegaPlus_exists_mulVec_eq
      (m := m) (by omega) hu he0 hxy
    have hbase : ∀ v : Fin m ⊕ Fin m → K, v (Sum.inl i0) = 0 → v (Sum.inr i0) = 0 →
        (Pi.single (Sum.inl i0) 1 : Fin m ⊕ Fin m → K) ⬝ᵥ (plusM m K *ᵥ v) = 0 := by
      intro v _ hv2
      rw [single_dot_plusM]
      simpa using hv2
    obtain ⟨F, hFΓ, hFp, hFc, hFfix⟩ := s16k_exists_group_fixing_base hm i0 hbase
      (z := (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ z)
    have hAΓ : A ∈ StatedOmega (StatedQuadPlus m K) := hA
    obtain ⟨F', hF'Γ, hF'p, hF'c, hF'fix⟩ :=
      s16k_conj_group (StatedOmega (StatedQuadPlus m K)) hFΓ hAΓ hFp hFc hFfix
    refine ⟨F', hF'Γ, hF'p, hF'c, ?_⟩
    intro f hf
    have hfix' := hF'fix f hf
    have hAu_inv : ((A⁻¹ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        (Pi.single (Sum.inl i0) 1 : Fin m ⊕ Fin m → K) = u := by
      rw [← hAu, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hz_inv : ((A⁻¹ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        (((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hAu_inv] at hfix'
    rw [hz_inv] at hfix'
    exact hfix'
  · have hQu' : CFSG.LieType.Universal.Spin.quadPlus m K u ≠ 0 := by
      simpa [CFSG.LieType.Universal.Spin.coe_quadPlus] using hQu
    have hy : CFSG.LieType.Universal.Spin.quadPlus m K (plusA i0) ≠ 0 := by
      rw [CFSG.LieType.Universal.Spin.coe_quadPlus, Q_plusA]
      exact one_ne_zero
    obtain ⟨A, hA, c, _hc, hAu⟩ :=
      CFSG.ClassicalGroups.Orthogonal.statedOmegaPlus_exists_mulVec_eq_smul
        (m := m) (by omega) hQu' hy
    have hbase : ∀ v : Fin m ⊕ Fin m → K, v (Sum.inl i0) = 0 → v (Sum.inr i0) = 0 →
        (c • plusA i0) ⬝ᵥ (plusM m K *ᵥ v) = 0 := by
      intro v hv1 hv2
      rw [smul_dotProduct]
      unfold plusA
      rw [add_dotProduct, s16k_single_inl_dot, s16k_single_inr_dot, hv1, hv2]
      ring
    obtain ⟨F, hFΓ, hFp, hFc, hFfix⟩ := s16k_exists_group_fixing_base hm i0 hbase
      (z := (A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ z)
    have hAΓ : A ∈ StatedOmega (StatedQuadPlus m K) := hA
    obtain ⟨F', hF'Γ, hF'p, hF'c, hF'fix⟩ :=
      s16k_conj_group (StatedOmega (StatedQuadPlus m K)) hFΓ hAΓ hFp hFc hFfix
    refine ⟨F', hF'Γ, hF'p, hF'c, ?_⟩
    intro f hf
    have hfix' := hF'fix f hf
    have hAu_inv : ((A⁻¹ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ (c • plusA i0) = u := by
      rw [← hAu, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    have hz_inv : ((A⁻¹ : GL (Fin m ⊕ Fin m) K) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
        (((A : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ z) = z := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.one_mulVec]
    rw [hAu_inv] at hfix'
    rw [hz_inv] at hfix'
    exact hfix'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
