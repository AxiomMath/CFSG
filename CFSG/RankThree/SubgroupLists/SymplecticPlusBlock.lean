module

public import CFSG.RankThree.SubgroupLists.SymplecticInvolutionPairs
public import CFSG.RankThree.SubgroupLists.PointLocalSL2

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.Assembly.LowTwoRank Module
open scoped MatrixGroups

local notation "V₄" => Fin 2 ⊕ Fin 2

variable {K : Type} [Field K]

@[expose] def stdSign : V₄ → K
  | Sum.inl i => if i = 0 then 1 else -1
  | Sum.inr i => if i = 0 then 1 else -1

@[expose] def tStdMat : Matrix V₄ V₄ K := Matrix.diagonal stdSign

theorem tStdMat_mul_self : tStdMat * tStdMat = (1 : Matrix V₄ V₄ K) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tStdMat, stdSign, Matrix.one_apply]

@[expose] def tStd : GL V₄ K := ⟨tStdMat, tStdMat, tStdMat_mul_self, tStdMat_mul_self⟩

theorem coe_tStd : ((tStd : GL V₄ K) : Matrix V₄ V₄ K) = tStdMat := rfl

theorem tStd_mem : (tStd : GL V₄ K) ∈ StatedSp 2 K := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, coe_tStd]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tStdMat, stdSign, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.one_apply]

theorem tStd_mul_self : (tStd : GL V₄ K) * tStd = 1 := Units.ext tStdMat_mul_self

theorem isNCInv_tStd (h2 : (2 : K) ≠ 0) : IsNCInv (tStd : GL V₄ K) := by
  refine ⟨tStd_mem, tStd_mul_self, fun h => ?_, fun h => ?_⟩
  · have := congrFun (congrFun (congrArg (fun x : GL V₄ K => (x : Matrix V₄ V₄ K)) h)
      (Sum.inl 1)) (Sum.inl 1)
    simp [coe_tStd, tStdMat, stdSign] at this
    apply h2
    linear_combination -this
  · have := congrFun (congrFun (congrArg (fun x : GL V₄ K => (x : Matrix V₄ V₄ K)) h)
      (Sum.inl 0)) (Sum.inl 0)
    simp [coe_tStd, tStdMat, stdSign] at this
    apply h2
    linear_combination this

theorem stdSign_sq (i : V₄) : stdSign i * stdSign i = (1 : K) := by
  rcases i with i | i <;> fin_cases i <;> simp [stdSign]

theorem entry_eq_zero_of_commute_tStd (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K}
    (hM : M * tStdMat = tStdMat * M) {i j : V₄} (hij : stdSign i ≠ (stdSign j : K)) :
    M i j = 0 := by
  have h := congrFun (congrFun hM i) j
  simp only [tStdMat, Matrix.mul_diagonal, Matrix.diagonal_mul] at h
  have hsub : M i j * (stdSign j - stdSign i) = 0 := by linear_combination h
  rcases mul_eq_zero.mp hsub with h0 | h0
  · exact h0
  · exact absurd (sub_eq_zero.mp h0).symm hij

@[expose] def plusBlock (M : Matrix V₄ V₄ K) : Matrix (Fin 2) (Fin 2) K :=
  !![M (Sum.inl 0) (Sum.inl 0), M (Sum.inl 0) (Sum.inr 0);
    M (Sum.inr 0) (Sum.inl 0), M (Sum.inr 0) (Sum.inr 0)]

theorem stdSign_inl_zero : stdSign (Sum.inl 0 : V₄) = (1 : K) := by simp [stdSign]
theorem stdSign_inr_zero : stdSign (Sum.inr 0 : V₄) = (1 : K) := by simp [stdSign]
theorem stdSign_inl_one : stdSign (Sum.inl 1 : V₄) = (-1 : K) := by simp [stdSign]
theorem stdSign_inr_one : stdSign (Sum.inr 1 : V₄) = (-1 : K) := by simp [stdSign]

theorem one_ne_neg_one_of_two (h2 : (2 : K) ≠ 0) : (1 : K) ≠ -1 := by
  intro h
  apply h2
  linear_combination h

theorem plusBlock_mul (h2 : (2 : K) ≠ 0) {M N : Matrix V₄ V₄ K}
    (hM : M * tStdMat = tStdMat * M) (hN : N * tStdMat = tStdMat * N) :
    plusBlock (M * N) = plusBlock M * plusBlock N := by
  have hne := one_ne_neg_one_of_two h2
  have z1 : M (Sum.inl 0) (Sum.inl 1) = 0 := entry_eq_zero_of_commute_tStd h2 hM
    (by rw [stdSign_inl_zero, stdSign_inl_one]; exact hne)
  have z2 : M (Sum.inl 0) (Sum.inr 1) = 0 := entry_eq_zero_of_commute_tStd h2 hM
    (by rw [stdSign_inl_zero, stdSign_inr_one]; exact hne)
  have z3 : M (Sum.inr 0) (Sum.inl 1) = 0 := entry_eq_zero_of_commute_tStd h2 hM
    (by rw [stdSign_inr_zero, stdSign_inl_one]; exact hne)
  have z4 : M (Sum.inr 0) (Sum.inr 1) = 0 := entry_eq_zero_of_commute_tStd h2 hM
    (by rw [stdSign_inr_zero, stdSign_inr_one]; exact hne)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusBlock, Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, z1, z2, z3, z4]

theorem plusBlock_one : plusBlock (1 : Matrix V₄ V₄ K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [plusBlock, Matrix.one_apply]

theorem det_plusBlock (h2 : (2 : K) ≠ 0) {g : GL V₄ K} (hg : g ∈ StatedSp 2 K)
    (hgt : (g : Matrix V₄ V₄ K) * tStdMat = tStdMat * (g : Matrix V₄ V₄ K)) :
    (plusBlock (g : Matrix V₄ V₄ K)).det = 1 := by
  have hne := one_ne_neg_one_of_two h2
  have z1 : (g : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inl 0) = 0 :=
    entry_eq_zero_of_commute_tStd h2 hgt (by rw [stdSign_inl_zero, stdSign_inl_one]; exact hne.symm)
  have z2 : (g : Matrix V₄ V₄ K) (Sum.inr 1) (Sum.inl 0) = 0 :=
    entry_eq_zero_of_commute_tStd h2 hgt (by rw [stdSign_inl_zero, stdSign_inr_one]; exact hne.symm)
  have z3 : (g : Matrix V₄ V₄ K) (Sum.inl 1) (Sum.inr 0) = 0 :=
    entry_eq_zero_of_commute_tStd h2 hgt (by rw [stdSign_inr_zero, stdSign_inl_one]; exact hne.symm)
  have z4 : (g : Matrix V₄ V₄ K) (Sum.inr 1) (Sum.inr 0) = 0 :=
    entry_eq_zero_of_commute_tStd h2 hgt (by rw [stdSign_inr_zero, stdSign_inr_one]; exact hne.symm)
  have h := congrFun (congrFun (transpose_mul_spGram_mul hg) (Sum.inl 0)) (Sum.inr 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, spGram, Matrix.fromBlocks, Matrix.one_apply,
    z1, z2, z3, z4] at h
  rw [plusBlock, Matrix.det_fin_two_of]
  linear_combination h

@[expose] def stdCent (K : Type) [Field K] : Subgroup (GL V₄ K) :=
  StatedSp 2 K ⊓ Subgroup.centralizer {tStd}

theorem mem_stdCent {g : GL V₄ K} :
    g ∈ stdCent K ↔
      g ∈ StatedSp 2 K ∧ (g : Matrix V₄ V₄ K) * tStdMat = tStdMat * (g : Matrix V₄ V₄ K) := by
  rw [stdCent, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    have := congrArg (fun x : GL V₄ K => (x : Matrix V₄ V₄ K)) h2
    simpa [coe_tStd] using this
  · rintro ⟨h1, h2⟩
    refine ⟨h1, Units.ext ?_⟩
    simpa [coe_tStd] using h2

@[expose] noncomputable def plusHom (h2 : (2 : K) ≠ 0) : stdCent K →* SL(2, K) where
  toFun g := ⟨plusBlock ((g : GL V₄ K) : Matrix V₄ V₄ K),
    det_plusBlock h2 (mem_stdCent.mp g.2).1 (mem_stdCent.mp g.2).2⟩
  map_one' := by
    ext i j
    simp [plusBlock_one]
  map_mul' g h := by
    apply Subtype.ext
    change plusBlock (((g : GL V₄ K) : Matrix V₄ V₄ K) * ((h : GL V₄ K) : Matrix V₄ V₄ K)) =
      plusBlock ((g : GL V₄ K) : Matrix V₄ V₄ K) * plusBlock ((h : GL V₄ K) : Matrix V₄ V₄ K)
    exact plusBlock_mul h2 (mem_stdCent.mp g.2).2 (mem_stdCent.mp h.2).2

theorem coe_plusHom (h2 : (2 : K) ≠ 0) (g : stdCent K) :
    ((plusHom h2 g : SL(2, K)) : Matrix (Fin 2) (Fin 2) K) =
      plusBlock ((g : GL V₄ K) : Matrix V₄ V₄ K) := rfl

theorem exists_spForm_eq_one_of_eig (h2 : (2 : K) ≠ 0) {u : GL V₄ K} (hu : IsNCInv u) (μ : K)
    (hμ : μ = 1 ∨ μ = -1) :
    ∃ a ∈ eigSp (u : Matrix V₄ V₄ K) μ, ∃ b ∈ eigSp (u : Matrix V₄ V₄ K) μ,
      spForm 2 K a b = 1 := by
  classical
  have huu : (u : Matrix V₄ V₄ K) * u = 1 := by rw [← Units.val_mul, hu.2.1, Units.val_one]
  have hm2 := finrank_eig_neg_one_eq_two h2 hu.1 hu.2.1 hu.2.2.1 hu.2.2.2
  have hp2 : finrank K (eigSp (u : Matrix V₄ V₄ K) 1) = 2 := by
    have := finrank_eig_add_finrank_eig h2 huu
    omega
  have hdim : finrank K (eigSp (u : Matrix V₄ V₄ K) μ) = 2 := by
    rcases hμ with rfl | rfl
    · exact hp2
    · exact hm2
  obtain ⟨v, hv0⟩ : ∃ v : eigSp (u : Matrix V₄ V₄ K) μ, v ≠ 0 := by
    have : Nontrivial (eigSp (u : Matrix V₄ V₄ K) μ) := by
      apply Module.nontrivial_of_finrank_pos (R := K)
      omega
    exact exists_ne 0
  have hv0' : (v : V₄ → K) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨y, hy⟩ : ∃ y, spForm 2 K (v : V₄ → K) y ≠ 0 := by
    by_contra h
    push Not at h
    apply hv0'
    apply eq_zero_of_forall_spForm
    intro x
    rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, h x, neg_zero]
  obtain ⟨y₁, y₂, hysum⟩ := mem_eig_add_mem_eig h2 huu y
  set w₁ := (2 : K)⁻¹ • (y + (u : Matrix V₄ V₄ K) *ᵥ y)
  set w₂ := (2 : K)⁻¹ • (y - (u : Matrix V₄ V₄ K) *ᵥ y)
  have hpair : ∃ w ∈ eigSp (u : Matrix V₄ V₄ K) μ, spForm 2 K (v : V₄ → K) w ≠ 0 := by
    rcases hμ with rfl | rfl
    · refine ⟨w₁, y₁, ?_⟩
      have h0 : spForm 2 K (v : V₄ → K) w₂ = 0 := spForm_eq_zero_of_eig h2 hu.1 v.2 y₂
      rw [hysum, map_add, h0, add_zero] at hy
      exact hy
    · refine ⟨w₂, y₂, ?_⟩
      have h0 : spForm 2 K (v : V₄ → K) w₁ = 0 := by
        rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt,
          spForm_eq_zero_of_eig h2 hu.1 y₁ v.2, neg_zero]
      rw [hysum, map_add, h0, zero_add] at hy
      exact hy
  obtain ⟨w, hw, hvw⟩ := hpair
  refine ⟨v, v.2, (spForm 2 K (v : V₄ → K) w)⁻¹ • w,
    Submodule.smul_mem _ _ hw, ?_⟩
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hvw]

theorem exists_conj_eq_tStd (h2 : (2 : K) ≠ 0) {u : GL V₄ K} (hu : IsNCInv u) :
    ∃ h ∈ StatedSp 2 K, h * tStd * h⁻¹ = u := by
  classical
  obtain ⟨a₁, ha₁, b₁, hb₁, hab₁⟩ := exists_spForm_eq_one_of_eig h2 hu 1 (Or.inl rfl)
  obtain ⟨a₂, ha₂, b₂, hb₂, hab₂⟩ := exists_spForm_eq_one_of_eig h2 hu (-1) (Or.inr rfl)
  let c : V₄ → (V₄ → K) := fun j => match j with
    | Sum.inl 0 => a₁ | Sum.inl 1 => a₂ | Sum.inr 0 => b₁ | Sum.inr 1 => b₂
  let H : Matrix V₄ V₄ K := Matrix.of fun i j => c j i
  have hcol : ∀ j, H *ᵥ Pi.single j 1 = c j := by
    intro j
    ext i
    simp [H, Matrix.mulVec, dotProduct, Pi.single_apply]
  have horth : ∀ x ∈ eigSp (u : Matrix V₄ V₄ K) 1, ∀ y ∈ eigSp (u : Matrix V₄ V₄ K) (-1),
      spForm 2 K x y = 0 ∧ spForm 2 K y x = 0 := fun x hx y hy =>
    ⟨spForm_eq_zero_of_eig h2 hu.1 hx hy, by
      rw [← LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt, spForm_eq_zero_of_eig h2 hu.1 hx hy,
        neg_zero]⟩
  have hanti : ∀ x y : V₄ → K, spForm 2 K y x = -spForm 2 K x y := fun x y =>
    (LinearMap.BilinForm.IsAlt.neg_eq spForm_isAlt x y).symm
  have hgram : Hᵀ * spGram 2 K * H = spGram 2 K := by
    have key : ∀ j k, (Hᵀ * spGram 2 K * H) j k = spForm 2 K (c j) (c k) := by
      intro j k
      rw [spForm, Matrix.toBilin'_apply']
      simp [H, Matrix.mul_apply, dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul,
        mul_comm, mul_left_comm, mul_assoc]
      ring
    ext j k
    rw [key]
    rcases j with j | j <;> rcases k with k | k <;> fin_cases j <;> fin_cases k <;>
      simp [c, spGram, Matrix.fromBlocks, Matrix.one_apply, spForm_self, hab₁, hab₂,
        hanti a₁ b₁, hanti a₂ b₂, (horth _ ha₁ _ ha₂).1, (horth _ ha₁ _ hb₂).1,
        (horth _ hb₁ _ ha₂).1, (horth _ hb₁ _ hb₂).1, (horth _ ha₁ _ ha₂).2,
        (horth _ ha₁ _ hb₂).2, (horth _ hb₁ _ ha₂).2, (horth _ hb₁ _ hb₂).2]
  set Hinv : Matrix V₄ V₄ K := -(spGram 2 K * Hᵀ * spGram 2 K) with hHinv
  have hJJ : spGram 2 K * spGram 2 K = -(1 : Matrix V₄ V₄ K) := by
    ext i j
    rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
      simp [spGram, Matrix.fromBlocks, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  have hinvH : Hinv * H = 1 := by
    rw [hHinv, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc Hᵀ, hgram,
      hJJ, neg_neg]
  have hHinv' : H * Hinv = 1 := mul_eq_one_comm.mp hinvH
  let h : GL V₄ K := ⟨H, Hinv, hHinv', hinvH⟩
  have hhS : h ∈ StatedSp 2 K := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff]
    exact hgram
  refine ⟨h, hhS, ?_⟩
  have hcomm : (u : Matrix V₄ V₄ K) * H = H * tStdMat := by
    refine Matrix.ext_of_mulVec_single fun j => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have htj : tStdMat *ᵥ (Pi.single j 1 : V₄ → K) = (stdSign j : K) • Pi.single j 1 := by
      ext i
      simp [tStdMat, Matrix.mulVec_diagonal, Pi.single_apply]
      split_ifs with h <;> simp [h]
    rw [htj, Matrix.mulVec_smul, hcol]
    rcases j with j | j <;> fin_cases j
    · simpa [c, stdSign] using mem_eigSp.mp ha₁
    · simpa [c, stdSign] using mem_eigSp.mp ha₂
    · simpa [c, stdSign] using mem_eigSp.mp hb₁
    · simpa [c, stdSign] using mem_eigSp.mp hb₂
  apply Units.ext
  show H * tStdMat * Hinv = (u : Matrix V₄ V₄ K)
  rw [← hcomm, Matrix.mul_assoc, hHinv', Matrix.mul_one]

@[expose] def swapIdx : V₄ → V₄
  | Sum.inl i => Sum.inl (Equiv.swap 0 1 i)
  | Sum.inr i => Sum.inr (Equiv.swap 0 1 i)

theorem swapIdx_swapIdx (i : V₄) : swapIdx (swapIdx i) = i := by
  rcases i with i | i <;> simp [swapIdx]

@[expose] def swapMat : Matrix V₄ V₄ K := Matrix.of fun i j => if j = swapIdx i then 1 else 0

theorem swapMat_mul_apply (M : Matrix V₄ V₄ K) (i j : V₄) :
    ((swapMat : Matrix V₄ V₄ K) * M) i j = M (swapIdx i) j := by
  simp [swapMat, Matrix.mul_apply]

theorem mul_swapMat_apply (M : Matrix V₄ V₄ K) (i j : V₄) :
    (M * (swapMat : Matrix V₄ V₄ K)) i j = M i (swapIdx j) := by
  simp only [swapMat, Matrix.mul_apply, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (swapIdx j)]
  · simp [swapIdx_swapIdx]
  · intro b _ hb
    rw [if_neg]
    intro h
    apply hb
    rw [h, swapIdx_swapIdx]
  · simp

theorem swapMat_mul_self : (swapMat : Matrix V₄ V₄ K) * swapMat = 1 := by
  ext i j
  rw [swapMat_mul_apply]
  simp only [swapMat, Matrix.of_apply, Matrix.one_apply, swapIdx_swapIdx]
  by_cases h : i = j
  · subst h
    simp
  · have h' : j ≠ i := fun e => h e.symm
    simp [h, h']

theorem swapMat_transpose : (swapMat : Matrix V₄ V₄ K)ᵀ = swapMat := by
  ext i j
  simp only [Matrix.transpose_apply, swapMat, Matrix.of_apply]
  by_cases h : j = swapIdx i
  · have h' : i = swapIdx j := by rw [h, swapIdx_swapIdx]
    rw [if_pos h, if_pos h']
  · have h' : ¬ i = swapIdx j := fun h' => h (by rw [h', swapIdx_swapIdx])
    rw [if_neg h, if_neg h']

@[expose] def swapGL : GL V₄ K := ⟨swapMat, swapMat, swapMat_mul_self, swapMat_mul_self⟩

theorem coe_swapGL : ((swapGL : GL V₄ K) : Matrix V₄ V₄ K) = swapMat := rfl

theorem swapGL_inv : (swapGL : GL V₄ K)⁻¹ = swapGL := inv_eq_of_mul_eq_one_right
  (Units.ext swapMat_mul_self)

theorem swap_conj_apply (M : Matrix V₄ V₄ K) (i j : V₄) :
    (swapMat * M * swapMat : Matrix V₄ V₄ K) i j = M (swapIdx i) (swapIdx j) := by
  rw [mul_swapMat_apply, swapMat_mul_apply]

theorem swapGL_mem : (swapGL : GL V₄ K) ∈ StatedSp 2 K := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl.mem_statedSp_iff, coe_swapGL,
    swapMat_transpose]
  ext i j
  rw [swap_conj_apply]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [swapIdx, Matrix.fromBlocks, Matrix.one_apply, Equiv.swap_apply_def]

theorem swap_conj_tStdMat :
    (swapMat : Matrix V₄ V₄ K) * tStdMat * swapMat = -(tStdMat : Matrix V₄ V₄ K) := by
  ext i j
  rw [swap_conj_apply]
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tStdMat, stdSign, swapIdx, Equiv.swap_apply_def]

@[expose] def minusBlock (M : Matrix V₄ V₄ K) : Matrix (Fin 2) (Fin 2) K :=
  !![M (Sum.inl 1) (Sum.inl 1), M (Sum.inl 1) (Sum.inr 1);
    M (Sum.inr 1) (Sum.inl 1), M (Sum.inr 1) (Sum.inr 1)]

theorem plusBlock_swap_conj (M : Matrix V₄ V₄ K) :
    plusBlock ((swapMat : Matrix V₄ V₄ K) * M * swapMat) = minusBlock M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusBlock, minusBlock, swap_conj_apply, swapIdx, Equiv.swap_apply_def]

theorem eq_of_blocks (h2 : (2 : K) ≠ 0) {M : Matrix V₄ V₄ K} (hM : M * tStdMat = tStdMat * M)
    {a b : K} (hp : plusBlock M = a • 1) (hm : minusBlock M = b • 1) :
    M = (2 : K)⁻¹ • (a • (1 + tStdMat) + b • (1 - tStdMat)) := by
  have hne := one_ne_neg_one_of_two h2
  have hz : ∀ i j : V₄, stdSign i ≠ (stdSign j : K) → M i j = 0 := fun i j h =>
    entry_eq_zero_of_commute_tStd h2 hM h
  have hp' := fun i j => congrFun (congrFun hp i) j
  have hm' := fun i j => congrFun (congrFun hm i) j
  simp only [plusBlock, minusBlock, Matrix.smul_apply, Matrix.one_apply] at hp' hm'
  ext i j
  have h22 : (2 : K)⁻¹ * 2 = 1 := inv_mul_cancel₀ h2
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [tStdMat, stdSign, Matrix.one_apply] <;>
    first
    | (have := hp' 0 0; simp at this; rw [this]; field_simp; ring)
    | (have := hp' 0 1; simp at this; rw [this])
    | (have := hp' 1 0; simp at this; rw [this])
    | (have := hp' 1 1; simp at this; rw [this]; field_simp; ring)
    | (have := hm' 0 0; simp at this; rw [this]; field_simp; ring)
    | (have := hm' 0 1; simp at this; rw [this])
    | (have := hm' 1 0; simp at this; rw [this])
    | (have := hm' 1 1; simp at this; rw [this]; field_simp; ring)
    | (rw [hz _ _ (by simp [stdSign]; exact hne)])
    | (rw [hz _ _ (by simp [stdSign]; exact hne.symm)])

end CFSG.RankThree.SubgroupLists
