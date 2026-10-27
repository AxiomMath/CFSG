module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherMaximalParabolics
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.ASVolI

open Matrix Subgroup CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section RowCol

variable {K : Type} [Field K]

theorem burnsideF411_row_iff {M : Matrix (Fin 3) (Fin 3) K} {i : Fin 3} :
    (∀ j, M i j = (1 : Matrix (Fin 3) (Fin 3) K) i j) ↔ ∀ v : Fin 3 → K, (M *ᵥ v) i = v i := by
  constructor
  · intro h v
    simp only [Matrix.mulVec, dotProduct, h, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
  · intro h j
    have := h (Pi.single j 1)
    rw [Matrix.mulVec_single_one] at this
    rw [Matrix.one_apply]
    simpa [Pi.single_apply, eq_comm] using this

theorem burnsideF411_col_iff {M : Matrix (Fin 3) (Fin 3) K} {j : Fin 3} :
    (∀ i, M i j = (1 : Matrix (Fin 3) (Fin 3) K) i j) ↔
      M *ᵥ (Pi.single j 1 : Fin 3 → K) = Pi.single j 1 := by
  rw [Matrix.mulVec_single_one]
  constructor
  · intro h
    funext i
    rw [Matrix.col_apply, h i, Matrix.one_apply, Pi.single_apply]
  · intro h i
    have := congrFun h i
    rw [Matrix.col_apply] at this
    rw [this, Matrix.one_apply, Pi.single_apply]

end RowCol

section Radicals

variable {K : Type} [Field K]

theorem burnsideF411_rows_mul {g h : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ i j : Fin 3, i ≠ 0 →
      (g : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j)
    (hh : ∀ i j : Fin 3, i ≠ 0 →
      (h : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j) :
    ∀ i j : Fin 3, i ≠ 0 → ((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  intro i j hi
  have hg' := burnsideF411_row_iff.mp (fun j => hg i j hi)
  have hh' := burnsideF411_row_iff.mp (fun j => hh i j hi)
  refine burnsideF411_row_iff.mpr (fun v => ?_) j
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hg', hh']

theorem burnsideF411_rows_inv {g : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ i j : Fin 3, i ≠ 0 →
      (g : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j) :
    ∀ i j : Fin 3, i ≠ 0 → ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  intro i j hi
  have hg' := burnsideF411_row_iff.mp (fun j => hg i j hi)
  refine burnsideF411_row_iff.mpr (fun v => ?_) j
  have h1 := hg' (((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec] at h1
  exact h1.symm

theorem burnsideF411_cols_mul {g h : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ i j : Fin 3, j ≠ 2 →
      (g : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j)
    (hh : ∀ i j : Fin 3, j ≠ 2 →
      (h : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j) :
    ∀ i j : Fin 3, j ≠ 2 → ((g * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  intro i j hj
  have hg' := burnsideF411_col_iff.mp (fun i => hg i j hj)
  have hh' := burnsideF411_col_iff.mp (fun i => hh i j hj)
  refine burnsideF411_col_iff.mpr ?_ i
  rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hh', hg']

theorem burnsideF411_cols_inv {g : SpecialLinearGroup (Fin 3) K}
    (hg : ∀ i j : Fin 3, j ≠ 2 →
      (g : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j) :
    ∀ i j : Fin 3, j ≠ 2 → ((g⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j =
      (1 : Matrix (Fin 3) (Fin 3) K) i j := by
  intro i j hj
  have hg' := burnsideF411_col_iff.mp (fun i => hg i j hj)
  refine burnsideF411_col_iff.mpr ?_ i
  conv_lhs => rw [← hg']
  rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

variable (K)

@[expose] def burnsideF411_l3R1 : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∀ i j : Fin 3, i ≠ 0 →
    (g : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j}
  one_mem' := fun i j _ => by simp
  mul_mem' := fun hg hh => burnsideF411_rows_mul hg hh
  inv_mem' := fun hg => burnsideF411_rows_inv hg

@[expose] def burnsideF411_l3R2 : Subgroup (SpecialLinearGroup (Fin 3) K) where
  carrier := {g | ∀ i j : Fin 3, j ≠ 2 →
    (g : Matrix (Fin 3) (Fin 3) K) i j = (1 : Matrix (Fin 3) (Fin 3) K) i j}
  one_mem' := fun i j _ => by simp
  mul_mem' := fun hg hh => burnsideF411_cols_mul hg hh
  inv_mem' := fun hg => burnsideF411_cols_inv hg

variable {K}

theorem burnsideF411_mem_l3R1 {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ burnsideF411_l3R1 K ↔ ∀ v : Fin 3 → K, ∀ i : Fin 3, i ≠ 0 →
      ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v) i = v i := by
  constructor
  · intro hg v i hi
    exact burnsideF411_row_iff.mp (hg i · hi) v
  · intro h i j hi
    exact burnsideF411_row_iff.mpr (fun v => h v i hi) j

theorem burnsideF411_mem_l3R2 {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ burnsideF411_l3R2 K ↔ ∀ j : Fin 3, j ≠ 2 →
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single j 1 : Fin 3 → K) = Pi.single j 1 := by
  constructor
  · intro hg j hj
    exact burnsideF411_col_iff.mp (hg · j hj)
  · intro h i j hj
    exact burnsideF411_col_iff.mpr (h j hj) i

theorem burnsideF411_mem_flag1 {w : Fin 3 → K} : w ∈ flagSpace 3 K 1 ↔ w 1 = 0 ∧ w 2 = 0 := by
  rw [mem_flagSpace]
  constructor
  · intro h
    exact ⟨h 1 le_rfl, h 2 (by decide)⟩
  · rintro ⟨h1, h2⟩ j hj
    fin_cases j
    · simp at hj
    · exact h1
    · exact h2

theorem burnsideF411_mem_flag2 {w : Fin 3 → K} : w ∈ flagSpace 3 K 2 ↔ w 2 = 0 := by
  rw [mem_flagSpace]
  constructor
  · intro h
    exact h 2 le_rfl
  · intro h2 j hj
    fin_cases j
    · simp at hj
    · simp at hj
    · exact h2

theorem burnsideF411_mem_l3R1_iff {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ burnsideF411_l3R1 K ↔ ∀ v : Fin 3 → K,
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v ∈ flagSpace 3 K 1 := by
  rw [burnsideF411_mem_l3R1]
  constructor
  · intro h v
    rw [burnsideF411_mem_flag1, Pi.sub_apply, Pi.sub_apply, h v 1 (by decide), h v 2 (by decide),
      sub_self, sub_self]
    exact ⟨rfl, rfl⟩
  · intro h v i hi
    have h' := burnsideF411_mem_flag1.mp (h v)
    rw [Pi.sub_apply, Pi.sub_apply, sub_eq_zero, sub_eq_zero] at h'
    fin_cases i
    · exact absurd rfl hi
    · exact h'.1
    · exact h'.2

theorem burnsideF411_mem_l3R2_iff {g : SpecialLinearGroup (Fin 3) K} :
    g ∈ burnsideF411_l3R2 K ↔ ∀ v ∈ flagSpace 3 K 2,
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
  rw [burnsideF411_mem_l3R2]
  constructor
  · intro h v hv
    have hv2 := burnsideF411_mem_flag2.mp hv
    have hdec : v = v 0 • (Pi.single 0 1 : Fin 3 → K) + v 1 • (Pi.single 1 1 : Fin 3 → K) := by
      funext i
      fin_cases i <;> simp [hv2]
    rw [hdec, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, h 0 (by decide),
      h 1 (by decide)]
  · intro h j hj
    refine h _ (burnsideF411_mem_flag2.mpr ?_)
    fin_cases j
    · simp
    · simp
    · exact absurd rfl hj

theorem burnsideF411_l3R1_apply_zero {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ burnsideF411_l3R1 K) : (g : Matrix (Fin 3) (Fin 3) K) 0 0 = 1 := by
  have hdet := g.2
  rw [Matrix.det_fin_three] at hdet
  have e := fun j => hg 1 j (by decide)
  have f := fun j => hg 2 j (by decide)
  simp only [Matrix.one_apply] at e f
  rw [e 0, e 1, e 2, f 0, f 1, f 2] at hdet
  simpa using hdet

theorem burnsideF411_l3R2_apply_two {g : SpecialLinearGroup (Fin 3) K}
    (hg : g ∈ burnsideF411_l3R2 K) : (g : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
  have hdet := g.2
  rw [Matrix.det_fin_three] at hdet
  have e := fun i => hg i 0 (by decide)
  have f := fun i => hg i 1 (by decide)
  simp only [Matrix.one_apply] at e f
  rw [e 0, e 1, e 2, f 0, f 1, f 2] at hdet
  simpa using hdet

theorem burnsideF411_pow_of_sq_zero {N : Matrix (Fin 3) (Fin 3) K} (hN : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + (n : K) • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, Matrix.smul_mul, hN, smul_zero,
      add_zero, Nat.cast_succ, add_smul, one_smul]
    abel

theorem burnsideF411_pow_char_of_sq_zero (p : ℕ) [CharP K p] {g : SpecialLinearGroup (Fin 3) K}
    (hN : ((g : Matrix (Fin 3) (Fin 3) K) - 1) * ((g : Matrix (Fin 3) (Fin 3) K) - 1) = 0) :
    g ^ p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, Matrix.SpecialLinearGroup.coe_one]
  have h := burnsideF411_pow_of_sq_zero hN p
  rw [add_sub_cancel, CharP.cast_eq_zero, zero_smul, add_zero] at h
  exact h

variable [Finite K]

theorem burnsideF411_l3R1_isPGroup (p : ℕ) [CharP K p] : IsPGroup p (burnsideF411_l3R1 K) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  refine burnsideF411_pow_char_of_sq_zero p ?_
  ext i j
  have hg := g.2
  have h0 := burnsideF411_l3R1_apply_zero hg
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  have hrow : ∀ i' j', i' ≠ 0 → (((g : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) - 1) i' j' = 0 :=
    fun i' j' hi' => by rw [Matrix.sub_apply, hg i' j' hi', sub_self]
  have h00 : (((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) 0 0 = 0 := by
    rw [Matrix.sub_apply, h0, Matrix.one_apply_eq, sub_self]
  rw [hrow 1 j (by decide), hrow 2 j (by decide), mul_zero, mul_zero, add_zero, add_zero,
    Matrix.zero_apply]
  fin_cases i
  · simp [h00]
  · simp [hrow 1 0 (by decide)]
  · simp [hrow 2 0 (by decide)]

theorem burnsideF411_l3R2_isPGroup (p : ℕ) [CharP K p] : IsPGroup p (burnsideF411_l3R2 K) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
  refine burnsideF411_pow_char_of_sq_zero p ?_
  ext i j
  have hg := g.2
  have h2 := burnsideF411_l3R2_apply_two hg
  rw [Matrix.mul_apply, Fin.sum_univ_three]
  have hcol : ∀ i' j', j' ≠ 2 → (((g : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) - 1) i' j' = 0 :=
    fun i' j' hj' => by rw [Matrix.sub_apply, hg i' j' hj', sub_self]
  have h22 : (((g : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) - 1) 2 2 = 0 := by
    rw [Matrix.sub_apply, h2, Matrix.one_apply_eq, sub_self]
  rw [hcol i 0 (by decide), hcol i 1 (by decide), zero_mul, zero_mul, zero_add, zero_add,
    Matrix.zero_apply]
  fin_cases j
  · simp [hcol 2 0 (by decide)]
  · simp [hcol 2 1 (by decide)]
  · simp [h22]

end Radicals

section PCore

variable {K : Type} [Field K]

theorem burnsideF411_l3_stab_mulVec {W : Submodule K (Fin 3 → K)} {s : SpecialLinearGroup (Fin 3) K}
    (hs : s ∈ stabilizer W) {w : Fin 3 → K} (hw : w ∈ W) :
    (s : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W := by
  have : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ w ∈ W.map (mulVecLin (s : Matrix (Fin 3) (Fin 3) K)) :=
    ⟨w, hw, rfl⟩
  rwa [mem_stabilizer.mp hs] at this

theorem burnsideF411_l3R1_le_stab : burnsideF411_l3R1 K ≤ stabilizer (flagSpace 3 K 1) := by
  intro g hg
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  have h := burnsideF411_mem_l3R1_iff.mp hg v
  have e : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v) + v := by
    abel
  rw [mulVecLin_apply, e]
  exact add_mem h hv

theorem burnsideF411_l3R2_le_stab : burnsideF411_l3R2 K ≤ stabilizer (flagSpace 3 K 2) := by
  intro g hg
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  rw [mulVecLin_apply, burnsideF411_mem_l3R2_iff.mp hg v hv]
  exact hv

theorem burnsideF411_l3R1_conj {s g : SpecialLinearGroup (Fin 3) K}
    (hs : s ∈ stabilizer (flagSpace 3 K 1)) (hg : g ∈ burnsideF411_l3R1 K) :
    s * g * s⁻¹ ∈ burnsideF411_l3R1 K := by
  rw [burnsideF411_mem_l3R1_iff] at hg ⊢
  intro v
  have hss : (s : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) = v := by
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  have hsgs : ((s * g * s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      (s : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e : ((s * g * s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v - v =
      (s : Matrix (Fin 3) (Fin 3) K) *ᵥ ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ
        (((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) -
          ((s⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v) := by
    rw [Matrix.mulVec_sub, hss, hsgs]
  rw [e]
  exact burnsideF411_l3_stab_mulVec hs (hg _)

theorem burnsideF411_l3R2_conj {s g : SpecialLinearGroup (Fin 3) K}
    (hs : s ∈ stabilizer (flagSpace 3 K 2)) (hg : g ∈ burnsideF411_l3R2 K) :
    s * g * s⁻¹ ∈ burnsideF411_l3R2 K := by
  rw [burnsideF411_mem_l3R2_iff] at hg ⊢
  intro v hv
  have hsv := burnsideF411_l3_stab_mulVec (inv_mem hs) hv
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, hg _ hsv, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem burnsideF411_l3_projStab_le_normalizer {W : Submodule K (Fin 3 → K)}
    {R : Subgroup (SpecialLinearGroup (Fin 3) K)}
    (hconj : ∀ s g, s ∈ stabilizer W → g ∈ R → s * g * s⁻¹ ∈ R) :
    projStabilizer W ≤ Subgroup.normalizer ((R.map (proj 3 K) : Subgroup (projectiveSL 3 K)) :
      Set (projectiveSL 3 K)) := by
  rintro _ ⟨s, hs, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨s * g * s⁻¹, hconj s g hs hg, by rw [map_mul, map_mul, map_inv]⟩
  · rintro ⟨g, hg, hgx⟩
    refine ⟨s⁻¹ * g * s, ?_, ?_⟩
    · have := hconj s⁻¹ g (inv_mem hs) hg
      simpa using this
    · rw [map_mul, map_mul, map_inv, hgx]
      group

variable [Finite K]

theorem burnsideF411_l3_pCoreOf_le_projU (p : ℕ) [Fact p.Prime] [CharP K p]
    {L : Subgroup (projectiveSL 3 K)} (hUL : projUnitriangular 3 K ≤ L) :
    pCoreOf p L ≤ projUnitriangular 3 K := by
  obtain ⟨SU, hSU⟩ := exists_sylow_projUnitriangular (K := K) p (n := 3) (by norm_num)
  have hSB : (SU : Subgroup (projectiveSL 3 K)) ≤ L := hSU ▸ hUL
  haveI := CFSG.LieType.BorelTits.pCore_normal p (G := ↥L)
  have hle := (CFSG.LieType.BorelTits.pCore_isPGroup p (G := ↥L)).le_sylow_of_normal
    (SU.subtype hSB)
  rintro _ ⟨x, hx, rfl⟩
  have hx' := hle hx
  rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf, hSU] at hx'
  exact hx'

theorem burnsideF411_l3_projU_le (d : ℕ) :
    projUnitriangular 3 K ≤ projStabilizer (flagSpace 3 K d) :=
  Subgroup.map_mono ((unitriangular_le_upperTriangular 3 K).trans
    (upperTriangular_le_stabilizer_flagSpace d))

theorem burnsideF411_l3_conj_scalar {u u' w : SpecialLinearGroup (Fin 3) K}
    (h : proj 3 K u' = proj 3 K (w⁻¹ * u * w)) :
    ∃ c : Kˣ, ∀ v : Fin 3 → K, (w : Matrix (Fin 3) (Fin 3) K) *ᵥ ((u' : Matrix (Fin 3) (Fin 3) K) *ᵥ v) =
      (c : K) • ((u : Matrix (Fin 3) (Fin 3) K) *ᵥ ((w : Matrix (Fin 3) (Fin 3) K) *ᵥ v)) := by
  have h' := (QuotientGroup.eq (s := scalars 3 K)).mp h.symm
  obtain ⟨c, -, hc⟩ := mem_scalars.mp h'
  refine ⟨c, fun v => ?_⟩
  have e1 : u' = w⁻¹ * u * w * ((w⁻¹ * u * w)⁻¹ * u') := by group
  have hs : ∀ x : Fin 3 → K, Matrix.scalar (Fin 3) (c : K) *ᵥ x = (c : K) • x := by
    intro x
    funext i
    rw [Matrix.scalar_apply, Matrix.mulVec_diagonal]
    rfl
  have hww : ∀ x : Fin 3 → K, (w : Matrix (Fin 3) (Fin 3) K) *ᵥ
      (((w⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
  conv_lhs => rw [e1]
  rw [Matrix.SpecialLinearGroup.coe_mul, hc, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_smul,
    Matrix.mulVec_smul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hww]

@[expose] def burnsideF411_l3w1 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 0, 1; 0, -1, 0], by simp [Matrix.det_fin_three]⟩

@[expose] def burnsideF411_l3w2 : SpecialLinearGroup (Fin 3) K :=
  ⟨!![0, 1, 0; -1, 0, 0; 0, 0, 1], by simp [Matrix.det_fin_three]⟩

theorem burnsideF411_l3w1_mem : burnsideF411_l3w1 (K := K) ∈ stabilizer (flagSpace 3 K 1) := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨h1, h2⟩ := burnsideF411_mem_flag1.mp hv
  rw [burnsideF411_mem_flag1]
  simp [burnsideF411_l3w1, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h1, h2]

theorem burnsideF411_l3w2_mem : burnsideF411_l3w2 (K := K) ∈ stabilizer (flagSpace 3 K 2) := by
  refine mem_stabilizer_of_map_le ?_
  rintro _ ⟨v, hv, rfl⟩
  have h2 := burnsideF411_mem_flag2.mp hv
  rw [burnsideF411_mem_flag2]
  simp [burnsideF411_l3w2, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h2]

theorem burnsideF411_l3_pCoreOf_point (p : ℕ) [Fact p.Prime] [CharP K p] :
    pCoreOf p (projStabilizer (flagSpace 3 K 1)) = (burnsideF411_l3R1 K).map (proj 3 K) := by
  apply le_antisymm
  · have hOU := burnsideF411_l3_pCoreOf_le_projU (K := K) p (burnsideF411_l3_projU_le 1)
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf p (projStabilizer (flagSpace 3 K 1))
    intro x hx
    have hw : proj 3 K burnsideF411_l3w1 ∈ projStabilizer (flagSpace 3 K 1) :=
      ⟨_, burnsideF411_l3w1_mem, rfl⟩
    have hwx : (proj 3 K burnsideF411_l3w1)⁻¹ * x * ((proj 3 K burnsideF411_l3w1)⁻¹)⁻¹ ∈
        pCoreOf p (projStabilizer (flagSpace 3 K 1)) :=
      (Subgroup.mem_normalizer_iff.mp (hN (inv_mem hw)) x).mp hx
    obtain ⟨u, hu, rfl⟩ := hOU hx
    obtain ⟨u', hu', hu'e⟩ := hOU hwx
    rw [inv_inv, ← map_inv, ← map_mul, ← map_mul] at hu'e
    obtain ⟨c, hc⟩ := burnsideF411_l3_conj_scalar hu'e
    have e := congrFun (hc (Pi.single 1 1)) 1
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨hu'1, hu'2⟩ := hu'
    have h21 : (u' : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := hu'1 2 1 (by decide)
    simp [burnsideF411_l3w1, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h21] at e
    have h12 : (u : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 := by
      first
        | exact e.symm
        | exact e
        | exact (mul_eq_zero.mp e.symm).resolve_left c.ne_zero
        | exact (mul_eq_zero.mp e).resolve_left c.ne_zero
    refine ⟨u, fun i j hi => ?_, rfl⟩
    fin_cases i
    · exact absurd rfl hi
    · fin_cases j
      · simpa using hu1 1 0 (by decide)
      · simpa using hu2 1
      · simpa using h12
    · fin_cases j
      · simpa using hu1 2 0 (by decide)
      · simpa using hu1 2 1 (by decide)
      · simpa using hu2 2
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
      (Subgroup.map_mono burnsideF411_l3R1_le_stab) ?_ ((burnsideF411_l3R1_isPGroup p).map _)
    exact burnsideF411_l3_projStab_le_normalizer fun s g hs hg => burnsideF411_l3R1_conj hs hg

theorem burnsideF411_l3_pCoreOf_line (p : ℕ) [Fact p.Prime] [CharP K p] :
    pCoreOf p (projStabilizer (flagSpace 3 K 2)) = (burnsideF411_l3R2 K).map (proj 3 K) := by
  apply le_antisymm
  · have hOU := burnsideF411_l3_pCoreOf_le_projU (K := K) p (burnsideF411_l3_projU_le 2)
    have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf p (projStabilizer (flagSpace 3 K 2))
    intro x hx
    have hw : proj 3 K burnsideF411_l3w2 ∈ projStabilizer (flagSpace 3 K 2) :=
      ⟨_, burnsideF411_l3w2_mem, rfl⟩
    have hwx : (proj 3 K burnsideF411_l3w2)⁻¹ * x * ((proj 3 K burnsideF411_l3w2)⁻¹)⁻¹ ∈
        pCoreOf p (projStabilizer (flagSpace 3 K 2)) :=
      (Subgroup.mem_normalizer_iff.mp (hN (inv_mem hw)) x).mp hx
    obtain ⟨u, hu, rfl⟩ := hOU hx
    obtain ⟨u', hu', hu'e⟩ := hOU hwx
    rw [inv_inv, ← map_inv, ← map_mul, ← map_mul] at hu'e
    obtain ⟨c, hc⟩ := burnsideF411_l3_conj_scalar hu'e
    have e := congrFun (hc (Pi.single 0 1)) 0
    obtain ⟨hu1, hu2⟩ := hu
    obtain ⟨hu'1, hu'2⟩ := hu'
    have h10 : (u' : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 := hu'1 1 0 (by decide)
    simp [burnsideF411_l3w2, Matrix.mulVec, dotProduct, Fin.sum_univ_three, h10] at e
    have h01 : (u : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 := by
      first
        | exact e.symm
        | exact e
        | exact (mul_eq_zero.mp e.symm).resolve_left c.ne_zero
        | exact (mul_eq_zero.mp e).resolve_left c.ne_zero
    refine ⟨u, fun i j hj => ?_, rfl⟩
    fin_cases j
    · fin_cases i
      · simpa using hu2 0
      · simpa using hu1 1 0 (by decide)
      · simpa using hu1 2 0 (by decide)
    · fin_cases i
      · simpa using h01
      · simpa using hu2 1
      · simpa using hu1 2 1 (by decide)
    · exact absurd rfl hj
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p
      (Subgroup.map_mono burnsideF411_l3R2_le_stab) ?_ ((burnsideF411_l3R2_isPGroup p).map _)
    exact burnsideF411_l3_projStab_le_normalizer fun s g hs hg => burnsideF411_l3R2_conj hs hg

end PCore

end CFSG.ASVolI
