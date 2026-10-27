module

public import CFSG.Monster.Griess.TrialityMatrix.Blocks

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess

open CFSG.Monster CFSG.Monster.Spin Matrix Module

noncomputable instance instDecidableEqOddOctIdx : DecidableEq ((C₀ × Fin 24 × Fin 3) ⊕ OctIdx) :=
  @instDecidableEqSum _ _ inferInstance inferInstance

noncomputable instance instDecidableEqPairOddOctIdx :
    DecidableEq ((LtPair × Fin 3) ⊕ (C₀ × Fin 24 × Fin 3) ⊕ OctIdx) :=
  @instDecidableEqSum _ _ inferInstance inferInstance

@[expose] noncomputable def pairBlock : Matrix (LtPair × Fin 3) (LtPair × Fin 3) ℚ :=
  kron1 LtPair cyc3

@[expose] noncomputable def oddBlock : Matrix (C₀ × Fin 24 × Fin 3) (C₀ × Fin 24 × Fin 3) ℚ :=
  kron1 C₀ (kron1 (Fin 24) cyc3)

@[expose] noncomputable def octBlock : Matrix OctIdx OctIdx ℚ := blockDiagonal' octHD

@[expose] noncomputable def tauMat : Matrix TIdx TIdx ℚ :=
  diag2 1 (diag2 pairBlock (diag2 oddBlock octBlock))

theorem pairBlock_mul_transpose : pairBlock * pairBlockᵀ = 1 := by
  rw [pairBlock, kron1_transpose, kron1_mul, cyc3_mul_transpose, kron1_one]

theorem pairBlock_transpose_mul : pairBlockᵀ * pairBlock = 1 := by
  rw [pairBlock, kron1_transpose, kron1_mul, cyc3_transpose_mul, kron1_one]

theorem oddBlock_mul_transpose : oddBlock * oddBlockᵀ = 1 := by
  rw [oddBlock, kron1_transpose, kron1_transpose, kron1_mul, kron1_mul, cyc3_mul_transpose,
    kron1_one, kron1_one]

theorem oddBlock_transpose_mul : oddBlockᵀ * oddBlock = 1 := by
  rw [oddBlock, kron1_transpose, kron1_transpose, kron1_mul, kron1_mul, cyc3_transpose_mul,
    kron1_one, kron1_one]

theorem octBlock_mul_transpose : octBlock * octBlockᵀ = 1 := by
  rw [octBlock, blockDiagonal'_transpose, ← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext d
  exact octHD_mul_transpose d

theorem octBlock_transpose_mul : octBlockᵀ * octBlock = 1 := by
  rw [octBlock, blockDiagonal'_transpose, ← blockDiagonal'_mul, ← blockDiagonal'_one]
  congr 1
  funext d
  exact octHD_transpose_mul d

theorem pairBlock_pow_three : pairBlock ^ 3 = 1 := by
  rw [pairBlock, kron1_pow, cyc3_pow_three, kron1_one]

theorem oddBlock_pow_three : oddBlock ^ 3 = 1 := by
  rw [oddBlock, kron1_pow, kron1_pow, cyc3_pow_three, kron1_one, kron1_one]

theorem octBlock_pow_three : octBlock ^ 3 = 1 := by
  rw [octBlock, ← blockDiagonal'_pow, ← blockDiagonal'_one]
  congr 1
  funext d
  exact octHD_pow_three d

theorem trace_pairBlock : trace pairBlock = 0 := by
  rw [pairBlock, trace_kron1, trace_cyc3, mul_zero]

theorem trace_oddBlock : trace oddBlock = 0 := by
  rw [oddBlock, trace_kron1, trace_kron1, trace_cyc3, mul_zero, mul_zero]

theorem trace_octBlock : trace octBlock = 759 := by
  rw [octBlock, trace_blockDiagonal']
  simp only [trace_octHD, Finset.sum_const, Finset.card_univ, card_octadWord, nsmul_eq_mul,
    mul_one]
  norm_num

theorem tauMat_mul_transpose : tauMat * tauMatᵀ = 1 := by
  rw [tauMat, diag2_transpose, diag2_transpose, diag2_transpose, diag2_mul, diag2_mul, diag2_mul,
    transpose_one, Matrix.mul_one, pairBlock_mul_transpose, oddBlock_mul_transpose,
    octBlock_mul_transpose, diag2_one, diag2_one, diag2_one]

theorem tauMat_transpose_mul : tauMatᵀ * tauMat = 1 := by
  rw [tauMat, diag2_transpose, diag2_transpose, diag2_transpose, diag2_mul, diag2_mul, diag2_mul,
    transpose_one, Matrix.mul_one, pairBlock_transpose_mul, oddBlock_transpose_mul,
    octBlock_transpose_mul, diag2_one, diag2_one, diag2_one]

theorem tauMat_pow_three : tauMat ^ 3 = 1 := by
  rw [tauMat, diag2_pow, diag2_pow, diag2_pow, one_pow, pairBlock_pow_three, oddBlock_pow_three,
    octBlock_pow_three, diag2_one, diag2_one, diag2_one]

theorem trace_tauMat : trace tauMat = 783 := by
  rw [tauMat, trace_diag2, trace_diag2, trace_diag2, trace_one, trace_pairBlock, trace_oddBlock,
    trace_octBlock, Fintype.card_fin]
  norm_num

theorem trace_tauMat_sq : trace (tauMat ^ 2) = 783 := by
  rw [sq_eq_transpose_of_pow_three tauMat_pow_three tauMat_mul_transpose, trace_transpose,
    trace_tauMat]

theorem tauMat_mem_dyadic : ∀ x y, tauMat x y ∈ dyadic :=
  diag2_mem_dyadic one_apply_mem_dyadic (diag2_mem_dyadic (kron1_mem_dyadic _ cyc3_mem_dyadic)
    (diag2_mem_dyadic (kron1_mem_dyadic _ (kron1_mem_dyadic _ cyc3_mem_dyadic))
      fun ⟨d, u⟩ ⟨d', v⟩ => by
        rw [octBlock, blockDiagonal'_apply]
        split_ifs with h
        · exact octHD_mem_dyadic _ _ _
        · exact dyadic.zero_mem))

theorem diagonal_tnorm : diagonal tnorm = diag2 1 (diag2 ((2 : ℚ) • 1) (diag2 1 1)) := by
  ext x y
  rcases x with i | q | q | o <;> rcases y with j | q' | q' | o' <;>
    simp [diag2, diagonal_apply, tnorm, one_apply]

theorem tauMat_mul_diagonal_tnorm : tauMat * diagonal tnorm * tauMatᵀ = diagonal tnorm := by
  rw [diagonal_tnorm, tauMat, diag2_transpose, diag2_transpose, diag2_transpose, diag2_mul,
    diag2_mul, diag2_mul, diag2_mul, diag2_mul, diag2_mul, Matrix.mul_one, Matrix.mul_one,
    Matrix.mul_one, transpose_one, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul, pairBlock_mul_transpose, oddBlock_mul_transpose, octBlock_mul_transpose]

theorem tauMat_diag_apply (i : Fin 24) (y : TIdx) :
    tauMat (.inl i) y = if y = .inl i then 1 else 0 := by
  rcases y with j | q | q | o
  · simp [tauMat, diag2_apply_inl_inl, one_apply, eq_comm]
  · simp [tauMat, diag2_apply_inl_inr]
  · simp [tauMat, diag2_apply_inl_inr]
  · simp [tauMat, diag2_apply_inl_inr]

theorem tauMat_pair_apply (p : LtPair) (k : Fin 3) (y : TIdx) :
    tauMat (.inr (.inl (p, k))) y = if y = .inr (.inl (p, k + 1)) then 1 else 0 := by
  rcases y with j | ⟨p', k'⟩ | q | o
  · simp [tauMat, diag2_apply_inr_inl]
  · simp only [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inl, pairBlock, kron1_apply, one_apply,
      cyc3_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
    by_cases hp : p = p' <;> by_cases hk : k' = k + 1 <;> simp [hp, hk, eq_comm]
  · simp [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inr]
  · simp [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inr]

theorem tauMat_odd_apply (c : C₀) (i : Fin 24) (k : Fin 3) (y : TIdx) :
    tauMat (.inr (.inr (.inl (c, i, k)))) y =
      if y = .inr (.inr (.inl (c, i, k + 1))) then 1 else 0 := by
  rcases y with j | q | ⟨c', i', k'⟩ | o
  · simp [tauMat, diag2_apply_inr_inl]
  · simp [tauMat, diag2_apply_inr_inr, diag2_apply_inr_inl]
  · simp only [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inl, oddBlock, kron1_apply, one_apply,
      cyc3_apply, Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq]
    by_cases hc : c = c' <;> by_cases hi : i = i' <;> by_cases hk : k' = k + 1 <;>
      simp [hc, hi, hk, eq_comm]
  · simp [tauMat, diag2_apply_inr_inr, diag2_apply_inl_inr]

theorem tauMat_oct_apply_oct (d : OctadWord) (v w : Octad.EvenQuot (octSupp d)) :
    tauMat (.inr (.inr (.inr ⟨d, v⟩))) (.inr (.inr (.inr ⟨d, w⟩))) = octHD d v w := by
  simp only [tauMat, diag2_apply_inr_inr, octBlock, blockDiagonal'_apply_eq]

theorem tauMat_oct_apply_of_notMem (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) (y : TIdx)
    (hy : y ∉ Set.range fun w : Octad.EvenQuot (octSupp d) => (.inr (.inr (.inr ⟨d, w⟩)) : TIdx)) :
    tauMat (.inr (.inr (.inr ⟨d, v⟩))) y = 0 := by
  rcases y with j | q | q | ⟨d', w⟩
  · rfl
  · rfl
  · rfl
  · have hd : d ≠ d' := by
      rintro rfl
      exact hy ⟨w, rfl⟩
    simp only [tauMat, diag2_apply_inr_inr, octBlock]
    exact blockDiagonal'_apply_ne _ _ _ hd

@[expose] noncomputable def tauB : SpaceB ≃ₗ[ℚ] SpaceB :=
  Matrix.toLinOfInv tbasis tbasis tauMat_transpose_mul tauMat_mul_transpose

theorem coe_tauB : (tauB : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis tauMatᵀ := rfl

theorem coe_tauB_symm : (tauB.symm : SpaceB →ₗ[ℚ] SpaceB) = toLin tbasis tbasis tauMat := rfl

theorem tauB_apply (u : SpaceB) : tauB u = toLin tbasis tbasis tauMatᵀ u := rfl

theorem tauB_symm_apply (u : SpaceB) : tauB.symm u = toLin tbasis tbasis tauMat u := rfl

theorem tauB_tbasis (x : TIdx) : tauB (tbasis x) = ∑ y, tauMat x y • tbasis y := by
  rw [tauB_apply, toLin_self]
  rfl

theorem tauB_diag (i : Fin 24) : tauB (tbasis (.inl i)) = tbasis (.inl i) := by
  rw [tauB_tbasis]
  simp only [tauMat_diag_apply, sum_ite_smul_tbasis]

theorem tauB_pair (p : LtPair) (k : Fin 3) :
    tauB (tbasis (.inr (.inl (p, k)))) = tbasis (.inr (.inl (p, k + 1))) := by
  rw [tauB_tbasis]
  simp only [tauMat_pair_apply, sum_ite_smul_tbasis]

theorem tauB_odd (c : C₀) (i : Fin 24) (k : Fin 3) :
    tauB (tbasis (.inr (.inr (.inl (c, i, k))))) = tbasis (.inr (.inr (.inl (c, i, k + 1)))) := by
  rw [tauB_tbasis]
  simp only [tauMat_odd_apply, sum_ite_smul_tbasis]

theorem tauB_oct (d : OctadWord) (v : Octad.EvenQuot (octSupp d)) :
    tauB (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
      ∑ w, octHD d v w • tbasis (.inr (.inr (.inr ⟨d, w⟩))) := by
  rw [tauB_tbasis]
  refine (Fintype.sum_of_injective (fun w : Octad.EvenQuot (octSupp d) =>
    (.inr (.inr (.inr ⟨d, w⟩)) : TIdx)) ?_ _ _ ?_ ?_).symm
  · intro w w' h
    simpa using h
  · intro y hy
    rw [tauMat_oct_apply_of_notMem d v y hy, zero_smul]
  · intro w
    rw [tauMat_oct_apply_oct]

theorem tauB_Xlift_rOct {d : OctadWord} {δ : Finset (Fin 24)} (hδ : δ ⊆ octSupp d)
    (he : Even δ.card) :
    tauB ((0 : symMat), Xlift (rOct d δ), (0 : SpaceW)) =
      ∑ v : Octad.EvenQuot (octSupp d),
        ((8 : ℚ)⁻¹ * (-1) ^ ((δ ∩ octRep d v).card + (octRep d v).card / 2)) •
          ((0 : symMat), Xlift (rOct d (octRep d v)), (0 : SpaceW)) := by
  rw [← tbasis_oct_cls hδ he, tauB_oct]
  refine Finset.sum_congr rfl fun v _ => ?_
  obtain ⟨h1, h2, h3⟩ := octRep_spec d v
  rw [tbasis_oct]
  refine congrArg₂ (· • ·) ?_ rfl
  calc octHD d (Octad.cls (octSupp d) δ) v =
        octHD d (Octad.cls (octSupp d) δ) (Octad.cls (octSupp d) (octRep d v)) := by rw [h3]
    _ = _ := octHD_cls d hδ he h1 h2

theorem bform_tauB (u v : SpaceB) : bform (tauB u) (tauB v) = bform u v :=
  bform_toLin_of_gram tbasis bform_tbasis tauMat_mul_diagonal_tnorm u v

theorem bform_tauB_symm (u v : SpaceB) : bform (tauB.symm u) (tauB.symm v) = bform u v := by
  rw [← bform_tauB, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

theorem tauB_mem_BR {u : SpaceB} (hu : u ∈ BR) : tauB u ∈ BR := by
  rw [tauB_apply]
  exact toLin_mem_BR (fun x y => tauMat_mem_dyadic y x) hu

theorem tauB_symm_mem_BR {u : SpaceB} (hu : u ∈ BR) : tauB.symm u ∈ BR := by
  rw [tauB_symm_apply]
  exact toLin_mem_BR tauMat_mem_dyadic hu

theorem tauB_mem_BR_iff {u : SpaceB} : tauB u ∈ BR ↔ u ∈ BR :=
  ⟨fun h => by simpa using tauB_symm_mem_BR h, tauB_mem_BR⟩

theorem tauB_symm_mem_BR_iff {u : SpaceB} : tauB.symm u ∈ BR ↔ u ∈ BR :=
  ⟨fun h => by simpa using tauB_mem_BR h, tauB_symm_mem_BR⟩

theorem map_tauB_BR : BR.map ((tauB : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR := by
  ext u
  refine ⟨?_, fun h => ⟨tauB.symm u, tauB_symm_mem_BR h, tauB.apply_symm_apply u⟩⟩
  rintro ⟨v, hv, rfl⟩
  exact tauB_mem_BR hv

theorem coe_pow_linearEquiv (e : SpaceB ≃ₗ[ℚ] SpaceB) (n : ℕ) :
    ((e ^ n : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB) = (e : SpaceB →ₗ[ℚ] SpaceB) ^ n :=
  map_pow LinearEquiv.automorphismGroup.toLinearMapMonoidHom e n

theorem coe_tauB_pow (n : ℕ) :
    (tauB : SpaceB →ₗ[ℚ] SpaceB) ^ n = toLin tbasis tbasis (tauMat ^ n)ᵀ := by
  rw [coe_tauB, transpose_pow, Matrix.toLin_pow]

theorem tauB_pow_three : tauB ^ 3 = 1 := by
  apply LinearEquiv.toLinearMap_injective
  rw [coe_pow_linearEquiv, coe_tauB_pow, tauMat_pow_three, transpose_one, Matrix.toLin_one]
  rfl

theorem trace_tauB : LinearMap.trace ℚ SpaceB tauB = 783 := by
  rw [LinearMap.trace_eq_matrix_trace ℚ tbasis, coe_tauB, LinearMap.toMatrix_toLin,
    trace_transpose, trace_tauMat]

theorem trace_tauB_sq : LinearMap.trace ℚ SpaceB ((tauB : SpaceB →ₗ[ℚ] SpaceB) ^ 2) = 783 := by
  rw [coe_tauB_pow, LinearMap.trace_eq_matrix_trace ℚ tbasis, LinearMap.toMatrix_toLin,
    trace_transpose, trace_tauMat_sq]

theorem tauB_ne_one : tauB ≠ 1 := by
  intro h
  have htr := trace_tauB
  rw [h, LinearEquiv.coe_toLinearMap_one, LinearMap.trace_id, finrank_B] at htr
  norm_num at htr

theorem orderOf_tauB : orderOf tauB = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime tauB_pow_three tauB_ne_one

theorem finrank_ker_tauB_sub_one :
    finrank ℚ (LinearMap.ker ((tauB : SpaceB →ₗ[ℚ] SpaceB) - 1)) = 66150 := by
  have h3 : (tauB : SpaceB →ₗ[ℚ] SpaceB) ^ 3 = 1 := by
    rw [← coe_pow_linearEquiv, tauB_pow_three]
    rfl
  have key := three_mul_finrank_ker_sub_one _ h3
  rw [trace_tauB, trace_tauB_sq, finrank_B] at key
  have h' : ((3 * finrank ℚ (LinearMap.ker ((tauB : SpaceB →ₗ[ℚ] SpaceB) - 1)) : ℕ) : ℚ) =
      ((3 * 66150 : ℕ) : ℚ) := by
    push_cast
    rw [key]
    norm_num
  have h'' := Nat.cast_injective h'
  omega

theorem rational_triality_matrix :
    (∀ i : Fin 24, tauB (tbasis (.inl i)) = tbasis (.inl i)) ∧
    (∀ (p : LtPair) (k : Fin 3),
      tauB (tbasis (.inr (.inl (p, k)))) = tbasis (.inr (.inl (p, k + 1)))) ∧
    (∀ (c : C₀) (i : Fin 24) (k : Fin 3),
      tauB (tbasis (.inr (.inr (.inl (c, i, k))))) = tbasis (.inr (.inr (.inl (c, i, k + 1))))) ∧
    (∀ (d : OctadWord) (v : Octad.EvenQuot (octSupp d)),
      tauB (tbasis (.inr (.inr (.inr ⟨d, v⟩)))) =
        ∑ w, (fourierMatrix (QuadraticMap.polarBilin (Octad.quadForm (octSupp d))) 3 *
          signMatrix (Octad.quadForm (octSupp d))) v w • tbasis (.inr (.inr (.inr ⟨d, w⟩)))) ∧
    (∀ (d : OctadWord) (δ ε : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      ε ⊆ octSupp d → Even ε.card →
      (fourierMatrix (QuadraticMap.polarBilin (Octad.quadForm (octSupp d))) 3 *
          signMatrix (Octad.quadForm (octSupp d))) (Octad.cls (octSupp d) δ)
            (Octad.cls (octSupp d) ε) =
        (8 : ℚ)⁻¹ * (-1) ^ ((δ ∩ ε).card + ε.card / 2)) ∧
    (∀ (d : OctadWord) (δ : Finset (Fin 24)), δ ⊆ octSupp d → Even δ.card →
      tauB ((0 : symMat), Xlift (rOct d δ), (0 : SpaceW)) =
        ∑ v : Octad.EvenQuot (octSupp d),
          ((8 : ℚ)⁻¹ * (-1) ^ ((δ ∩ octRep d v).card + (octRep d v).card / 2)) •
            ((0 : symMat), Xlift (rOct d (octRep d v)), (0 : SpaceW))) ∧
    (∀ u v : SpaceB, bform (tauB u) (tauB v) = bform u v) ∧
    BR.map ((tauB : SpaceB →ₗ[ℚ] SpaceB).restrictScalars dyadic) = BR ∧
    orderOf tauB = 3 ∧
    LinearMap.trace ℚ SpaceB tauB = 783 ∧
    finrank ℚ (LinearMap.ker ((tauB : SpaceB →ₗ[ℚ] SpaceB) - 1)) = 66150 :=
  ⟨tauB_diag, tauB_pair, tauB_odd, tauB_oct,
    fun d _ _ hδ hδe hε hεe => octHD_cls d hδ hδe hε hεe, fun _ _ hδ he => tauB_Xlift_rOct hδ he,
    bform_tauB, map_tauB_BR, orderOf_tauB, trace_tauB, finrank_ker_tauB_sub_one⟩

end CFSG.Monster.Griess
