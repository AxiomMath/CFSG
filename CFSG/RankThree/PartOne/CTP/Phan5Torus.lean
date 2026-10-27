module

public import CFSG.RankThree.PartOne.KF.UnitaryTorus
public import CFSG.RankThree.PartOne.KF.SU5Swap
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFSU5

section BlockMats

variable {K : Type} [Field K]

theorem blockMat_diag_zero (a b : K) :
    blockMat 5 0 (Matrix.diagonal ![a, b]) = Matrix.diagonal ![a, b, (1 : K), 1, 1] := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem blockMat_diag_one (a b : K) :
    blockMat 5 1 (Matrix.diagonal ![a, b]) = Matrix.diagonal ![(1 : K), a, b, 1, 1] := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem blockMat_diag_three (a b : K) :
    blockMat 5 3 (Matrix.diagonal ![a, b]) = Matrix.diagonal ![(1 : K), 1, 1, a, b] := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.diagonal_apply]

theorem blockMat_swap_zero :
    blockMat 5 0 (swapMatrix K (0 : Fin 2) 1) = swapMatrix K (0 : Fin 5) 1 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, swapMatrix_apply,
      Equiv.swap_apply_def, Matrix.one_apply]

theorem blockMat_swap_one :
    blockMat 5 1 (swapMatrix K (0 : Fin 2) 1) = swapMatrix K (1 : Fin 5) 2 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, swapMatrix_apply,
      Equiv.swap_apply_def, Matrix.one_apply]

theorem blockMat_swap_three :
    blockMat 5 3 (swapMatrix K (0 : Fin 2) 1) = swapMatrix K (3 : Fin 5) 4 := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, swapMatrix_apply,
      Equiv.swap_apply_def, Matrix.one_apply]

theorem diag_comm_blockMat_zero (ν μ a b c d : K) :
    Matrix.diagonal ![ν, ν, ν, μ, μ] * blockMat 5 0 !![a, b; c, d] =
      blockMat 5 0 !![a, b; c, d] * Matrix.diagonal ![ν, ν, ν, μ, μ] := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.one_apply] <;> ring

theorem diag_comm_blockMat_one (ν μ a b c d : K) :
    Matrix.diagonal ![ν, ν, ν, μ, μ] * blockMat 5 1 !![a, b; c, d] =
      blockMat 5 1 !![a, b; c, d] * Matrix.diagonal ![ν, ν, ν, μ, μ] := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.one_apply] <;> ring

theorem diag_comm_blockMat_three (ν μ a b c d : K) :
    Matrix.diagonal ![ν, ν, ν, μ, μ] * blockMat 5 3 !![a, b; c, d] =
      blockMat 5 3 !![a, b; c, d] * Matrix.diagonal ![ν, ν, ν, μ, μ] := by
  ext x y
  fin_cases x <;> fin_cases y <;>
    simp [blockMat, blockSel, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal_apply,
      Matrix.one_apply] <;> ring

theorem entry_zero_of_comm_diagonal {G : Matrix (Fin 5) (Fin 5) K} {e : Fin 5 → K}
    (h : G * Matrix.diagonal e = Matrix.diagonal e * G) {x y : Fin 5} (hxy : e y ≠ e x) :
    G x y = 0 := by
  have h1 := congrFun (congrFun h x) y
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
  have h2 : G x y * (e y - e x) = 0 := by linear_combination h1
  rcases mul_eq_zero.mp h2 with h3 | h3
  · exact h3
  · exact absurd (sub_eq_zero.mp h3) hxy

theorem diag_entry_eq_of_comm_swap {G : Matrix (Fin 5) (Fin 5) K} {a b : Fin 5}
    (h : G * swapMatrix K a b = swapMatrix K a b * G) : G a a = G b b := by
  have h1 := congrFun (congrFun h a) b
  simp only [Matrix.mul_apply, swapMatrix_apply] at h1
  have e1 : ∀ k : Fin 5,
      (if k = Equiv.swap a b b then (1 : K) else 0) = if k = a then 1 else 0 := by
    intro k
    rw [Equiv.swap_apply_right]
  have e2 : ∀ k : Fin 5,
      (if a = Equiv.swap a b k then (1 : K) else 0) = if k = b then 1 else 0 := by
    intro k
    have : a = Equiv.swap a b k ↔ k = b := by
      rw [eq_comm, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left, eq_comm]
    simp only [this]
  simp only [e1, e2, mul_ite, mul_one, mul_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true] at h1
  exact h1

end BlockMats

section Elements

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

noncomputable abbrev blk5 (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ) (i : Fin 4) :
    Subgroup (Su K 2 f 5) :=
  (blockEmb2 K 2 f 4 i).range

noncomputable def swapSU (n : ℕ) (a b : Fin n) : Su K 2 f n :=
  ⟨swapUnit K a b, by
    refine ⟨?_, ?_⟩
    · rw [swapUnit_val]
      exact det_swapMatrix a b
    · rw [swapUnit_val]
      have hm := swapMatrix_map (K := K) (unitaryInvolution K 2 f).toRingHom a b
      simp only [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at hm
      have hT : conjTr (unitaryInvolution K 2 f) (swapMatrix K a b) = swapMatrix K a b := by
        rw [conjTr, hm, swapMatrix_transpose]
      rw [hT, swapMatrix_mul_self]⟩

theorem coe_swapSU (n : ℕ) (a b : Fin n) :
    (((swapSU n a b : Su K 2 f n) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      swapMatrix K a b := by
  rw [swapSU]
  exact swapUnit_val _ _

noncomputable abbrev swapSU2 : Su K 2 f 2 := swapSU 2 0 1

theorem coe_swapSU2 :
    (((swapSU2 : Su K 2 f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      swapMatrix K (0 : Fin 2) 1 :=
  coe_swapSU 2 0 1

theorem coe_blockEmb2_mat (i : Fin 4) (A : Su K 2 f 2) :
    (((blockEmb2 K 2 f 4 i A : Su K 2 f 5) : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      blockMat 5 (i : ℕ) (((A : Su K 2 f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem comm_matrix {g u : Su K 2 f 5} (h : g * u = u * g) :
    ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * ((u : GL (Fin 5) K) : Matrix _ _ K) =
      ((u : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) * ((g : GL (Fin 5) K) : Matrix _ _ K) := by
  have := congrArg (fun x : Su K 2 f 5 => ((x : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K)) h
  simpa using this

theorem exists_normOne_ne_one (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) :
    ∃ t : Kˣ, t ∈ normOne (unitaryInvolution K 2 f) ∧ t ≠ 1 := by
  obtain ⟨ω, hω⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hcard : Nat.card Kˣ = (2 ^ f) ^ 2 - 1 := by
    classical
    have := Fintype.ofFinite K
    rw [Nat.card_eq_fintype_card, Fintype.card_units, ← Nat.card_eq_fintype_card, hK]
  have hord : orderOf ω = (2 ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hω, hcard]
  have hQ : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  refine ⟨ω ^ (2 ^ f - 1), ?_, ?_⟩
  · rw [mem_normOne, unitaryInvolution_apply]
    have h1 : (ω ^ (2 ^ f - 1) : Kˣ) ^ (2 ^ f + 1) = 1 := by
      rw [← pow_mul]
      have : (2 ^ f - 1) * (2 ^ f + 1) = (2 ^ f) ^ 2 - 1 := by
        have h2 : 1 ≤ 2 ^ f := by omega
        have h3 : 1 ≤ (2 ^ f) ^ 2 := by nlinarith
        zify [h2, h3]
        ring
      rw [this, ← hord, pow_orderOf_eq_one]
    have h2 : ((ω ^ (2 ^ f - 1) : Kˣ) : K) ^ (2 ^ f + 1) = 1 := by
      have := congrArg (fun u : Kˣ => (u : K)) h1
      simpa using this
    calc ((ω ^ (2 ^ f - 1) : Kˣ) : K) ^ 2 ^ f * ((ω ^ (2 ^ f - 1) : Kˣ) : K)
        = ((ω ^ (2 ^ f - 1) : Kˣ) : K) ^ (2 ^ f + 1) := by rw [pow_succ]
      _ = 1 := h2
  · intro h
    have h1 : orderOf ω ∣ 2 ^ f - 1 := orderOf_dvd_of_pow_eq_one h
    rw [hord] at h1
    have h2 : 0 < 2 ^ f - 1 := by omega
    have h3 := Nat.le_of_dvd h2 h1
    have h4 : 2 * 2 ^ f ≤ (2 ^ f) ^ 2 := by nlinarith
    omega

end Elements

section Centralizer

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

omit [Finite K] [CharP K 2] in
theorem blockScalar_val (ν μ : Kˣ) :
    ((diagU ![ν, ν, ν, μ, μ] : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) =
      Matrix.diagonal ![(ν : K), ν, ν, μ, μ] := by
  rw [diagU_val]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem comm_blocks_of_blockScalar (i : Fin 4) (hi : i = 0 ∨ i = 1 ∨ i = 3) (ν μ : Kˣ)
    {g : Su K 2 f 5} (hg : (g : GL (Fin 5) K) = diagU ![ν, ν, ν, μ, μ]) {u : Su K 2 f 5}
    (hu : u ∈ blk5 K f i) : g * u = u * g := by
  obtain ⟨A, rfl⟩ := hu
  refine Subtype.ext (Units.ext ?_)
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [coe_blockEmb2_mat, hg, blockScalar_val,
    Matrix.eta_fin_two (((A : Su K 2 f 2) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)]
  rcases hi with rfl | rfl | rfl
  · exact diag_comm_blockMat_zero _ _ _ _ _ _
  · exact diag_comm_blockMat_one _ _ _ _ _ _
  · exact diag_comm_blockMat_three _ _ _ _ _ _

omit [Finite K] [CharP K 2] in
theorem diag_separates (t : K) (ht1 : t ≠ 1) (htinv : t⁻¹ ≠ 1) (httt : t⁻¹ ≠ t) (x y : Fin 5)
    (hxy : x ≠ y) :
    (![t, t⁻¹, 1, 1, 1] y ≠ ![t, t⁻¹, 1, 1, 1] x) ∨
      (![(1 : K), t, t⁻¹, 1, 1] y ≠ ![(1 : K), t, t⁻¹, 1, 1] x) ∨
      (![(1 : K), 1, 1, t, t⁻¹] y ≠ ![(1 : K), 1, 1, t, t⁻¹] x) := by
  have h1 : (1 : K) ≠ t := fun h => ht1 h.symm
  have h2 : (1 : K) ≠ t⁻¹ := fun h => htinv h.symm
  have h3 : t ≠ t⁻¹ := fun h => httt h.symm
  fin_cases x <;> fin_cases y <;> first
    | exact absurd rfl hxy
    | simp [ht1, htinv, httt, h1, h2, h3]

theorem eq_diag_of_comm_blocks (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (g : Su K 2 f 5)
    (h0 : ∀ u ∈ blk5 K f 0, g * u = u * g) (h1 : ∀ u ∈ blk5 K f 1, g * u = u * g)
    (h3 : ∀ u ∈ blk5 K f 3, g * u = u * g) :
    ∃ ν μ : Kˣ, (g : GL (Fin 5) K) = diagU ![ν, ν, ν, μ, μ] := by
  obtain ⟨t, ht, ht1⟩ := exists_normOne_ne_one hK hf
  set G : Matrix (Fin 5) (Fin 5) K := ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) with hG
  have ht1' : (t : K) ≠ 1 := fun h => ht1 (Units.ext h)
  have htinv : (t : K)⁻¹ ≠ 1 := fun h => ht1' (inv_eq_one.mp h)
  have httt : (t : K)⁻¹ ≠ t := by
    intro h
    have h2 : (t : K) ^ 2 = 1 := by
      have : (t : K) * t = 1 := by
        calc (t : K) * t = (t : K) * (t : K)⁻¹ := by rw [h]
          _ = 1 := mul_inv_cancel₀ t.ne_zero
      rw [pow_two, this]
    have h3 : ((t : K) - 1) ^ 2 = 0 := by
      have h2' : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      have : ((t : K) - 1) ^ 2 = (t : K) ^ 2 - 1 := by
        linear_combination (-(t : K) + 1) * h2'
      rw [this, h2, sub_self]
    exact ht1' (sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h3))
  let tt : normOne (unitaryInvolution K 2 f) := ⟨t, ht⟩
  have hdiagval : ∀ i : Fin 4, (∀ u ∈ blk5 K f i, g * u = u * g) →
      G * blockMat 5 (i : ℕ) (Matrix.diagonal ![(t : K), (t : K)⁻¹]) =
        blockMat 5 (i : ℕ) (Matrix.diagonal ![(t : K), (t : K)⁻¹]) * G := by
    intro i hi
    have hc := comm_matrix (hi (blockEmb2 K 2 f 4 i (torusTwo (unitaryInvolution K 2 f) tt))
      ⟨_, rfl⟩)
    rw [coe_blockEmb2_mat, coe_torusTwo] at hc
    have hv : (fun j => ((![(tt : Kˣ), (tt : Kˣ)⁻¹] : Fin 2 → Kˣ) j : K)) =
        ![(t : K), (t : K)⁻¹] := by
      funext j
      fin_cases j <;> simp [tt]
    rw [hv] at hc
    exact hc
  have hE0 := hdiagval 0 h0
  have hE1 := hdiagval 1 h1
  have hE3 := hdiagval 3 h3
  simp only [Fin.val_zero, Fin.val_one] at hE0 hE1
  rw [blockMat_diag_zero] at hE0
  rw [blockMat_diag_one] at hE1
  have hE3' : G * Matrix.diagonal ![(1 : K), 1, 1, (t : K), (t : K)⁻¹] =
      Matrix.diagonal ![(1 : K), 1, 1, (t : K), (t : K)⁻¹] * G := by
    have h := hE3
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [e3, blockMat_diag_three] at h
    exact h
  have hoff : ∀ x y : Fin 5, x ≠ y → G x y = 0 := by
    intro x y hxy
    rcases diag_separates (t : K) ht1' htinv httt x y hxy with k | k | k
    · exact entry_zero_of_comm_diagonal hE0 k
    · exact entry_zero_of_comm_diagonal hE1 k
    · exact entry_zero_of_comm_diagonal hE3' k
  have hdiag : G.IsDiag := hoff
  have hsw : ∀ i : Fin 4, (∀ u ∈ blk5 K f i, g * u = u * g) →
      G * blockMat 5 (i : ℕ) (swapMatrix K (0 : Fin 2) 1) =
        blockMat 5 (i : ℕ) (swapMatrix K (0 : Fin 2) 1) * G := by
    intro i hi
    have hc := comm_matrix (hi (blockEmb2 K 2 f 4 i (swapSU2 (K := K) (f := f))) ⟨_, rfl⟩)
    rw [coe_blockEmb2_mat, coe_swapSU2] at hc
    exact hc
  have s0 := hsw 0 h0
  have s1 := hsw 1 h1
  have s3 := hsw 3 h3
  simp only [Fin.val_zero, Fin.val_one] at s0 s1
  rw [blockMat_swap_zero] at s0
  rw [blockMat_swap_one] at s1
  have s3' : G * swapMatrix K (3 : Fin 5) 4 = swapMatrix K (3 : Fin 5) 4 * G := by
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [e3, blockMat_swap_three] at s3
    exact s3
  have d01 : G 0 0 = G 1 1 := diag_entry_eq_of_comm_swap s0
  have d12 : G 1 1 = G 2 2 := diag_entry_eq_of_comm_swap s1
  have d34 : G 3 3 = G 4 4 := diag_entry_eq_of_comm_swap s3'
  obtain ⟨d, hd⟩ := exists_diagU_of_isDiag (g := (g : GL (Fin 5) K)) hdiag
  have hent : ∀ i, G i i = (d i : K) := by
    intro i
    rw [hG, ← hd, diagU_apply_same]
  refine ⟨d 0, d 3, ?_⟩
  rw [← hd]
  congr 1
  funext j
  have e01 : d 0 = d 1 := Units.ext (by rw [← hent, ← hent]; exact d01)
  have e12 : d 1 = d 2 := Units.ext (by rw [← hent, ← hent]; exact d12)
  have e34 : d 3 = d 4 := Units.ext (by rw [← hent, ← hent]; exact d34)
  fin_cases j
  · rfl
  · exact e01.symm
  · exact (e01.trans e12).symm
  · rfl
  · exact e34.symm

end Centralizer

section Cent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}

noncomputable abbrev centBlocks (K : Type) [Field K] [Finite K] [CharP K 2] (f : ℕ) :
    Subgroup (Su K 2 f 5) :=
  Subgroup.centralizer
    ((blk5 K f 0 ⊔ blk5 K f 1 ⊔ blk5 K f 3 : Subgroup (Su K 2 f 5)) : Set (Su K 2 f 5))

theorem mem_centBlocks_iff (hK : Nat.card K = (2 ^ f) ^ 2) (hf : 1 ≤ f) (g : Su K 2 f 5) :
    g ∈ centBlocks K f ↔ ∃ ν μ : Kˣ, (g : GL (Fin 5) K) = diagU ![ν, ν, ν, μ, μ] := by
  constructor
  · intro hg
    rw [Subgroup.mem_centralizer_iff] at hg
    refine eq_diag_of_comm_blocks hK hf g (fun u hu => ?_) (fun u hu => ?_) (fun u hu => ?_)
    · exact (hg u (Subgroup.mem_sup_left (Subgroup.mem_sup_left hu))).symm
    · exact (hg u (Subgroup.mem_sup_left (Subgroup.mem_sup_right hu))).symm
    · exact (hg u (Subgroup.mem_sup_right hu)).symm
  · rintro ⟨ν, μ, hg⟩
    rw [Subgroup.mem_centralizer_iff]
    have hle : (blk5 K f 0 ⊔ blk5 K f 1 ⊔ blk5 K f 3 : Subgroup (Su K 2 f 5)) ≤
        Subgroup.centralizer {g} := by
      refine sup_le (sup_le ?_ ?_) ?_
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact comm_blocks_of_blockScalar 0 (Or.inl rfl) ν μ hg hu
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact comm_blocks_of_blockScalar 1 (Or.inr (Or.inl rfl)) ν μ hg hu
      · intro u hu
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        rw [hx]
        exact comm_blocks_of_blockScalar 3 (Or.inr (Or.inr rfl)) ν μ hg hu
    intro x hx
    have := Subgroup.mem_centralizer_iff.mp (hle hx) g (Set.mem_singleton g)
    exact this.symm

omit [Finite K] [CharP K 2] in
theorem prod_blockScalar (ν μ : Kˣ) :
    ∏ i : Fin 5, ((![ν, ν, ν, μ, μ] i : Kˣ) : K) = (ν : K) ^ 3 * (μ : K) ^ 2 := by
  simp [Fin.prod_univ_five]
  ring

theorem blockScalar_mem_iff (ν μ : Kˣ) :
    (diagU ![ν, ν, ν, μ, μ] : GL (Fin 5) K) ∈ SUid (unitaryInvolution K 2 f) 5 ↔
      unitaryInvolution K 2 f (ν : K) * ν = 1 ∧ unitaryInvolution K 2 f (μ : K) * μ = 1 ∧
        (ν : K) ^ 3 * (μ : K) ^ 2 = 1 := by
  constructor
  · rintro ⟨hdet, hunit⟩
    rw [det_diagU, prod_blockScalar] at hdet
    rw [blockScalar_val, conjTr_diagonal, Matrix.diagonal_mul_diagonal] at hunit
    have h0 := congrFun (congrFun hunit 0) 0
    have h3 := congrFun (congrFun hunit 3) 3
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, Matrix.cons_val_zero] at h0
    simp only [Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h3
    exact ⟨by simpa using h0, by simpa using h3, hdet⟩
  · rintro ⟨hν, hμ, hdet⟩
    refine ⟨?_, ?_⟩
    · rw [det_diagU, prod_blockScalar]
      exact hdet
    · rw [blockScalar_val, conjTr_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext i
      fin_cases i <;> simpa using ‹_›

end Cent

end CFSG.RankThree.PartOne.CTP
