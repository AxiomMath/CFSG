module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328

open CFSG.Open
open scoped Matrix commutatorElement

private theorem k328r2f_scalars {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    {ω : F} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 ∧ ω ≠ 1 ∧ ω ^ 2 ≠ ω := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := 2) (by rw [hF]; norm_num)
  refine ⟨by linear_combination (ω - 1) * hω, fun h => ?_, fun h => ?_⟩
  · have h2 : (1 : F) + 1 = 0 := CharTwo.add_self_eq_zero 1
    rw [h] at hω
    exact one_ne_zero (by linear_combination hω - h2 : (1 : F) = 0)
  · have h2 : ω + ω = 0 := CharTwo.add_self_eq_zero ω
    exact one_ne_zero (by linear_combination hω - h - h2 : (1 : F) = 0)

private theorem k328r2f_order {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {z : GL ι F} {d : ι → F} (hz : (z : Matrix ι ι F) = Matrix.diagonal d)
    (h3 : ∀ i, d i ^ 3 = 1) (i₀ : ι) (h1 : d i₀ ≠ 1) : orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  apply orderOf_eq_prime
  · apply Units.ext
    rw [Units.val_pow_eq_pow_val, hz, Matrix.diagonal_pow, Units.val_one,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    exact h3 i
  · intro h
    apply h1
    have := congrArg (fun g : GL ι F => (g : Matrix ι ι F) i₀ i₀) h
    simpa [hz] using this

private theorem k328r2f_commute {F : Type} [Field F] {ι : Type} [Fintype ι] [DecidableEq ι]
    {z t : GL ι F} {d e : ι → F} (hz : (z : Matrix ι ι F) = Matrix.diagonal d)
    (ht : (t : Matrix ι ι F) = Matrix.diagonal e) : z * t = t * z := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz, ht, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

private theorem k328r2f_not_mem {F : Type} [Field F] {ω : F} (hω2 : ω ^ 2 ≠ ω)
    {z t : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (ht : (t : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1]))
    (hord : orderOf z = 3) : t ∉ Subgroup.zpowers z := by
  intro h
  have hfin : IsOfFinOrder z := orderOf_pos_iff.mp (by rw [hord]; norm_num)
  rw [← hfin.mem_powers_iff_mem_zpowers] at h
  obtain ⟨n, hn⟩ := h
  have h1 := congrArg (fun g : GL (Fin 3 ⊕ Fin 3) F =>
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (Sum.inl 0) (Sum.inl 0)) hn
  have h2 := congrArg (fun g : GL (Fin 3 ⊕ Fin 3) F =>
    (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) (Sum.inl 1) (Sum.inl 1)) hn
  simp [Units.val_pow_eq_pow_val, hz, ht, Matrix.diagonal_pow] at h1 h2
  exact hω2 (h2.symm.trans h1)

private theorem k328r2f_exists_blk {F : Type} [Field F] {X Y : Matrix (Fin 3) (Fin 3) F}
    (h : Xᵀ * Y = 1) :
    ∃ A : GL (Fin 3 ⊕ Fin 3) F,
      (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y := by
  have hY : Y * Xᵀ = 1 := mul_eq_one_comm.mp h
  have hX : X * Yᵀ = 1 := by
    simpa [Matrix.transpose_mul] using congrArg Matrix.transpose hY
  have hYX : Yᵀ * X = 1 := mul_eq_one_comm.mp hX
  refine ⟨⟨Matrix.fromBlocks X 0 0 Y, Matrix.fromBlocks Yᵀ 0 0 Xᵀ, ?_, ?_⟩, rfl⟩
  · simp [Matrix.fromBlocks_multiply, hX, hY]
  · simp [Matrix.fromBlocks_multiply, hYX, h]

private theorem k328r2f_mem_sp {F : Type} [Field F] {A : GL (Fin 3 ⊕ Fin 3) F}
    {X Y : Matrix (Fin 3) (Fin 3) F}
    (hA : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y)
    (h : Xᵀ * Y = 1) : A ∈ StatedSp 3 F := by
  rw [StatedAPI.mem_statedSp_iff, hA]
  have hYX : Yᵀ * X = 1 := by simpa [Matrix.transpose_mul] using congrArg Matrix.transpose h
  simp [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, h, hYX]

private theorem k328r2f_comm_z {F : Type} [Field F] {ω : F} {z A : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {X Y : Matrix (Fin 3) (Fin 3) F}
    (hA : (A : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks X 0 0 Y) :
    A ∈ Subgroup.centralizer {z} := by
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  have hz' : (g : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.fromBlocks (Matrix.scalar (Fin 3) ω) 0 0 (Matrix.scalar (Fin 3) (ω ^ 2)) := by
    rw [hz, ← Matrix.fromBlocks_diagonal]
    congr 2 <;> (funext i; fin_cases i <;> rfl)
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, hz', hA, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero]
  rw [(Matrix.scalar_commute ω (fun r => Commute.all ω r) X).eq,
    (Matrix.scalar_commute (ω ^ 2) (fun r => Commute.all (ω ^ 2) r) Y).eq]

private theorem k328r2f_mem_stdComp {F : Type} [Field F] {ω : F} {z w : GL (Fin 3 ⊕ Fin 3) F}
    (hz : (z : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    {X₁ Y₁ X₂ Y₂ U V : Matrix (Fin 3) (Fin 3) F} (h₁ : X₁ᵀ * Y₁ = 1) (h₂ : X₂ᵀ * Y₂ = 1)
    (hw : (w : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks U 0 0 V)
    (hU : X₁ * X₂ = U * (X₂ * X₁)) (hV : Y₁ * Y₂ = V * (Y₂ * Y₁)) :
    w ∈ stdComp (StatedSp 3 F) z := by
  obtain ⟨A, hA⟩ := k328r2f_exists_blk h₁
  obtain ⟨B, hB⟩ := k328r2f_exists_blk h₂
  have hAC : A ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z} :=
    ⟨k328r2f_mem_sp hA h₁, k328r2f_comm_z hz hA⟩
  have hBC : B ∈ StatedSp 3 F ⊓ Subgroup.centralizer {z} :=
    ⟨k328r2f_mem_sp hB h₂, k328r2f_comm_z hz hB⟩
  have hAB : A * B = w * (B * A) := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, hA, hB, hw]
    simp [Matrix.fromBlocks_multiply, hU, hV]
  have hcomm : ⁅A, B⁆ = w := by
    rw [commutatorElement_def, hAB]
    group
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator hAC hBC

private theorem k328r2f_orth_P {F : Type} [Field F] :
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F)ᵀ *
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem k328r2f_orth_tau {F : Type} [Field F] :
    (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F)ᵀ *
      !![0, 1, 0; 1, 0, 0; 0, 0, 1] = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]

private theorem k328r2f_orth_D {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1) :
    (Matrix.diagonal ![1, ω ^ 2, ω] : Matrix (Fin 3) (Fin 3) F)ᵀ *
      Matrix.diagonal ![1, ω, ω ^ 2] = 1 := by
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp <;> linear_combination h3

private theorem k328r2f_orth_D' {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1) :
    (Matrix.diagonal ![1, ω, ω ^ 2] : Matrix (Fin 3) (Fin 3) F)ᵀ *
      Matrix.diagonal ![1, ω ^ 2, ω] = 1 := by
  rw [Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp <;> linear_combination h3

private theorem k328r2f_comm_PD {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1) :
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal ![1, ω ^ 2, ω] =
      Matrix.diagonal ![ω, ω, ω] *
        (Matrix.diagonal ![1, ω ^ 2, ω] * !![0, 0, 1; 1, 0, 0; 0, 1, 0]) := by
  have h1 : ω * ω ^ 2 = 1 := by linear_combination h3
  have h2 : ω * ω = ω ^ 2 := (sq ω).symm
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, h1, h2]

private theorem k328r2f_comm_PD' {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1) :
    (!![0, 0, 1; 1, 0, 0; 0, 1, 0] : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal ![1, ω, ω ^ 2] =
      Matrix.diagonal ![ω ^ 2, ω ^ 2, ω ^ 2] *
        (Matrix.diagonal ![1, ω, ω ^ 2] * !![0, 0, 1; 1, 0, 0; 0, 1, 0]) := by
  have h1 : ω ^ 2 * ω = 1 := by linear_combination h3
  have h2 : ω ^ 2 * ω ^ 2 = ω := by linear_combination ω * h3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, h1, h2]

private theorem k328r2f_comm_tauD {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1) :
    (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal ![1, ω, ω ^ 2] =
      Matrix.diagonal ![ω, ω ^ 2, 1] *
        (Matrix.diagonal ![1, ω, ω ^ 2] * !![0, 1, 0; 1, 0, 0; 0, 0, 1]) := by
  have h1 : ω ^ 2 * ω = 1 := by linear_combination h3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, h1]

private theorem k328r2f_comm_tauD' {F : Type} [Field F] {ω : F} (h3 : ω ^ 3 = 1) :
    (!![0, 1, 0; 1, 0, 0; 0, 0, 1] : Matrix (Fin 3) (Fin 3) F) * Matrix.diagonal ![1, ω ^ 2, ω] =
      Matrix.diagonal ![ω ^ 2, ω, 1] *
        (Matrix.diagonal ![1, ω ^ 2, ω] * !![0, 1, 0; 1, 0, 0; 0, 0, 1]) := by
  have h1 : ω * ω ^ 2 = 1 := by linear_combination h3
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Matrix.diagonal_apply, h1]

theorem row2_facts (F : Type) [Field F] [Fintype F] [DecidableEq F]
    (hF : Fintype.card F = 4) (ω : F)
    (hω : ω ^ 2 + ω + 1 = 0) (z₀ t₀ : GL (Fin 3 ⊕ Fin 3) F)
    (hz : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω, ω] ![ω ^ 2, ω ^ 2, ω ^ 2]))
    (ht : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) =
      Matrix.diagonal (Sum.elim ![ω, ω ^ 2, 1] ![ω ^ 2, ω, 1])) :
    FactsLeaf (StatedSp 3 F) z₀ t₀ := by
  obtain ⟨h3, hω1, hω2⟩ := k328r2f_scalars hF hω
  have h6 : (ω ^ 2) ^ 3 = 1 := by rw [← pow_mul, mul_comm, pow_mul, h3, one_pow]
  have ho₁ : orderOf z₀ = 3 :=
    k328r2f_order hz (fun i => by rcases i with i | i <;> fin_cases i <;> simp [h3, h6])
      (Sum.inl 0) (by simpa using hω1)
  have ho₂ : orderOf t₀ = 3 :=
    k328r2f_order ht (fun i => by rcases i with i | i <;> fin_cases i <;> simp [h3, h6])
      (Sum.inl 0) (by simpa using hω1)
  have hzw : (z₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks
      (Matrix.diagonal ![ω, ω, ω]) 0 0 (Matrix.diagonal ![ω ^ 2, ω ^ 2, ω ^ 2]) := by
    rw [hz, Matrix.fromBlocks_diagonal]
  have htw : (t₀ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) F) = Matrix.fromBlocks
      (Matrix.diagonal ![ω, ω ^ 2, 1]) 0 0 (Matrix.diagonal ![ω ^ 2, ω, 1]) := by
    rw [ht, Matrix.fromBlocks_diagonal]
  have hzs : z₀ ∈ stdComp (StatedSp 3 F) z₀ :=
    k328r2f_mem_stdComp hz k328r2f_orth_P (k328r2f_orth_D h3) hzw (k328r2f_comm_PD h3)
      (k328r2f_comm_PD' h3)
  have hts : t₀ ∈ stdComp (StatedSp 3 F) z₀ :=
    k328r2f_mem_stdComp hz k328r2f_orth_tau (k328r2f_orth_D' h3) htw (k328r2f_comm_tauD h3)
      (k328r2f_comm_tauD' h3)
  exact ⟨stdComp_le _ _ hzs, hzs, hts, ho₁, ho₂, k328r2f_commute hz ht,
    k328r2f_not_mem hω2 hz ht ho₁⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.K328
