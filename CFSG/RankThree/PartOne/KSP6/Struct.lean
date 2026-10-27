module

public import CFSG.RankThree.PartOne.KSP6.Aut

public section

namespace CFSG.RankThree.PartOne.KSP6

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.RankThree.Classical CFSG.Assembly.LowTwoRank

section Root

variable {K : Type} [Field K]

theorem mul_single_mul_apply {n : Type} [Fintype n] [DecidableEq n] (P Q : Matrix n n K)
    (r c : n) (s : K) (i j : n) :
    (P * Matrix.single r c s * Q) i j = P i r * s * Q c j := by
  simp only [Matrix.mul_apply, Matrix.single_apply]
  rw [Finset.sum_eq_single c]
  · simp [mul_assoc]
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

theorem nmat_single (a : K) :
    nmat (Matrix.single (0 : Fin 3) 0 a) = Matrix.single (Sum.inl 0) (Sum.inr 0) a := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [nmat, Matrix.single_apply]

@[expose] def longAdd (K : Type) [Field K] : K →+ symMatrices 3 K where
  toFun a := ⟨Matrix.single 0 0 a, by rw [mem_symMatrices]; simp⟩
  map_zero' := by
    apply Subtype.ext
    simp
  map_add' a b := by
    apply Subtype.ext
    simp [Matrix.single_add]

@[expose] def longRoot (K : Type) [Field K] : Subgroup (StatedSp 3 K) :=
  ((siegelSpHom 3 K).comp (AddMonoidHom.toMultiplicative (longAdd K))).range

theorem mem_longRoot {g : StatedSp 3 K} :
    g ∈ longRoot K ↔ ∃ a : K, mat g = fromBlocks 1 (Matrix.single 0 0 a) 0 1 := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨Multiplicative.toAdd a, rfl⟩
  · rintro ⟨a, ha⟩
    refine ⟨Multiplicative.ofAdd a, ?_⟩
    apply mat_inj
    rw [ha]
    rfl

theorem longRoot_le_siegel : longRoot K ≤ siegelRadicalSp 3 K := by
  intro g hg
  obtain ⟨a, ha⟩ := mem_longRoot.1 hg
  exact mem_siegelRadicalSp.2 ⟨Matrix.single 0 0 a, by simp, ha⟩

theorem exists_ne_one_mem_longRoot : ∃ x ∈ longRoot K, x ≠ 1 := by
  obtain ⟨g, hg, hgm⟩ := exists_siegel_elt (B := Matrix.single (0 : Fin 3) 0 (1 : K)) (by simp)
  refine ⟨g, mem_longRoot.2 ⟨1, hgm⟩, fun hg1 => ?_⟩
  have := congrArg (fun M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K => M (Sum.inl 0) (Sum.inr 0))
    (hgm.symm.trans (hg1 ▸ mat_one))
  simp at this

theorem longRoot_central {u x : StatedSp 3 K} (hu : u ∈ unipotent 3 K) (hx : x ∈ longRoot K) :
    u * x = x * u := by
  obtain ⟨A, C, hA, hC, hum⟩ := hu
  obtain ⟨a, hxa⟩ := mem_longRoot.1 hx
  have hum' : mat u = blockMat A C := hum
  have h10 : A 1 0 = 0 := hA.1 (show (0 : Fin 3) < 1 by decide)
  have h20 : A 2 0 = 0 := hA.1 (show (0 : Fin 3) < 2 by decide)
  have hAe : A * Matrix.single 0 0 a * Aᵀ = Matrix.single 0 0 a := by
    ext i j
    rw [mul_single_mul_apply]
    fin_cases i <;> fin_cases j <;> simp [Matrix.transpose_apply, h10, h20, hA.2 0]
  apply mat_inj
  rw [mat_mul, mat_mul, hum', hxa, blockMat_mul_siegel hA.isUnit_det, hAe]

end Root

section Stable

variable {K : Type} [Field K] [Finite K] [CharP K 2]

omit [CharP K 2] in
theorem exists_unipotent_preimage {β : MulAut (StatedSp 3 K)}
    (hU : ∀ u ∈ unipotent 3 K, β u ∈ unipotent 3 K) :
    ∀ u ∈ unipotent 3 K, ∃ u' ∈ unipotent 3 K, β u' = u := by
  have hinj : Function.Injective
      (fun u : ↥(unipotent 3 K) => (⟨β u.1, hU u.1 u.2⟩ : ↥(unipotent 3 K))) := by
    intro u w h
    apply Subtype.ext
    exact β.injective (congrArg Subtype.val h)
  intro u hu
  obtain ⟨w, hw⟩ := (Finite.injective_iff_surjective.1 hinj) ⟨u, hu⟩
  exact ⟨w.1, w.2, congrArg Subtype.val hw⟩

theorem longRoot_stable {β : MulAut (StatedSp 3 K)}
    (hU : ∀ u ∈ unipotent 3 K, β u ∈ unipotent 3 K) :
    ∀ x ∈ longRoot K, β x ∈ longRoot K := by
  classical
  have hV := siegel_char hU
  obtain ⟨A, σ, hAσ⟩ := exists_conjSp_fieldSp β
  intro x hx
  obtain ⟨a, hxa⟩ := mem_longRoot.1 hx
  have hCs : (Matrix.single (0 : Fin 3) (0 : Fin 3) a)ᵀ = Matrix.single 0 0 a := by simp
  obtain ⟨hsym, hz⟩ := psi_spec hAσ hV hCs hxa
  set C' := psiMap (gm A) (gmi A) σ (Matrix.single (0 : Fin 3) (0 : Fin 3) a) with hC'
  have hcent : ∀ u ∈ unipotent 3 K, u * β x = β x * u := by
    intro u hu
    obtain ⟨u', hu', rfl⟩ := exists_unipotent_preimage hU u hu
    rw [← map_mul, ← map_mul, longRoot_central hu' hx]
  have hentry : ∀ i j, C' i j =
      gm A (Sum.inl i) (Sum.inl 0) * σ a * gmi A (Sum.inr 0) (Sum.inr j) := by
    intro i j
    rw [hC', psiMap, Matrix.toBlocks₁₂, Matrix.of_apply]
    have : (Matrix.single (0 : Fin 3) (0 : Fin 3) a).map σ = Matrix.single 0 0 (σ a) := by
      ext k l
      by_cases h : (0 : Fin 3) = k ∧ (0 : Fin 3) = l
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · simp [h]
    rw [this, nmat_single, mul_single_mul_apply]
  have hfix : ∀ a' b' c' : K, ut3 a' b' c' * C' * (ut3 a' b' c')ᵀ = C' := by
    intro a' b' c'
    obtain ⟨u, hu, hum⟩ := exists_mem_unipotent (isUnitriangular_ut3 a' b' c')
      (Matrix.transpose_zero : (0 : Matrix (Fin 3) (Fin 3) K)ᵀ = 0)
    exact fix_of_comm (isUnitriangular_ut3 a' b' c').isUnit_det hum hz (hcent u hu)
  have h1 := (fixes_iff' (a := 0) (b := 0) (c := 1) hsym).1 (hfix 0 0 1)
  have h2 := (fixes_iff' (a := 0) (b := 1) (c := 0) hsym).1 (hfix 0 1 0)
  have h3 := (fixes_iff' (a := 1) (b := 0) (c := 0) hsym).1 (hfix 1 0 0)
  have h22 : C' 2 2 = 0 := by linear_combination h1.2.2.1
  have h12 : C' 1 2 = 0 := by linear_combination h1.2.1
  have h02 : C' 0 2 = 0 := by linear_combination h2.2.1
  have h11 : C' 1 1 = 0 := by linear_combination h3.1
  have hsym01 : C' 1 0 = C' 0 1 := by
    have := congrFun (congrFun hsym 0) 1
    simpa [Matrix.transpose_apply] using this
  have hminor : C' 0 1 * C' 1 0 = C' 0 0 * C' 1 1 := by
    rw [hentry, hentry, hentry, hentry]
    ring
  have h01 : C' 0 1 = 0 := by
    rw [hsym01, h11, mul_zero] at hminor
    exact mul_self_eq_zero.1 hminor
  refine mem_longRoot.2 ⟨C' 0 0, ?_⟩
  rw [hz]
  congr 2
  rw [sym3_eq hsym]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sym3, h01, h02, h11, h12, h22]

end Stable

end CFSG.RankThree.PartOne.KSP6
