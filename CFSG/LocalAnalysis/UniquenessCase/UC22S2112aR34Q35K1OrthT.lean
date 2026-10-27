module

public import CFSG.Open.StatedDefs
public import CFSG.Open.PGLModelDefs
public import CFSG.ClassicalGroups.Orthogonal.SumSquaresDefs
import CFSG.ClassicalGroups.Orthogonal.MatrixIsometry
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
import CFSG.LocalAnalysis.QuasithinUnique.CompNormSylow
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Fin81Ref
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.GH74.GLS.Stage1.Thm3.Sec8 Equiv
open Matrix
open scoped commutatorElement

@[expose] def uc22s2112r34q35_Q7 {K : Type} [Field K] (e : K) (v : Fin 4 ⊕ Fin 3 → K) : K :=
  ∑ i, v (.inl i) ^ 2 + v (.inr 0) ^ 2 + v (.inr 1) ^ 2 + e * v (.inr 2) ^ 2

@[expose] def uc22s2112r34q35_Q8 {K : Type} [Field K] (e : K) (v : Fin 4 ⊕ Fin 4 → K) : K :=
  ∑ i, v (.inl i) ^ 2 + v (.inr 0) ^ 2 + v (.inr 1) ^ 2 + v (.inr 2) ^ 2 + e * v (.inr 3) ^ 2

@[expose] noncomputable def uc22s2112r34q35_signs (ι : Type) [Fintype ι] [DecidableEq ι]
    (K : Type) [Field K] : Subgroup (GL ι K) :=
  (TauCeti.diagGL.comp (MonoidHom.compLeft (Units.map (Int.castRingHom K).toMonoidHom) ι)).range

@[expose] def uc22s2112r34q35_W (κ : Type) [DecidableEq κ] (k₀ k₁ : κ) :
    Subgroup (Perm (Fin 4 ⊕ κ)) :=
  (Fin81.R0.prod (Subgroup.zpowers (swap k₀ k₁))).map (Perm.sumCongrHom (Fin 4) κ)

@[expose] noncomputable def uc22s2112r34q35_T (κ : Type) [Fintype κ] [DecidableEq κ] (k₀ k₁ : κ)
    (K : Type) [Field K] : Subgroup (GL (Fin 4 ⊕ κ) K) :=
  uc22s2112r34q35_signs (Fin 4 ⊕ κ) K ⊔ (uc22s2112r34q35_W κ k₀ k₁).map TauCeti.permutationGL

@[expose] noncomputable def uc22s2112r34q35_z1 (κ : Type) [Fintype κ] [DecidableEq κ]
    (K : Type) [Field K] : GL (Fin 4 ⊕ κ) K :=
  TauCeti.diagGL (Sum.elim (fun _ => -1) (fun _ => 1))

@[expose] def uc22s2112r34q35_permTest (κ : Type) [DecidableEq κ] (k₀ k₁ : κ) :
    Fin 3 → Perm (Fin 4 ⊕ κ) :=
  ![Perm.sumCongr (swap 0 1 * swap 2 3) 1, Perm.sumCongr (swap 0 2 * swap 1 3) 1,
    Perm.sumCongr (swap 0 1) (swap k₀ k₁)]

private def uc22s2112r34q35_coef7 {K : Type} [Field K] (e : K) : Fin 4 ⊕ Fin 3 → K :=
  Sum.elim (fun _ => 1) ![1, 1, e]

private def uc22s2112r34q35_coef8 {K : Type} [Field K] (e : K) : Fin 4 ⊕ Fin 4 → K :=
  Sum.elim (fun _ => 1) ![1, 1, 1, e]

private theorem uc22s2112r34q35_Q7_eq_sum {K : Type} [Field K] (e : K)
    (v : Fin 4 ⊕ Fin 3 → K) :
    uc22s2112r34q35_Q7 e v = ∑ l, uc22s2112r34q35_coef7 e l * v l ^ 2 := by
  rw [uc22s2112r34q35_Q7, Fintype.sum_sum_type]
  simp [uc22s2112r34q35_coef7, Fin.sum_univ_three]
  ring

private theorem uc22s2112r34q35_Q8_eq_sum {K : Type} [Field K] (e : K)
    (v : Fin 4 ⊕ Fin 4 → K) :
    uc22s2112r34q35_Q8 e v = ∑ l, uc22s2112r34q35_coef8 e l * v l ^ 2 := by
  rw [uc22s2112r34q35_Q8, Fintype.sum_sum_type]
  simp [uc22s2112r34q35_coef8, Fin.sum_univ_four]
  ring

private theorem uc22s2112r34q35_coef7_apply {K : Type} [Field K] (e : K)
    (l : Fin 4 ⊕ Fin 3) :
    uc22s2112r34q35_coef7 e l = if l = .inr 2 then e else 1 := by
  rcases l with i | j
  · fin_cases i <;> simp [uc22s2112r34q35_coef7]
  · fin_cases j <;> simp [uc22s2112r34q35_coef7]

private theorem uc22s2112r34q35_coef8_apply {K : Type} [Field K] (e : K)
    (l : Fin 4 ⊕ Fin 4) :
    uc22s2112r34q35_coef8 e l = if l = .inr 3 then e else 1 := by
  rcases l with i | j
  · fin_cases i <;> simp [uc22s2112r34q35_coef8]
  · fin_cases j <;> simp [uc22s2112r34q35_coef8]

private theorem uc22s2112r34q35_coef_singleton_invariant {M : Type} [DecidableEq M]
    {K : Type} [Field K] (p : M) (e : K) {π : Equiv.Perm M} (hπ : π p = p) (l : M) :
    (if π l = p then e else 1) = if l = p then e else 1 := by
  by_cases hl : l = p
  · subst hl
    rw [hπ]
  · have hne : π l ≠ p := by
      intro h
      apply hl
      have h' : π l = π p := by rw [h, hπ]
      exact π.injective h'
    rw [if_neg hne, if_neg hl]

private theorem uc22s2112r34q35_diagGL_mem_isometry {M K : Type} [Fintype M]
    [DecidableEq M] [Field K] (c : M → K) (Q : (M → K) → K)
    (hQ : ∀ v, Q v = ∑ l, c l * v l ^ 2) (d : M → Kˣ)
    (hd : ∀ l, ((d l : K)) ^ 2 = 1) :
    TauCeti.diagGL d ∈ CFSG.PGLModel.orthogonalGroup Q := by
  rw [CFSG.PGLModel.mem_orthogonalGroup_iff]
  intro v
  rw [hQ, hQ]
  have hmul : ((TauCeti.diagGL d : GL M K) : Matrix M M K) *ᵥ v =
      fun l => (d l : K) * v l := by
    rw [TauCeti.diagGL_coe]
    funext i
    rw [Matrix.mulVec_diagonal]
  rw [hmul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_pow, hd l, one_mul]

private theorem uc22s2112r34q35_permutationGL_mem_isometry {M K : Type} [Fintype M]
    [DecidableEq M] [Field K] (c : M → K) (Q : (M → K) → K)
    (hQ : ∀ v, Q v = ∑ l, c l * v l ^ 2) (π : Equiv.Perm M)
    (hπ : ∀ l, c (π l) = c l) :
    TauCeti.permutationGL π ∈ CFSG.PGLModel.orthogonalGroup Q := by
  rw [CFSG.PGLModel.mem_orthogonalGroup_iff]
  intro v
  rw [hQ, hQ]
  have hmul : ((TauCeti.permutationGL π : GL M K) : Matrix M M K) *ᵥ v =
      v ∘ ⇑π.symm := by
    rw [TauCeti.permutationGL_coe, Matrix.permMatrix_mulVec, Equiv.Perm.inv_def]
  rw [hmul]
  simp only [Function.comp_apply]
  rw [← Equiv.sum_comp π (fun l => c l * v (π.symm l) ^ 2)]
  simp only [Equiv.symm_apply_apply, hπ]

private theorem uc22s2112r34q35_units_map_int_cast_sq_one {K : Type} [Field K] (u : ℤˣ) :
    ((Units.map (Int.castRingHom K).toMonoidHom u : Kˣ) : K) ^ 2 = 1 := by
  have hu : u ^ 2 = 1 := by
    rcases Int.units_eq_one_or u with rfl | rfl <;> norm_num
  have h : Units.map (Int.castRingHom K).toMonoidHom u ^ 2 = 1 := by
    rw [← map_pow, hu, map_one]
  simpa using congrArg Units.val h

private theorem uc22s2112r34q35_units_map_int_cast_injective {K : Type} [Field K]
    (h2 : (2 : K) ≠ 0) :
    Function.Injective (Units.map (Int.castRingHom K).toMonoidHom) := by
  intro u v huv
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    rcases Int.units_eq_one_or v with rfl | rfl
  · rfl
  · exfalso
    have h : (1 : K) = -1 := by simpa using congrArg Units.val huv
    have hzero : (2 : K) = 0 := by
      have h' : (1 : K) + 1 = 0 := by
        have := congrArg (fun x : K => x + 1) h
        simpa using this
      rw [show (2 : K) = 1 + 1 by norm_num]
      exact h'
    exact h2 hzero
  · exfalso
    have h : (-1 : K) = 1 := by simpa using congrArg Units.val huv
    have hzero : (2 : K) = 0 := by
      have h' : (1 : K) + 1 = 0 := by
        have := congrArg (fun x : K => x + 1) h
        simpa using this.symm
      rw [show (2 : K) = 1 + 1 by norm_num]
      exact h'
    exact h2 hzero
  · rfl

private theorem uc22s2112r34q35_card_signs {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (h2 : (2 : K) ≠ 0) :
    Nat.card (uc22s2112r34q35_signs ι K) = 2 ^ Fintype.card ι := by
  let φ : (ι → ℤˣ) →* GL ι K :=
    TauCeti.diagGL.comp (MonoidHom.compLeft (Units.map (Int.castRingHom K).toMonoidHom) ι)
  have hφ : Function.Injective φ :=
    TauCeti.diagGL_injective.comp fun ε ε' h => by
      funext i
      exact uc22s2112r34q35_units_map_int_cast_injective h2 (congrFun h i)
  have hcard : Nat.card (uc22s2112r34q35_signs ι K) = Nat.card (ι → ℤˣ) := by
    rw [uc22s2112r34q35_signs]
    exact Nat.card_range_of_injective hφ
  rw [hcard, Nat.card_fun, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Fintype.card_units_int]

private theorem uc22s2112r34q35_negCoordGL_mem_signs {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (s : Finset ι) :
    negCoordGL (K := K) s ∈ uc22s2112r34q35_signs ι K := by
  rw [uc22s2112r34q35_signs, MonoidHom.mem_range]
  refine ⟨fun i => if i ∈ s then (-1 : ℤˣ) else 1, ?_⟩
  simp only [MonoidHom.comp_apply, negCoordGL]
  congr 1
  funext i
  by_cases hi : i ∈ s <;> simp [hi]

private theorem uc22s2112r34q35_permutationGL_injective {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] :
    Function.Injective (TauCeti.permutationGL (k := K) (ι := ι)) := by
  intro σ τ h
  have hmat : Equiv.Perm.permMatrix K σ⁻¹ = Equiv.Perm.permMatrix K τ⁻¹ := by
    have h' : ((TauCeti.permutationGL (k := K) σ : GL ι K) : Matrix ι ι K) =
        ((TauCeti.permutationGL (k := K) τ : GL ι K) : Matrix ι ι K) := by rw [h]
    simpa only [TauCeti.permutationGL_coe] using h'
  have hrow : ∀ (π : Equiv.Perm ι) (i : ι), Equiv.Perm.permMatrix K π.symm (π i) i = 1 := by
    intro π i
    simp
  ext i
  have h1 : Equiv.Perm.permMatrix K σ.symm (σ i) i =
      Equiv.Perm.permMatrix K τ.symm (σ i) i :=
    congrFun (congrFun hmat (σ i)) i
  rw [hrow σ i] at h1
  have h3 : Equiv.Perm.permMatrix K τ.symm (σ i) i =
      (Pi.single i (1 : K) : ι → K) (τ.symm (σ i)) := by
    have hh := congrFun (Matrix.permMatrix_mulVec (σ := τ.symm) (R := K)
      (v := (Pi.single i (1 : K) : ι → K))) (σ i)
    rw [Matrix.mulVec_single_one, Matrix.col_apply] at hh
    simpa [Function.comp_apply] using hh
  rw [h3] at h1
  by_cases hh : τ.symm (σ i) = i
  · have h2 : σ i = τ i := by
      have := congrArg (⇑τ) hh
      simpa using this
    exact h2
  · rw [show (Pi.single i (1 : K) : ι → K) (τ.symm (σ i)) = 0 by
      rw [Pi.single_eq_of_ne (M := fun _ => K) hh]] at h1
    exact absurd h1 (by norm_num)

private theorem uc22s2112r34q35_card_W {κ : Type} [Fintype κ] [DecidableEq κ] {k₀ k₁ : κ}
    (hk : k₀ ≠ k₁) :
    Nat.card (uc22s2112r34q35_W κ k₀ k₁) = 16 := by
  rw [uc22s2112r34q35_W, Subgroup.card_map_of_injective Equiv.Perm.sumCongrHom_injective,
    Nat.card_congr
      (Subgroup.prodEquiv Fin81.R0 (Subgroup.zpowers (Equiv.swap k₀ k₁))).toEquiv,
    Nat.card_prod, Fin81.card_R0, Nat.card_zpowers,
    (Equiv.Perm.swap_isSwap_iff.mpr hk).orderOf]

theorem uc22s2112r34q35_statedOmega_le {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type}
    [Field K] (Q : (ι → K) → K) : StatedOmega Q ≤ CFSG.PGLModel.orthogonalGroup Q := by
  show ⁅CFSG.MatrixModel.isometryCore Q, CFSG.MatrixModel.isometryCore Q⁆ ≤
    CFSG.MatrixModel.isometryCore Q
  exact Subgroup.commutator_le_self _

theorem uc22s2112r34q35_det_eq_one_of_mem_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {Q : (ι → K) → K} {g : GL ι K} (hg : g ∈ StatedOmega Q) :
    (g : Matrix ι ι K).det = 1 := by
  have hg' : g ∈ commutator (GL ι K) :=
    (Subgroup.commutator_mono (le_top : CFSG.MatrixModel.isometryCore Q ≤ ⊤) le_top) hg
  have hdet := Abelianization.commutator_subset_ker Matrix.GeneralLinearGroup.det hg'
  simpa using congrArg Units.val (MonoidHom.mem_ker.mp hdet)

private theorem uc22s2112r34q35_Q7_smul {K : Type} [Field K] (e : K) (c : K)
    (v : Fin 4 ⊕ Fin 3 → K) :
    uc22s2112r34q35_Q7 e (c • v) = c ^ 2 * uc22s2112r34q35_Q7 e v := by
  rw [uc22s2112r34q35_Q7_eq_sum, uc22s2112r34q35_Q7_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

private theorem uc22s2112r34q35_Q8_smul {K : Type} [Field K] (e : K) (c : K)
    (v : Fin 4 ⊕ Fin 4 → K) :
    uc22s2112r34q35_Q8 e (c • v) = c ^ 2 * uc22s2112r34q35_Q8 e v := by
  rw [uc22s2112r34q35_Q8_eq_sum, uc22s2112r34q35_Q8_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, mul_pow]
  ring

private theorem uc22s2112r34q35_Q7_single {K : Type} [Field K] (e : K) :
    uc22s2112r34q35_Q7 e (Pi.single (Sum.inl 0) (1 : K)) = 1 := by
  rw [uc22s2112r34q35_Q7_eq_sum, Finset.sum_eq_single (Sum.inl (0 : Fin 4))]
  · simp [uc22s2112r34q35_coef7]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem uc22s2112r34q35_Q8_single {K : Type} [Field K] (e : K) :
    uc22s2112r34q35_Q8 e (Pi.single (Sum.inl 0) (1 : K)) = 1 := by
  rw [uc22s2112r34q35_Q8_eq_sum, Finset.sum_eq_single (Sum.inl (0 : Fin 4))]
  · simp [uc22s2112r34q35_coef8]
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    ring
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem uc22s2112r34q35_signs_apply {ι K : Type} [Fintype ι] [DecidableEq ι]
    [Field K] (ε : ι → ℤˣ) :
    (TauCeti.diagGL.comp (MonoidHom.compLeft (Units.map (Int.castRingHom K).toMonoidHom) ι)) ε =
      TauCeti.diagGL (fun l => Units.map (Int.castRingHom K).toMonoidHom (ε l)) := by
  rw [MonoidHom.comp_apply]
  rfl

private theorem uc22s2112r34q35_conj_permutationGL_mem_signs {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (π : Equiv.Perm ι) {x : GL ι K}
    (hx : x ∈ uc22s2112r34q35_signs ι K) :
    TauCeti.permutationGL (k := K) π * x * (TauCeti.permutationGL (k := K) π)⁻¹ ∈
      uc22s2112r34q35_signs ι K := by
  rw [uc22s2112r34q35_signs, MonoidHom.mem_range] at hx ⊢
  obtain ⟨ε, rfl⟩ := hx
  refine ⟨fun i => ε (π.symm i), ?_⟩
  rw [uc22s2112r34q35_signs_apply, uc22s2112r34q35_signs_apply,
    TauCeti.mul_diagGL_of_coe_eq_permMatrix
      (g := TauCeti.permutationGL (k := K) π) (π := π.symm)
      (TauCeti.permutationGL_coe (k := K) π),
    mul_assoc, mul_inv_cancel, mul_one]
  rfl

private theorem uc22s2112r34q35_W_map_le_normalizer_signs {κ : Type} [Fintype κ]
    [DecidableEq κ] {k₀ k₁ : κ} (_hk : k₀ ≠ k₁) {K : Type} [Field K] :
    (uc22s2112r34q35_W κ k₀ k₁).map TauCeti.permutationGL ≤
      Subgroup.normalizer (uc22s2112r34q35_signs (Fin 4 ⊕ κ) K :
        Set (GL (Fin 4 ⊕ κ) K)) := by
  rintro g ⟨π, -, rfl⟩
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have hle : (uc22s2112r34q35_signs (Fin 4 ⊕ κ) K).map
      (MulAut.conj (TauCeti.permutationGL (k := K) π)).toMonoidHom ≤
      uc22s2112r34q35_signs (Fin 4 ⊕ κ) K := by
    rintro y ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using
      uc22s2112r34q35_conj_permutationGL_mem_signs π hx
  refine le_antisymm hle ?_
  intro x hx
  refine ⟨TauCeti.permutationGL (k := K) (π⁻¹) * x *
      (TauCeti.permutationGL (k := K) (π⁻¹))⁻¹, ?_, ?_⟩
  · simpa [MulAut.conj_apply] using
      uc22s2112r34q35_conj_permutationGL_mem_signs (π⁻¹) hx
  · rw [show TauCeti.permutationGL (k := K) (π⁻¹) =
        (TauCeti.permutationGL (k := K) π)⁻¹
      from map_inv (TauCeti.permutationGL (k := K)) π]
    change MulAut.conj (TauCeti.permutationGL (k := K) π)
      ((TauCeti.permutationGL (k := K) π)⁻¹ * x *
        ((TauCeti.permutationGL (k := K) π)⁻¹)⁻¹) = x
    rw [MulAut.conj_apply]
    group

private theorem uc22s2112r34q35_permutationGL_apply_self {ι K : Type} [Fintype ι]
    [DecidableEq ι] [Field K] (π : Equiv.Perm ι) (i : ι) :
    ((TauCeti.permutationGL (k := K) π : GL ι K) : Matrix ι ι K) (π i) i = 1 := by
  rw [TauCeti.permutationGL_coe, Equiv.Perm.inv_def]
  simp

private theorem uc22s2112r34q35_disjoint_signs_W_map {κ : Type} [Fintype κ]
    [DecidableEq κ] {k₀ k₁ : κ} (_hk : k₀ ≠ k₁) {K : Type} [Field K] :
    Disjoint (uc22s2112r34q35_signs (Fin 4 ⊕ κ) K)
      ((uc22s2112r34q35_W κ k₀ k₁).map TauCeti.permutationGL) := by
  rw [Subgroup.disjoint_def]
  intro x hx1 hx2
  rw [uc22s2112r34q35_signs, MonoidHom.mem_range] at hx1
  obtain ⟨ε, hε⟩ := hx1
  rw [Subgroup.mem_map] at hx2
  obtain ⟨π, -, rfl⟩ := hx2
  have hπ : π = 1 := by
    by_contra hne
    obtain ⟨i, hi⟩ := DFunLike.ne_iff.mp hne
    have hi' : π i ≠ i := by simpa using hi
    have h1 := uc22s2112r34q35_permutationGL_apply_self (K := K) π i
    rw [← hε, uc22s2112r34q35_signs_apply] at h1
    rw [TauCeti.diagGL_coe] at h1
    rw [Matrix.diagonal_apply_ne _ hi'] at h1
    exact absurd h1.symm one_ne_zero
  rw [hπ, map_one]

private theorem uc22s2112r34q35_sumCongr_mem_W {κ : Type} [DecidableEq κ] {k₀ k₁ : κ}
    {σ : Equiv.Perm (Fin 4)} {τ : Equiv.Perm κ}
    (hσ : σ ∈ Fin81.R0) (hτ : τ ∈ Subgroup.zpowers (Equiv.swap k₀ k₁)) :
    Equiv.Perm.sumCongr σ τ ∈ uc22s2112r34q35_W κ k₀ k₁ := by
  rw [uc22s2112r34q35_W]
  exact Subgroup.mem_map.mpr ⟨(σ, τ), Subgroup.mem_prod.mpr ⟨hσ, hτ⟩, rfl⟩

private theorem uc22s2112r34q35_mem_T_of_mem_W {κ : Type} [Fintype κ] [DecidableEq κ]
    {k₀ k₁ : κ} {K : Type} [Field K] {π : Equiv.Perm (Fin 4 ⊕ κ)}
    (hπ : π ∈ uc22s2112r34q35_W κ k₀ k₁) :
    TauCeti.permutationGL (k := K) π ∈ uc22s2112r34q35_T κ k₀ k₁ K :=
  Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hπ)

private theorem uc22s2112r34q35_coef7_sumCongr {K : Type} [Field K] (e : K)
    (σ : Equiv.Perm (Fin 4)) {τ : Equiv.Perm (Fin 3)}
    (hτ : τ ∈ Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)) (l : Fin 4 ⊕ Fin 3) :
    uc22s2112r34q35_coef7 e ((Equiv.Perm.sumCongr σ τ) l) =
      uc22s2112r34q35_coef7 e l := by
  rw [uc22s2112r34q35_coef7_apply, uc22s2112r34q35_coef7_apply]
  refine uc22s2112r34q35_coef_singleton_invariant (Sum.inr 2) e ?_ l
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have h2 : (Equiv.Perm.sumCongr σ τ) (Sum.inr (2 : Fin 3)) = Sum.inr (τ 2) := by
    rw [Equiv.Perm.sumCongr_apply]
    rfl
  rw [h2, ← hm]
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
    (f := Equiv.swap (0 : Fin 3) 1) (x := (2 : Fin 3)) (by decide) m]

private theorem uc22s2112r34q35_coef8_sumCongr {K : Type} [Field K] (e : K)
    (σ : Equiv.Perm (Fin 4)) {τ : Equiv.Perm (Fin 4)}
    (hτ : τ ∈ Subgroup.zpowers (Equiv.swap (0 : Fin 4) 1)) (l : Fin 4 ⊕ Fin 4) :
    uc22s2112r34q35_coef8 e ((Equiv.Perm.sumCongr σ τ) l) =
      uc22s2112r34q35_coef8 e l := by
  rw [uc22s2112r34q35_coef8_apply, uc22s2112r34q35_coef8_apply]
  refine uc22s2112r34q35_coef_singleton_invariant (Sum.inr 3) e ?_ l
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hτ
  have h3 : (Equiv.Perm.sumCongr σ τ) (Sum.inr (3 : Fin 4)) = Sum.inr (τ 3) := by
    rw [Equiv.Perm.sumCongr_apply]
    rfl
  rw [h3, ← hm]
  rw [Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self
    (f := Equiv.swap (0 : Fin 4) 1) (x := (3 : Fin 4)) (by decide) m]

theorem uc22s2112r34q35_card_T {K : Type} [Field K] (h2 : (2 : K) ≠ 0) {κ : Type} [Fintype κ]
    [DecidableEq κ] {k₀ k₁ : κ} (hk : k₀ ≠ k₁) :
    Nat.card (uc22s2112r34q35_T κ k₀ k₁ K) = 2 ^ (4 + Fintype.card κ) * 16 := by
  rw [uc22s2112r34q35_T,
    CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
      (uc22s2112r34q35_W_map_le_normalizer_signs hk)
      (uc22s2112r34q35_disjoint_signs_W_map hk),
    uc22s2112r34q35_card_signs h2, Fintype.card_sum, Fintype.card_fin,
    Subgroup.card_map_of_injective uc22s2112r34q35_permutationGL_injective,
    uc22s2112r34q35_card_W hk]

theorem uc22s2112r34q35_T7_le {K : Type} [Field K] (e : K) :
    uc22s2112r34q35_T (Fin 3) 0 1 K ≤ CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q7 e) := by
  rw [uc22s2112r34q35_T]
  refine sup_le ?_ ?_
  · rintro g ⟨ε, rfl⟩
    rw [uc22s2112r34q35_signs_apply]
    exact uc22s2112r34q35_diagGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
      (fun l => uc22s2112r34q35_units_map_int_cast_sq_one _)
  · rintro g ⟨π, hπ, rfl⟩
    rw [uc22s2112r34q35_W] at hπ
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hπ
    obtain ⟨σ, τ⟩ := x
    have hxπ' : Equiv.Perm.sumCongr σ τ = π := by
      simpa only [Equiv.Perm.sumCongrHom_apply] using hxπ
    rw [← hxπ']
    rw [Subgroup.mem_prod] at hx
    exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
      (uc22s2112r34q35_coef7_sumCongr e σ hx.2)

theorem uc22s2112r34q35_T8_le {K : Type} [Field K] (e : K) :
    uc22s2112r34q35_T (Fin 4) 0 1 K ≤ CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q8 e) := by
  rw [uc22s2112r34q35_T]
  refine sup_le ?_ ?_
  · rintro g ⟨ε, rfl⟩
    rw [uc22s2112r34q35_signs_apply]
    exact uc22s2112r34q35_diagGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
      (fun l => uc22s2112r34q35_units_map_int_cast_sq_one _)
  · rintro g ⟨π, hπ, rfl⟩
    rw [uc22s2112r34q35_W] at hπ
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hπ
    obtain ⟨σ, τ⟩ := x
    have hxπ' : Equiv.Perm.sumCongr σ τ = π := by
      simpa only [Equiv.Perm.sumCongrHom_apply] using hxπ
    rw [← hxπ']
    rw [Subgroup.mem_prod] at hx
    exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
      (uc22s2112r34q35_coef8_sumCongr e σ hx.2)

theorem uc22s2112r34q35_exists_sylow_T7 {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (e : K)
    (hO : (Nat.card (CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q7 e))).factorization 2 =
      11) :
    ∃ S : Sylow 2 (StatedOmega (uc22s2112r34q35_Q7 e)),
      (S : Subgroup (StatedOmega (uc22s2112r34q35_Q7 e))).map
          (StatedOmega (uc22s2112r34q35_Q7 e)).subtype =
        uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e) := by
  let O := CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q7 e)
  let Ω := StatedOmega (uc22s2112r34q35_Q7 e)
  have hTO : uc22s2112r34q35_T (Fin 3) 0 1 K ≤ O := uc22s2112r34q35_T7_le e
  have hΩle : Ω ≤ O := uc22s2112r34q35_statedOmega_le _
  have hcardT : Nat.card ((uc22s2112r34q35_T (Fin 3) 0 1 K).subgroupOf O) =
      2 ^ (Nat.card O).factorization 2 := by
    rw [← Subgroup.card_subtype O ((uc22s2112r34q35_T (Fin 3) 0 1 K).subgroupOf O),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTO,
      uc22s2112r34q35_card_T (K := K) h2 (κ := Fin 3) (by decide), hO]
    norm_num
  let S₀ : Sylow 2 O := Sylow.ofCard _ hcardT
  have hΩnormal : (Ω.subgroupOf O).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΩle).mpr
      (Subgroup.normalizer_commutator_ge_left (H₁ := O) (H₂ := O))
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal S₀
    (Ω.subgroupOf O)
  let e' : Ω.subgroupOf O ≃* Ω := Subgroup.subgroupOfEquivOfLe hΩle
  have hsurj : Function.Surjective e'.toMonoidHom := fun y => ⟨e'.symm y, e'.apply_symm_apply y⟩
  refine ⟨P.mapSurjective hsurj, ?_⟩
  rw [Sylow.coe_mapSurjective]
  have hmap_eq : ((P : Subgroup (Ω.subgroupOf O)).map e'.toMonoidHom).map Ω.subtype =
      ((P : Subgroup (Ω.subgroupOf O)).map (Ω.subgroupOf O).subtype).map O.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap_eq, hP, Subgroup.map_inf_eq _ _ O.subtype O.subtype_injective,
    Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hTO, inf_eq_left.mpr hΩle]

theorem uc22s2112r34q35_exists_sylow_T8 {K : Type} [Field K] [Finite K] (h2 : (2 : K) ≠ 0)
    (e : K)
    (hO : (Nat.card (CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q8 e))).factorization 2 =
      12) :
    ∃ S : Sylow 2 (StatedOmega (uc22s2112r34q35_Q8 e)),
      (S : Subgroup (StatedOmega (uc22s2112r34q35_Q8 e))).map
          (StatedOmega (uc22s2112r34q35_Q8 e)).subtype =
        uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e) := by
  let O := CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q8 e)
  let Ω := StatedOmega (uc22s2112r34q35_Q8 e)
  have hTO : uc22s2112r34q35_T (Fin 4) 0 1 K ≤ O := uc22s2112r34q35_T8_le e
  have hΩle : Ω ≤ O := uc22s2112r34q35_statedOmega_le _
  have hcardT : Nat.card ((uc22s2112r34q35_T (Fin 4) 0 1 K).subgroupOf O) =
      2 ^ (Nat.card O).factorization 2 := by
    rw [← Subgroup.card_subtype O ((uc22s2112r34q35_T (Fin 4) 0 1 K).subgroupOf O),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTO,
      uc22s2112r34q35_card_T (K := K) h2 (κ := Fin 4) (by decide), hO]
    norm_num
  let S₀ : Sylow 2 O := Sylow.ofCard _ hcardT
  have hΩnormal : (Ω.subgroupOf O).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hΩle).mpr
      (Subgroup.normalizer_commutator_ge_left (H₁ := O) (H₂ := O))
  obtain ⟨P, hP⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal S₀
    (Ω.subgroupOf O)
  let e' : Ω.subgroupOf O ≃* Ω := Subgroup.subgroupOfEquivOfLe hΩle
  have hsurj : Function.Surjective e'.toMonoidHom := fun y => ⟨e'.symm y, e'.apply_symm_apply y⟩
  refine ⟨P.mapSurjective hsurj, ?_⟩
  rw [Sylow.coe_mapSurjective]
  have hmap_eq : ((P : Subgroup (Ω.subgroupOf O)).map e'.toMonoidHom).map Ω.subtype =
      ((P : Subgroup (Ω.subgroupOf O)).map (Ω.subgroupOf O).subtype).map O.subtype := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [hmap_eq, hP, Subgroup.map_inf_eq _ _ O.subtype O.subtype_injective,
    Sylow.coe_ofCard, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.mpr hTO, inf_eq_left.mpr hΩle]

theorem uc22s2112r34q35_isPGroup_scalars_Q7 {K : Type} [Field K] (e : K) :
    IsPGroup 2 ((StatedScalars (Fin 4 ⊕ Fin 3) K).subgroupOf
      (StatedOmega (uc22s2112r34q35_Q7 e))) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  have hgO : (g : GL (Fin 4 ⊕ Fin 3) K) ∈
      CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q7 e) :=
    uc22s2112r34q35_statedOmega_le _ g.1.2
  have hgS : (g : GL (Fin 4 ⊕ Fin 3) K) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 4 ⊕ Fin 3)).range := g.2
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hgS
  have hv := (CFSG.PGLModel.mem_orthogonalGroup_iff.mp hgO)
    (Pi.single (Sum.inl 0) (1 : K))
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_const_mulVec, uc22s2112r34q35_Q7_smul,
    uc22s2112r34q35_Q7_single, mul_one] at hv
  have hc2 : c ^ 2 = 1 := Units.ext (by simpa using hv)
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  have hgl : ((g : ↥(StatedOmega (uc22s2112r34q35_Q7 e))) : GL (Fin 4 ⊕ Fin 3) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 4 ⊕ Fin 3) c := hc.symm
  rw [hgl, ← map_pow, hc2, map_one]

theorem uc22s2112r34q35_isPGroup_scalars_Q8 {K : Type} [Field K] (e : K) :
    IsPGroup 2 ((StatedScalars (Fin 4 ⊕ Fin 4) K).subgroupOf
      (StatedOmega (uc22s2112r34q35_Q8 e))) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  rw [pow_one]
  have hgO : (g : GL (Fin 4 ⊕ Fin 4) K) ∈
      CFSG.PGLModel.orthogonalGroup (uc22s2112r34q35_Q8 e) :=
    uc22s2112r34q35_statedOmega_le _ g.1.2
  have hgS : (g : GL (Fin 4 ⊕ Fin 4) K) ∈
      (Matrix.GeneralLinearGroup.scalar (Fin 4 ⊕ Fin 4)).range := g.2
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hgS
  have hv := (CFSG.PGLModel.mem_orthogonalGroup_iff.mp hgO)
    (Pi.single (Sum.inl 0) (1 : K))
  rw [← hc, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.diagonal_const_mulVec, uc22s2112r34q35_Q8_smul,
    uc22s2112r34q35_Q8_single, mul_one] at hv
  have hc2 : c ^ 2 = 1 := Units.ext (by simpa using hv)
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  refine Subtype.ext ?_
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  have hgl : ((g : ↥(StatedOmega (uc22s2112r34q35_Q8 e))) : GL (Fin 4 ⊕ Fin 4) K) =
      Matrix.GeneralLinearGroup.scalar (Fin 4 ⊕ Fin 4) c := hc.symm
  rw [hgl, ← map_pow, hc2, map_one]

private theorem uc22s2112r34q35_negCoordGL_singleton_mul_self {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [Field K] (r : ι) :
    negCoordGL (K := K) {r} * negCoordGL (K := K) {r} = 1 := by
  simp only [negCoordGL]
  rw [← map_mul, ← map_one (TauCeti.diagGL (k := K) (ι := ι))]
  refine congrArg (TauCeti.diagGL (k := K) (ι := ι)) ?_
  funext i
  simp only [Pi.mul_apply, Pi.one_apply]
  split_ifs <;> simp

private theorem uc22s2112r34q35_negCoordGL_singleton_mul_singleton {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] {r s : ι} (hrs : r ≠ s) :
    negCoordGL (K := K) {r} * negCoordGL (K := K) {s} = negCoordGL (K := K) {r, s} := by
  simp only [negCoordGL]
  rw [← map_mul]
  refine congrArg (TauCeti.diagGL (k := K) (ι := ι)) ?_
  funext i
  by_cases hir : i = r
  · subst hir
    simp [hrs]
  by_cases his : i = s
  · subst his
    simp [hir]
  · simp [hir, his]

private theorem uc22s2112r34q35_swap_conj_negCoordGL_singleton {ι K : Type*}
    [Fintype ι] [DecidableEq ι] [Field K] {r s : ι} (hrs : r ≠ s) :
    TauCeti.permutationGL (k := K) (Equiv.swap r s) * negCoordGL (K := K) {r} *
        (TauCeti.permutationGL (k := K) (Equiv.swap r s))⁻¹ =
      negCoordGL (K := K) {s} := by
  have hswap : (Equiv.swap r s).symm = Equiv.swap r s := by
    simp
  have hfamily : (fun i => (if (Equiv.swap r s).symm i ∈ ({r} : Finset ι) then
        (-1 : Kˣ) else 1)) =
      fun i => if i ∈ ({s} : Finset ι) then (-1 : Kˣ) else 1 := by
    funext i
    rw [hswap]
    by_cases hir : i = r
    · subst hir
      simp [hrs, hrs.symm]
    by_cases his : i = s
    · subst his
      simp
    · simp [Equiv.swap_apply_of_ne_of_ne hir his, hir, his]
  simp only [negCoordGL]
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix
    (g := TauCeti.permutationGL (k := K) (Equiv.swap r s))
    (π := (Equiv.swap r s)⁻¹) (TauCeti.permutationGL_coe _),
    mul_inv_cancel_right]
  change TauCeti.diagGL (fun i => (if (Equiv.swap r s).symm i ∈ ({r} : Finset ι) then
      (-1 : Kˣ) else 1)) =
    TauCeti.diagGL (fun i => if i ∈ ({s} : Finset ι) then (-1 : Kˣ) else 1)
  rw [hfamily]

private theorem uc22s2112r34q35_negCoordGL_pair_eq_commutator {ι K : Type*} [Fintype ι]
    [DecidableEq ι] [Field K] {r s : ι} (hrs : r ≠ s) :
    negCoordGL (K := K) {r, s} =
      ⁅negCoordGL (K := K) {r}, TauCeti.permutationGL (k := K) (Equiv.swap r s)⁆ := by
  have hDinv : (negCoordGL (K := K) {r})⁻¹ = negCoordGL (K := K) {r} :=
    inv_eq_of_mul_eq_one_right (uc22s2112r34q35_negCoordGL_singleton_mul_self r)
  have hconj : TauCeti.permutationGL (k := K) (Equiv.swap r s) *
      (negCoordGL (K := K) {r})⁻¹ * (TauCeti.permutationGL (k := K) (Equiv.swap r s))⁻¹ =
        negCoordGL (K := K) {s} := by
    rw [hDinv]
    exact uc22s2112r34q35_swap_conj_negCoordGL_singleton hrs
  rw [commutatorElement_def]
  symm
  calc
    negCoordGL (K := K) {r} * TauCeti.permutationGL (k := K) (Equiv.swap r s) *
        (negCoordGL (K := K) {r})⁻¹ * (TauCeti.permutationGL (k := K) (Equiv.swap r s))⁻¹ =
      negCoordGL (K := K) {r} *
        (TauCeti.permutationGL (k := K) (Equiv.swap r s) *
          (negCoordGL (K := K) {r})⁻¹ *
            (TauCeti.permutationGL (k := K) (Equiv.swap r s))⁻¹) := by group
    _ = negCoordGL (K := K) {r} * negCoordGL (K := K) {s} := by rw [hconj]
    _ = negCoordGL (K := K) {r, s} :=
      uc22s2112r34q35_negCoordGL_singleton_mul_singleton hrs

private theorem uc22s2112r34q35_coef7_swap {K : Type} [Field K] (e : K)
    {i j : Fin 4 ⊕ Fin 3} (hi : i ≠ Sum.inr 2) (hj : j ≠ Sum.inr 2)
    (l : Fin 4 ⊕ Fin 3) :
    uc22s2112r34q35_coef7 e (Equiv.swap i j l) = uc22s2112r34q35_coef7 e l := by
  rw [uc22s2112r34q35_coef7_apply, uc22s2112r34q35_coef7_apply]
  by_cases hli : l = i
  · subst hli
    rw [Equiv.swap_apply_left]
    simp [hi, hj]
  · by_cases hlj : l = j
    · subst hlj
      rw [Equiv.swap_apply_right]
      simp [hi, hj]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

private theorem uc22s2112r34q35_coef8_swap {K : Type} [Field K] (e : K)
    {i j : Fin 4 ⊕ Fin 4} (hi : i ≠ Sum.inr 3) (hj : j ≠ Sum.inr 3)
    (l : Fin 4 ⊕ Fin 4) :
    uc22s2112r34q35_coef8 e (Equiv.swap i j l) = uc22s2112r34q35_coef8 e l := by
  rw [uc22s2112r34q35_coef8_apply, uc22s2112r34q35_coef8_apply]
  by_cases hli : l = i
  · subst hli
    rw [Equiv.swap_apply_left]
    simp [hi, hj]
  · by_cases hlj : l = j
    · subst hlj
      rw [Equiv.swap_apply_right]
      simp [hi, hj]
    · rw [Equiv.swap_apply_of_ne_of_ne hli hlj]

private theorem uc22s2112r34q35_coef7_of_fixes {K : Type} [Field K] (e : K)
    {π : Equiv.Perm (Fin 4 ⊕ Fin 3)} (hπ : π (Sum.inr 2) = Sum.inr 2)
    (l : Fin 4 ⊕ Fin 3) :
    uc22s2112r34q35_coef7 e (π l) = uc22s2112r34q35_coef7 e l := by
  rw [uc22s2112r34q35_coef7_apply, uc22s2112r34q35_coef7_apply]
  exact uc22s2112r34q35_coef_singleton_invariant (Sum.inr 2) e hπ l

private theorem uc22s2112r34q35_coef8_of_fixes {K : Type} [Field K] (e : K)
    {π : Equiv.Perm (Fin 4 ⊕ Fin 4)} (hπ : π (Sum.inr 3) = Sum.inr 3)
    (l : Fin 4 ⊕ Fin 4) :
    uc22s2112r34q35_coef8 e (π l) = uc22s2112r34q35_coef8 e l := by
  rw [uc22s2112r34q35_coef8_apply, uc22s2112r34q35_coef8_apply]
  exact uc22s2112r34q35_coef_singleton_invariant (Sum.inr 3) e hπ l

private def uc22s2112r34q35_cross (κ : Type) [DecidableEq κ] (a b : κ) :
    Equiv.Perm (Fin 4 ⊕ κ) :=
  Equiv.swap (α := Fin 4 ⊕ κ) (Sum.inl 0) (Sum.inr a) *
    Equiv.swap (α := Fin 4 ⊕ κ) (Sum.inl 1) (Sum.inr b)

theorem uc22s2112r34q35_negPair_mem_T7 {K : Type} [Field K] (e : K) {i j : Fin 4 ⊕ Fin 3}
    (hi : i ≠ .inr 2) (hj : j ≠ .inr 2) (hij : i ≠ j) :
    negCoordGL {i, j} ∈
      uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e) := by
  refine ⟨Subgroup.mem_sup_left (uc22s2112r34q35_negCoordGL_mem_signs _), ?_⟩
  rw [uc22s2112r34q35_negCoordGL_pair_eq_commutator hij]
  refine Subgroup.commutator_mem_commutator ?_ ?_
  · exact (uc22s2112r34q35_T7_le e)
      (Subgroup.mem_sup_left (uc22s2112r34q35_negCoordGL_mem_signs {i}))
  · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
      (uc22s2112r34q35_coef7_swap e hi hj)

theorem uc22s2112r34q35_negPair_mem_T8 {K : Type} [Field K] (e : K) {i j : Fin 4 ⊕ Fin 4}
    (hi : i ≠ .inr 3) (hj : j ≠ .inr 3) (hij : i ≠ j) :
    negCoordGL {i, j} ∈
      uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e) := by
  refine ⟨Subgroup.mem_sup_left (uc22s2112r34q35_negCoordGL_mem_signs _), ?_⟩
  rw [uc22s2112r34q35_negCoordGL_pair_eq_commutator hij]
  refine Subgroup.commutator_mem_commutator ?_ ?_
  · exact (uc22s2112r34q35_T8_le e)
      (Subgroup.mem_sup_left (uc22s2112r34q35_negCoordGL_mem_signs {i}))
  · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
      (uc22s2112r34q35_coef8_swap e hi hj)

theorem uc22s2112r34q35_permTest_mem_T7 {K : Type} [Field K] (e : K) (a : Fin 3) :
    TauCeti.permutationGL (uc22s2112r34q35_permTest (Fin 3) 0 1 a) ∈
      uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e) := by
  have hR : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) ∈ Fin81.R0 := by decide
  have hS : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ∈ Fin81.R0 := by decide
  have hA : (Equiv.swap 0 1 : Equiv.Perm (Fin 4)) ∈ Fin81.R0 := by decide
  refine ⟨?_, ?_⟩
  · fin_cases a
    · simpa [uc22s2112r34q35_permTest] using
        uc22s2112r34q35_mem_T_of_mem_W (K := K)
          (uc22s2112r34q35_sumCongr_mem_W hR (Subgroup.one_mem _))
    · simpa [uc22s2112r34q35_permTest] using
        uc22s2112r34q35_mem_T_of_mem_W (K := K)
          (uc22s2112r34q35_sumCongr_mem_W hS (Subgroup.one_mem _))
    · simpa [uc22s2112r34q35_permTest] using
        uc22s2112r34q35_mem_T_of_mem_W (K := K)
          (uc22s2112r34q35_sumCongr_mem_W hA (Subgroup.mem_zpowers _))
  · fin_cases a
    · change TauCeti.permutationGL (uc22s2112r34q35_permTest (Fin 3) 0 1 0) ∈
        StatedOmega (uc22s2112r34q35_Q7 e)
      have hid : uc22s2112r34q35_permTest (Fin 3) 0 1 0 =
          ⁅Equiv.Perm.sumCongr
              (Equiv.swap (0 : Fin 4) (2 : Fin 4) * Equiv.swap (1 : Fin 4) (3 : Fin 4))
              (1 : Equiv.Perm (Fin 3)),
            Equiv.Perm.sumCongr (Equiv.swap (0 : Fin 4) (1 : Fin 4))
              (1 : Equiv.Perm (Fin 3))⁆ := by
        simp only [uc22s2112r34q35_permTest]
        decide
      rw [hid, map_commutatorElement]
      refine Subgroup.commutator_mem_commutator ?_ ?_
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
          (uc22s2112r34q35_coef7_of_fixes e (by decide))
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
          (uc22s2112r34q35_coef7_of_fixes e (by decide))
    · change TauCeti.permutationGL (uc22s2112r34q35_permTest (Fin 3) 0 1 1) ∈
        StatedOmega (uc22s2112r34q35_Q7 e)
      have hid : uc22s2112r34q35_permTest (Fin 3) 0 1 1 =
          ⁅Equiv.Perm.sumCongr
              (Equiv.swap (0 : Fin 4) (1 : Fin 4) * Equiv.swap (2 : Fin 4) (3 : Fin 4))
              (1 : Equiv.Perm (Fin 3)),
            Equiv.Perm.sumCongr (Equiv.swap (0 : Fin 4) (2 : Fin 4))
              (1 : Equiv.Perm (Fin 3))⁆ := by
        simp only [uc22s2112r34q35_permTest]
        decide
      rw [hid, map_commutatorElement]
      refine Subgroup.commutator_mem_commutator ?_ ?_
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
          (uc22s2112r34q35_coef7_of_fixes e (by decide))
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
          (uc22s2112r34q35_coef7_of_fixes e (by decide))
    · change TauCeti.permutationGL (uc22s2112r34q35_permTest (Fin 3) 0 1 2) ∈
        StatedOmega (uc22s2112r34q35_Q7 e)
      have hid : uc22s2112r34q35_permTest (Fin 3) 0 1 2 =
          ⁅uc22s2112r34q35_cross (Fin 3) 0 1,
            Equiv.Perm.sumCongr (Equiv.swap (0 : Fin 4) (1 : Fin 4))
              (1 : Equiv.Perm (Fin 3))⁆ := by
        ext x
        rcases x with i | j
        · fin_cases i <;> decide
        · fin_cases j <;> decide
      rw [hid, map_commutatorElement]
      refine Subgroup.commutator_mem_commutator ?_ ?_
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
          (uc22s2112r34q35_coef7_of_fixes e (by decide))
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q7_eq_sum e) _
          (uc22s2112r34q35_coef7_of_fixes e (by decide))

theorem uc22s2112r34q35_permTest_mem_T8 {K : Type} [Field K] (e : K) (a : Fin 3) :
    TauCeti.permutationGL (uc22s2112r34q35_permTest (Fin 4) 0 1 a) ∈
      uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e) := by
  have hR : (Equiv.swap 0 1 * Equiv.swap 2 3 : Equiv.Perm (Fin 4)) ∈ Fin81.R0 := by decide
  have hS : (Equiv.swap 0 2 * Equiv.swap 1 3 : Equiv.Perm (Fin 4)) ∈ Fin81.R0 := by decide
  have hA : (Equiv.swap 0 1 : Equiv.Perm (Fin 4)) ∈ Fin81.R0 := by decide
  refine ⟨?_, ?_⟩
  · fin_cases a
    · simpa [uc22s2112r34q35_permTest] using
        uc22s2112r34q35_mem_T_of_mem_W (K := K)
          (uc22s2112r34q35_sumCongr_mem_W hR (Subgroup.one_mem _))
    · simpa [uc22s2112r34q35_permTest] using
        uc22s2112r34q35_mem_T_of_mem_W (K := K)
          (uc22s2112r34q35_sumCongr_mem_W hS (Subgroup.one_mem _))
    · simpa [uc22s2112r34q35_permTest] using
        uc22s2112r34q35_mem_T_of_mem_W (K := K)
          (uc22s2112r34q35_sumCongr_mem_W hA (Subgroup.mem_zpowers _))
  · fin_cases a
    · change TauCeti.permutationGL (uc22s2112r34q35_permTest (Fin 4) 0 1 0) ∈
        StatedOmega (uc22s2112r34q35_Q8 e)
      have hid : uc22s2112r34q35_permTest (Fin 4) 0 1 0 =
          ⁅Equiv.Perm.sumCongr
              (Equiv.swap (0 : Fin 4) (2 : Fin 4) * Equiv.swap (1 : Fin 4) (3 : Fin 4))
              (1 : Equiv.Perm (Fin 4)),
            Equiv.Perm.sumCongr (Equiv.swap (0 : Fin 4) (1 : Fin 4))
              (1 : Equiv.Perm (Fin 4))⁆ := by
        simp only [uc22s2112r34q35_permTest]
        decide
      rw [hid, map_commutatorElement]
      refine Subgroup.commutator_mem_commutator ?_ ?_
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
          (uc22s2112r34q35_coef8_of_fixes e (by decide))
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
          (uc22s2112r34q35_coef8_of_fixes e (by decide))
    · change TauCeti.permutationGL (uc22s2112r34q35_permTest (Fin 4) 0 1 1) ∈
        StatedOmega (uc22s2112r34q35_Q8 e)
      have hid : uc22s2112r34q35_permTest (Fin 4) 0 1 1 =
          ⁅Equiv.Perm.sumCongr
              (Equiv.swap (0 : Fin 4) (1 : Fin 4) * Equiv.swap (2 : Fin 4) (3 : Fin 4))
              (1 : Equiv.Perm (Fin 4)),
            Equiv.Perm.sumCongr (Equiv.swap (0 : Fin 4) (2 : Fin 4))
              (1 : Equiv.Perm (Fin 4))⁆ := by
        simp only [uc22s2112r34q35_permTest]
        decide
      rw [hid, map_commutatorElement]
      refine Subgroup.commutator_mem_commutator ?_ ?_
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
          (uc22s2112r34q35_coef8_of_fixes e (by decide))
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
          (uc22s2112r34q35_coef8_of_fixes e (by decide))
    · change TauCeti.permutationGL (uc22s2112r34q35_permTest (Fin 4) 0 1 2) ∈
        StatedOmega (uc22s2112r34q35_Q8 e)
      have hid : uc22s2112r34q35_permTest (Fin 4) 0 1 2 =
          ⁅uc22s2112r34q35_cross (Fin 4) 0 1,
            Equiv.Perm.sumCongr (Equiv.swap (0 : Fin 4) (1 : Fin 4))
              (1 : Equiv.Perm (Fin 4))⁆ := by
        ext x
        rcases x with i | j
        · fin_cases i <;> decide
        · fin_cases j <;> decide
      rw [hid, map_commutatorElement]
      refine Subgroup.commutator_mem_commutator ?_ ?_
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
          (uc22s2112r34q35_coef8_of_fixes e (by decide))
      · exact uc22s2112r34q35_permutationGL_mem_isometry _ _ (uc22s2112r34q35_Q8_eq_sum e) _
          (uc22s2112r34q35_coef8_of_fixes e (by decide))

theorem uc22s2112r34q35_z1_mem_T7 {K : Type} [Field K] (e : K) :
    uc22s2112r34q35_z1 (Fin 3) K ∈
      uc22s2112r34q35_T (Fin 3) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q7 e) := by
  have hz : uc22s2112r34q35_z1 (Fin 3) K =
      negCoordGL (K := K) ({Sum.inl 0, Sum.inl 1} : Finset (Fin 4 ⊕ Fin 3)) *
        negCoordGL (K := K) ({Sum.inl 2, Sum.inl 3} : Finset (Fin 4 ⊕ Fin 3)) := by
    simp only [uc22s2112r34q35_z1, negCoordGL, ← TauCeti.diagGL.map_mul]
    congr 1
    funext l
    rcases l with i | j
    · fin_cases i <;> simp
    · fin_cases j <;> simp
  rw [hz]
  exact mul_mem (uc22s2112r34q35_negPair_mem_T7 e (by decide) (by decide) (by decide))
    (uc22s2112r34q35_negPair_mem_T7 e (by decide) (by decide) (by decide))

theorem uc22s2112r34q35_z1_mem_T8 {K : Type} [Field K] (e : K) :
    uc22s2112r34q35_z1 (Fin 4) K ∈
      uc22s2112r34q35_T (Fin 4) 0 1 K ⊓ StatedOmega (uc22s2112r34q35_Q8 e) := by
  have hz : uc22s2112r34q35_z1 (Fin 4) K =
      negCoordGL (K := K) ({Sum.inl 0, Sum.inl 1} : Finset (Fin 4 ⊕ Fin 4)) *
        negCoordGL (K := K) ({Sum.inl 2, Sum.inl 3} : Finset (Fin 4 ⊕ Fin 4)) := by
    simp only [uc22s2112r34q35_z1, negCoordGL, ← TauCeti.diagGL.map_mul]
    congr 1
    funext l
    rcases l with i | j
    · fin_cases i <;> simp
    · fin_cases j <;> simp
  rw [hz]
  exact mul_mem (uc22s2112r34q35_negPair_mem_T8 e (by decide) (by decide) (by decide))
    (uc22s2112r34q35_negPair_mem_T8 e (by decide) (by decide) (by decide))

private theorem uc22s2112r34q35_diagGL_commute_z1 {κ : Type} [Fintype κ] [DecidableEq κ]
    {K : Type} [Field K] (d : Fin 4 ⊕ κ → Kˣ) :
    TauCeti.diagGL d * uc22s2112r34q35_z1 κ K =
      uc22s2112r34q35_z1 κ K * TauCeti.diagGL d := by
  rw [uc22s2112r34q35_z1, ← TauCeti.diagGL.map_mul, ← TauCeti.diagGL.map_mul]
  congr 1
  funext l
  rw [Pi.mul_apply, Pi.mul_apply, mul_comm]

private theorem uc22s2112r34q35_z1_coe_comp {κ : Type} {K : Type} [Field K]
    (π : Equiv.Perm (Fin 4 ⊕ κ)) (hπ : ∃ σ τ, π = Equiv.Perm.sumCongr σ τ) :
    (Sum.elim (fun _ => (-1 : Kˣ)) (fun _ => 1)) ∘ π =
      Sum.elim (fun _ => (-1 : Kˣ)) (fun _ => 1) := by
  obtain ⟨σ, τ, rfl⟩ := hπ
  funext l
  rcases l with i | j <;> rfl

private theorem uc22s2112r34q35_permutationGL_commute_z1 {κ : Type} [Fintype κ]
    [DecidableEq κ] {k₀ k₁ : κ} {K : Type} [Field K] {π : Equiv.Perm (Fin 4 ⊕ κ)}
    (hπ : π ∈ uc22s2112r34q35_W κ k₀ k₁) :
    TauCeti.permutationGL (k := K) π * uc22s2112r34q35_z1 κ K =
      uc22s2112r34q35_z1 κ K * TauCeti.permutationGL (k := K) π := by
  rw [uc22s2112r34q35_W] at hπ
  obtain ⟨x, -, hxπ⟩ := Subgroup.mem_map.mp hπ
  obtain ⟨σ, τ⟩ := x
  have hπ_eq : Equiv.Perm.sumCongr σ τ = π := by
    simpa only [Equiv.Perm.sumCongrHom_apply] using hxπ
  have hsymm : π.symm = Equiv.Perm.sumCongr σ.symm τ.symm := by
    rw [← hπ_eq, Equiv.Perm.sumCongr_symm]
  have hd : (Sum.elim (fun _ => (-1 : Kˣ)) (fun _ => 1)) ∘ π.symm =
      Sum.elim (fun _ => (-1 : Kˣ)) (fun _ => 1) :=
    uc22s2112r34q35_z1_coe_comp π.symm ⟨σ.symm, τ.symm, hsymm⟩
  rw [uc22s2112r34q35_z1]
  rw [TauCeti.mul_diagGL_of_coe_eq_permMatrix
    (g := TauCeti.permutationGL (k := K) π) (π := π.symm)
    (TauCeti.permutationGL_coe (k := K) π)]
  rw [hd]

theorem uc22s2112r34q35_commute_z1 {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    {k₀ k₁ : κ} {g : GL (Fin 4 ⊕ κ) K} (hg : g ∈ uc22s2112r34q35_T κ k₀ k₁ K) :
    g * uc22s2112r34q35_z1 κ K = uc22s2112r34q35_z1 κ K * g := by
  have hle : uc22s2112r34q35_T κ k₀ k₁ K ≤
      Subgroup.centralizer ({uc22s2112r34q35_z1 κ K} : Set (GL (Fin 4 ⊕ κ) K)) := by
    rw [uc22s2112r34q35_T]
    refine sup_le ?_ ?_
    · rintro x ⟨d, rfl⟩
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      rw [uc22s2112r34q35_signs_apply]
      exact uc22s2112r34q35_diagGL_commute_z1 _
    · rintro x ⟨π, hπ, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (uc22s2112r34q35_permutationGL_commute_z1 hπ)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hg)

end CFSG.LocalAnalysis.UniquenessCase.UC22
