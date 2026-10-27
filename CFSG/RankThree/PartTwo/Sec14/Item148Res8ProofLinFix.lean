module

public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofLinRat
public import CFSG.RankThree.PartTwo.Sec14.Item148Res8ProofLinRoot

public section

namespace CFSG.RankThree.PartTwo.Sec14.Item148Res8

open Matrix

variable {K : Type} [Field K]

section Spread

variable (H : Subgroup (SpecialLinearGroup (Fin 3) K))

theorem transvection_02_mem_of_mem
    (h1 : ∀ (i j : Fin 3) (hij : i ≠ j), SpecialLinearGroup.transvection hij (1 : K) ∈ H)
    {i j : Fin 3} (hij : i ≠ j) {a : K} (ha : SpecialLinearGroup.transvection hij a ∈ H) :
    SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a ∈ H := by
  have r01 : SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) a ∈ H →
      SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a ∈ H :=
    transvection_mem_of_mem_left H (by decide) (by decide) (by decide) (h1 1 2 (by decide))
  have r12 : SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) a ∈ H →
      SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a ∈ H :=
    transvection_mem_of_mem_right H (by decide : (0 : Fin 3) ≠ 1) (by decide) (by decide)
      (h1 0 1 (by decide))
  have r10 : SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 0) a ∈ H →
      SpecialLinearGroup.transvection (by decide : (1 : Fin 3) ≠ 2) a ∈ H :=
    transvection_mem_of_mem_left H (by decide) (by decide) (by decide) (h1 0 2 (by decide))
  have r21 : SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) a ∈ H →
      SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 1) a ∈ H :=
    transvection_mem_of_mem_right H (by decide : (0 : Fin 3) ≠ 2) (by decide) (by decide)
      (h1 0 2 (by decide))
  have r20 : SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 0) a ∈ H →
      SpecialLinearGroup.transvection (by decide : (2 : Fin 3) ≠ 1) a ∈ H :=
    transvection_mem_of_mem_left H (by decide) (by decide) (by decide) (h1 0 1 (by decide))
  fin_cases i <;> fin_cases j
  · exact absurd rfl hij
  · exact r01 ha
  · exact ha
  · exact r12 (r10 ha)
  · exact absurd rfl hij
  · exact r12 ha
  · exact r01 (r21 (r20 ha))
  · exact r01 (r21 ha)
  · exact absurd rfl hij

end Spread

section Conj

variable [Finite K] [CharP K 2]

theorem dot_mul_dot_mem' (F₀ : Subfield K) {n : ℕ} (hn : 2 ≤ n)
    (hF₀ : Nat.card F₀ = 2 ^ n) (hK : Nat.card K = 2 ^ (3 * n))
    (H : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hι : (SpecialLinearGroup.map F₀.subtype).range ≤ H) {i j : Fin 3} (hij : i ≠ j)
    (hS : ∀ a : K, SpecialLinearGroup.transvection hij a ∈ H → a ∈ F₀)
    {h : SpecialLinearGroup (Fin 3) K} (hh : h ∈ H) {w ψ : Fin 3 → K} (hw : ∀ r, w r ∈ F₀)
    (hψ : ∀ r, ψ r ∈ F₀) (hψw : ψ ⬝ᵥ w = 0) :
    (((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).row j ⬝ᵥ w) *
      (ψ ⬝ᵥ (h : Matrix (Fin 3) (Fin 3) K).col i) ∈ F₀ := by
  have hψw' : (fun r => (⟨ψ r, hψ r⟩ : F₀)) ⬝ᵥ (fun r => (⟨w r, hw r⟩ : F₀)) = 0 := by
    apply Subtype.ext
    simpa [dotProduct, Fin.sum_univ_three] using hψw
  exact dot_mul_dot_mem F₀ hn hF₀ hK H hι hij hS hh _ _ hψw'

theorem conj_single_entry_mem (F₀ : Subfield K) {n : ℕ}
    (hn : 2 ≤ n) (hF₀ : Nat.card F₀ = 2 ^ n) (hK : Nat.card K = 2 ^ (3 * n))
    (H : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hι : (SpecialLinearGroup.map F₀.subtype).range ≤ H) {i j : Fin 3} (hij : i ≠ j)
    (hS : ∀ a : K, SpecialLinearGroup.transvection hij a ∈ H → a ∈ F₀)
    {h : SpecialLinearGroup (Fin 3) K} (hh : h ∈ H) (r c : Fin 3) :
    ((h : Matrix (Fin 3) (Fin 3) K) * single i j (1 : K) *
      ((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) r c ∈ F₀ := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  set hM := (h : Matrix (Fin 3) (Fin 3) K) with hhM
  set hiM := ((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hhiM
  have hN : ∀ r c, (hM * single i j (1 : K) * hiM) r c = hM r i * hiM j c := by
    intro r c
    rw [mul_single_mul, vecMulVec_apply]
    rfl
  rw [hN]
  have hsingle : ∀ k, ∀ r, (Pi.single k (1 : K) : Fin 3 → K) r ∈ F₀ := by
    intro k r
    by_cases hr : r = k
    · subst hr; simp [F₀.one_mem]
    · simp [hr, F₀.zero_mem]
  have hoff : ∀ r c, r ≠ c → hM r i * hiM j c ∈ F₀ := by
    intro r c hrc
    have := dot_mul_dot_mem' F₀ hn hF₀ hK H hι hij hS hh (w := Pi.single c 1)
      (ψ := Pi.single r 1) (hsingle c) (hsingle r)
      (by rw [single_dotProduct, one_mul, Pi.single_eq_of_ne hrc])
    rw [dotProduct_single, single_dotProduct, mul_one, one_mul] at this
    rw [mul_comm]
    exact this
  by_cases hrc : r = c
  swap
  · exact hoff r c hrc
  subst hrc
  have hdiag : ∀ a b : Fin 3, a ≠ b →
      hM a i * hiM j a + hM b i * hiM j b ∈ F₀ := by
    intro a b hab
    set e : Fin 3 → K := Pi.single a 1 + Pi.single b 1 with he
    have heF : ∀ r, e r ∈ F₀ := fun r => F₀.add_mem (hsingle a r) (hsingle b r)
    have hee : e ⬝ᵥ e = 0 := by
      rw [he, add_dotProduct, dotProduct_add, dotProduct_add, single_dotProduct,
        single_dotProduct, single_dotProduct, single_dotProduct]
      simp [hab, hab.symm]
      linear_combination h2
    have := dot_mul_dot_mem' F₀ hn hF₀ hK H hι hij hS hh heF heF hee
    rw [he, dotProduct_add, dotProduct_single, dotProduct_single, add_dotProduct,
      single_dotProduct, single_dotProduct] at this
    have hab' := hoff a b hab
    have hba' := hoff b a hab.symm
    have e2 : (hiM.row j a * 1 + hiM.row j b * 1) *
        (1 * hM.col i a + 1 * hM.col i b) =
        (hM a i * hiM j a + hM b i * hiM j b) + (hM a i * hiM j b + hM b i * hiM j a) := by
      simp only [Matrix.row_apply, Matrix.col_apply]
      ring
    rw [e2] at this
    have := F₀.sub_mem this (F₀.add_mem hab' hba')
    rwa [add_sub_cancel_right] at this
  have htr : hM 0 i * hiM j 0 + hM 1 i * hiM j 1 + hM 2 i * hiM j 2 = 0 := by
    have hhi : hiM * hM = 1 := by
      have : ((h⁻¹ * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
        rw [inv_mul_cancel]; rfl
      exact this
    have := congrFun (congrFun hhi j) i
    rw [Matrix.mul_apply, Matrix.one_apply_ne hij.symm, Fin.sum_univ_three] at this
    linear_combination this
  have d01 := hdiag 0 1 (by decide)
  have d12 := hdiag 1 2 (by decide)
  have d0 : hM 0 i * hiM j 0 ∈ F₀ := by
    have e : hM 0 i * hiM j 0 = (hM 1 i * hiM j 1 + hM 2 i * hiM j 2) := by
      linear_combination htr - (hM 1 i * hiM j 1 + hM 2 i * hiM j 2) * h2
    rw [e]; exact d12
  have d1 : hM 1 i * hiM j 1 ∈ F₀ := by
    have := F₀.sub_mem d01 d0
    rwa [add_sub_cancel_left] at this
  fin_cases r
  · exact d0
  · exact d1
  · have := F₀.sub_mem d12 d1
    rwa [add_sub_cancel_left] at this

theorem exists_map_eq_smul (F₀ : Subfield K) {n : ℕ} (hn : 2 ≤ n)
    (hF₀ : Nat.card F₀ = 2 ^ n) (hK : Nat.card K = 2 ^ (3 * n))
    (H : Subgroup (SpecialLinearGroup (Fin 3) K))
    (hι : (SpecialLinearGroup.map F₀.subtype).range ≤ H)
    (hS : ∀ a : K, SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a ∈ H → a ∈ F₀)
    (σ : K ≃+* K) (hσ : ∀ x ∈ F₀, σ x = x) {h : SpecialLinearGroup (Fin 3) K} (hh : h ∈ H) :
    ∃ ζ : K, ζ ^ 3 = 1 ∧
      ((SpecialLinearGroup.map σ.toRingHom h : SpecialLinearGroup (Fin 3) K) :
        Matrix (Fin 3) (Fin 3) K) = ζ • (h : Matrix (Fin 3) (Fin 3) K) := by
  have h1 : ∀ (i j : Fin 3) (hij : i ≠ j), SpecialLinearGroup.transvection hij (1 : K) ∈ H := by
    intro i j hij
    exact hι ⟨SpecialLinearGroup.transvection hij 1, by
      rw [map_subtype_transvection]; rfl⟩
  have hSij : ∀ (i j : Fin 3) (hij : i ≠ j) (a : K),
      SpecialLinearGroup.transvection hij a ∈ H → a ∈ F₀ :=
    fun i j hij a ha => hS a (transvection_02_mem_of_mem H h1 hij ha)
  set hM := (h : Matrix (Fin 3) (Fin 3) K) with hhM
  set hiM := ((h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hhiM
  have hhi : hiM * hM = 1 := by
    have : ((h⁻¹ * h : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [inv_mul_cancel]; rfl
    exact this
  have hih : hM * hiM = 1 := by
    have : ((h * h⁻¹ : SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
      rw [mul_inv_cancel]; rfl
    exact this
  set sM := hM.map σ with hsM
  set siM := hiM.map σ with hsiM
  have hsi : siM * sM = 1 := by
    rw [hsM, hsiM, ← Matrix.map_mul, hhi, Matrix.map_one σ (map_zero σ) (map_one σ)]
  have hmap : ((SpecialLinearGroup.map σ.toRingHom h : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) = sM := by
    rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    rfl
  set X := hiM * sM with hX
  have hcomm : Pairwise fun i j : Fin 3 => Commute (single i j (1 : K)) X := by
    intro i j hij
    have hfix : (hM * single i j (1 : K) * hiM).map σ = hM * single i j (1 : K) * hiM := by
      ext r c
      rw [Matrix.map_apply]
      exact hσ _ (conj_single_entry_mem F₀ hn hF₀ hK H hι hij (hSij i j hij) hh r c)
    have hsingle : (single i j (1 : K)).map σ = single i j (1 : K) := by
      ext r c
      simp [Matrix.single_apply]
    rw [Matrix.map_mul, Matrix.map_mul, hsingle] at hfix
    show single i j 1 * X = X * single i j 1
    calc single i j (1 : K) * X = hiM * (hM * single i j 1 * hiM) * sM := by
          rw [hX]
          simp only [← Matrix.mul_assoc, hhi, Matrix.one_mul]
      _ = hiM * (sM * single i j 1 * siM) * sM := by rw [hfix]
      _ = X * single i j 1 := by
          rw [hX]
          simp only [Matrix.mul_assoc, hsi, Matrix.mul_one]
  obtain ⟨ζ, hζ⟩ := Matrix.mem_range_scalar_of_commute_single hcomm
  refine ⟨ζ, ?_, ?_⟩
  ·
    have hdet : X.det = 1 := by
      have e : (hM.map σ).det = σ hM.det := (RingHom.map_det σ.toRingHom hM).symm
      have hd1 : hM.det = 1 := h.2
      have hd2 : hiM.det = 1 := h⁻¹.2
      rw [hX, Matrix.det_mul, hsM, e, hd1, hd2, map_one, one_mul]
    rw [← hζ, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin] at hdet
    exact hdet
  · rw [hmap]
    have e : sM = hM * X := by
      rw [hX, ← Matrix.mul_assoc, hih, Matrix.one_mul]
    rw [e, ← hζ, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, Matrix.mul_smul,
      Matrix.mul_one]

end Conj

end CFSG.RankThree.PartTwo.Sec14.Item148Res8
