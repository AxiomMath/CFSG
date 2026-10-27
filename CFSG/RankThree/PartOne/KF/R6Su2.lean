module

public import CFSG.RankThree.PartOne.KF.R6LeviA

public section

namespace CFSG.RankThree.PartOne.KFU

open Matrix CFSG CFSG.LieType.Universal.Unitary CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

variable {K : Type} [Field K]

@[expose] def blk25 (X : Matrix (Fin 2) (Fin 2) K) : Matrix (Fin 5) (Fin 5) K :=
  !![X 0 0, 0, 0, 0, X 0 1; 0, 1, 0, 0, 0; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; X 1 0, 0, 0, 0, X 1 1]

theorem blk25_one : blk25 (1 : Matrix (Fin 2) (Fin 2) K) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk25]

theorem blk25_mul (X Y : Matrix (Fin 2) (Fin 2) K) : blk25 (X * Y) = blk25 X * blk25 Y := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blk25, Matrix.mul_apply, Fin.sum_univ_two, Fin.sum_univ_five]

@[expose] def e25 : Fin 2 ⊕ Fin 3 ≃ Fin 5 where
  toFun := Sum.elim ![0, 4] ![1, 2, 3]
  invFun := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inr 2, Sum.inl 1]
  left_inv := by decide
  right_inv := by decide

theorem blk25_eq_submatrix (X : Matrix (Fin 2) (Fin 2) K) :
    blk25 X = (Matrix.fromBlocks X 0 0 1).submatrix e25.symm e25.symm := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk25, e25]

theorem det_blk25 (X : Matrix (Fin 2) (Fin 2) K) : (blk25 X).det = X.det := by
  rw [blk25_eq_submatrix, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_one, mul_one]

theorem blk25_injective {X Y : Matrix (Fin 2) (Fin 2) K} (h : blk25 X = blk25 Y) : X = Y := by
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [blk25] using congrFun (congrFun h 0) 0
  · simpa [blk25] using congrFun (congrFun h 0) 4
  · simpa [blk25] using congrFun (congrFun h 4) 0
  · simpa [blk25] using congrFun (congrFun h 4) 4

theorem blk25_gram [CharP K 2] (X : Matrix (Fin 2) (Fin 2) K) (hX : X.det = 1) :
    (blk25 X)ᵀ * antidiag 5 * blk25 X = antidiag 5 := by
  rw [Matrix.det_fin_two] at hX
  ext i j
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  fin_cases i <;> fin_cases j <;>
    simp [blk25, antidiag, Matrix.mul_apply, Fin.sum_univ_five, Matrix.transpose_apply, Fin.rev]
  all_goals first
    | linear_combination (X 0 0 * X 1 0) * h2
    | linear_combination hX + (X 0 1 * X 1 0) * h2
    | linear_combination (X 0 1 * X 1 1) * h2

theorem map_blk25 (φ : K → K) (h0 : φ 0 = 0) (h1 : φ 1 = 1) (X : Matrix (Fin 2) (Fin 2) K) :
    (blk25 X).map φ = blk25 (X.map φ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [blk25, h0, h1]

variable (σ : K ≃+* K)

theorem blk25_conjTr_gram [CharP K 2] (X : Matrix (Fin 2) (Fin 2) K) (hX : X.det = 1)
    (hfix : ∀ i j, σ (X i j) = X i j) :
    conjTr σ (blk25 X) * antidiag 5 * blk25 X = antidiag 5 := by
  have hmap : X.map σ = X := by
    ext i j
    exact hfix i j
  have : conjTr σ (blk25 X) = (blk25 X)ᵀ := by
    rw [conjTr, map_blk25 σ (map_zero σ) (map_one σ), hmap]
  rw [this]
  exact blk25_gram X hX

@[expose] noncomputable def blkGL25 : SpecialLinearGroup (Fin 2) K →* GL (Fin 5) K where
  toFun A :=
    { val := blk25 (A : Matrix (Fin 2) (Fin 2) K)
      inv := blk25 ((A⁻¹ : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      val_inv := by
        rw [← blk25_mul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, blk25_one]
      inv_val := by
        rw [← blk25_mul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
          Matrix.SpecialLinearGroup.coe_one, blk25_one] }
  map_one' := by
    apply Units.ext
    simp [blk25_one]
  map_mul' A B := by
    apply Units.ext
    simp [blk25_mul]

variable [CharP K 2]

@[expose] noncomputable def su2Emb : SpecialLinearGroup (Fin 2) (fixF σ) →* ↥(SU σ 5) :=
  (blkGL25.comp (liftSL σ)).codRestrict (SU σ 5) (fun A => by
    refine mem_SU.mpr ⟨?_, ?_⟩
    · show (blk25 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)).det = 1
      rw [det_blk25]
      exact (liftSL σ A).2
    · show conjTr σ (blk25 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) :
        Matrix (Fin 2) (Fin 2) K)) * antidiag 5 *
          blk25 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
            antidiag 5
      exact blk25_conjTr_gram σ _ (liftSL σ A).2 (fun i j => (A i j).2))

theorem gu5_su2Emb (A : SpecialLinearGroup (Fin 2) (fixF σ)) :
    gu5 (su2Emb σ A) = blk25 ((liftSL σ A : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) :=
  rfl

theorem su2Emb_injective : Function.Injective (su2Emb σ) := by
  intro A B h
  apply liftSL_injective σ
  apply Subtype.ext
  have h1 := congrArg (fun g : ↥(SU σ 5) => gu5 g) h
  simp only [gu5_su2Emb] at h1
  exact blk25_injective h1

open CFSG.RankThree.PartOne.KFOUT3 in
omit [CharP K 2] in
theorem mem_range_su3Emb_of_entries (g : ↥(SU σ 5)) (e01 : gu5 g 0 1 = 0) (e03 : gu5 g 0 3 = 0)
    (e10 : gu5 g 1 0 = 0) (e12 : gu5 g 1 2 = 0) (e13 : gu5 g 1 3 = 0) (e14 : gu5 g 1 4 = 0)
    (e21 : gu5 g 2 1 = 0) (e23 : gu5 g 2 3 = 0) (e30 : gu5 g 3 0 = 0) (e31 : gu5 g 3 1 = 0)
    (e32 : gu5 g 3 2 = 0) (e34 : gu5 g 3 4 = 0) (e41 : gu5 g 4 1 = 0) (e43 : gu5 g 4 3 = 0)
    (hu : gu5 g 1 1 = 1) (hv : gu5 g 3 3 = 1) : g ∈ (su3Emb σ).range := by
  set m : Matrix (Fin 3) (Fin 3) K := (gu5 g).submatrix ![0, 2, 4] ![0, 2, 4] with hm
  have hm_apply : ∀ a b : Fin 3, m a b = gu5 g ((![0, 2, 4] : Fin 3 → Fin 5) a)
      ((![0, 2, 4] : Fin 3 → Fin 5) b) := fun a b => rfl
  have hgb : gu5 g = embMat35 m := by
    ext a b
    rw [embMat35_apply]
    fin_cases a <;> fin_cases b <;>
      simp [hm_apply, e01, e03, e10, e12, e13, e14, e21, e23, e30, e31, e32, e34, e41, e43, hu, hv]
  have hdet : m.det = 1 := by
    have h0 := (mem_SU.1 g.2).1
    rw [show ((g : GL (Fin 5) K) : Matrix (Fin 5) (Fin 5) K) = embMat35 m from hgb,
      det_embMat35] at h0
    exact h0
  have hcol : ∀ (a : Fin 3) (l : Fin 5), l ∉ Set.range (![0, 2, 4] : Fin 3 → Fin 5) →
      gu5 g l ((![0, 2, 4] : Fin 3 → Fin 5) a) = 0 := by
    intro a l hl
    have key : ∀ l : Fin 5, (∃ a : Fin 3, (![0, 2, 4] : Fin 3 → Fin 5) a = l) ∨ l = 1 ∨ l = 3 := by
      decide
    rcases key l with ⟨a', ha'⟩ | rfl | rfl
    · exact absurd ⟨a', ha'⟩ hl
    · fin_cases a <;> simp [e10, e12, e14]
    · fin_cases a <;> simp [e30, e32, e34]
  have hgm : conjTr σ m * antidiag 3 * m = antidiag 3 := by
    have := gram_block σ (![0, 2, 4] : Fin 3 → Fin 5) eig_inj_five eig_rev_five
      (m := gu5 g) (fun a l hl => hcol a l hl) (mem_SU.1 g.2).2
    simpa [hm] using this
  refine ⟨mkSU3 σ m hdet hgm, ?_⟩
  apply Subtype.ext
  apply Units.ext
  exact hgb.symm

theorem su2Emb_mem_range_su3Emb (A : SpecialLinearGroup (Fin 2) (fixF σ)) :
    su2Emb σ A ∈ (su3Emb σ).range := by
  apply mem_range_su3Emb_of_entries
  all_goals simp [gu5_su2Emb, blk25]

@[expose] def wSL (F : Type) [Field F] [CharP F 2] : SpecialLinearGroup (Fin 2) F :=
  ⟨!![0, 1; 1, 0], by
    rw [Matrix.det_fin_two_of]
    simp [CharTwo.neg_eq]⟩

theorem wSL_conj_diag2 {F : Type} [Field F] [CharP F 2] (a : Fˣ) :
    wSL F * diag2 a * (wSL F)⁻¹ = diag2 a⁻¹ := by
  apply Subtype.ext
  have hw : (wSL F)⁻¹ = wSL F := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_inv]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [wSL, Matrix.adjugate_fin_two, CharTwo.neg_eq]
  rw [hw]
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [wSL, diag2, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.vecMul_diagonal]

theorem gu5_su2Emb_diag2 (a : (fixF σ)ˣ) :
    gu5 (su2Emb σ (diag2 a)) = Matrix.diagonal fun i => ((dvec5 (upU σ a) 1 i : Kˣ) : K) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [gu5_su2Emb, blk25, liftSL_diag2, dvec5, coe_upU]

theorem su2Emb_diag2_eq_rho {p : ℕ} (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u)
    (u : ↥(rootsOfUnity p K)) (a : (fixF σ)ˣ) (ha : upU σ a = (u : Kˣ)) :
    su2Emb σ (diag2 a) = rhoSU3 hfix u := by
  apply Subtype.ext
  apply Units.ext
  show gu5 (su2Emb σ (diag2 a)) = Matrix.diagonal fun i => ((dvec5 (u : Kˣ) 1 i : Kˣ) : K)
  rw [gu5_su2Emb_diag2, ha]

theorem rhoSU3_mem_range_su2Emb {p : ℕ} (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u)
    (u : ↥(rootsOfUnity p K)) : rhoSU3 hfix u ∈ (su2Emb σ).range := by
  have hu : (u : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).1 u.2
  have hσu := hfix _ hu
  let a : (fixF σ)ˣ := Units.mk0 ⟨((u : Kˣ) : K), hσu⟩ (fun h0 => (u : Kˣ).ne_zero (congrArg Subtype.val h0))
  refine ⟨diag2 a, su2Emb_diag2_eq_rho σ hfix u a ?_⟩
  exact Units.ext rfl

theorem su2Emb_weyl_conj {p : ℕ} (hfix : ∀ u : Kˣ, u ^ p = 1 → σ (u : K) = u)
    (u : ↥(rootsOfUnity p K)) :
    su2Emb σ (wSL (fixF σ)) * rhoSU3 hfix u * (su2Emb σ (wSL (fixF σ)))⁻¹ = rhoSU3 hfix u⁻¹ := by
  have hu : (u : Kˣ) ^ p = 1 := (mem_rootsOfUnity p _).1 u.2
  have hσu := hfix _ hu
  let a : (fixF σ)ˣ := Units.mk0 ⟨((u : Kˣ) : K), hσu⟩ (fun h0 => (u : Kˣ).ne_zero (congrArg Subtype.val h0))
  have ha : upU σ a = (u : Kˣ) := Units.ext rfl
  have ha' : upU σ a⁻¹ = ((u⁻¹ : ↥(rootsOfUnity p K)) : Kˣ) := by
    rw [map_inv, ha]
    rfl
  rw [← su2Emb_diag2_eq_rho σ hfix u a ha, ← su2Emb_diag2_eq_rho σ hfix u⁻¹ a⁻¹ ha', ← map_inv,
    ← map_mul, ← map_mul, wSL_conj_diag2]

end CFSG.RankThree.PartOne.KFU
