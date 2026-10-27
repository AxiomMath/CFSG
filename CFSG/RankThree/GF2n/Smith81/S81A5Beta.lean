module

public import CFSG.RankThree.GF2n.Smith81.S81A5Basic
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing

public section

namespace CFSG.RankThree.GF2n.Smith81.A5Cube

open Matrix exteriorPower

variable {K : Type*} [Field K]

@[expose] noncomputable def beta (K : Type*) [Field K] : Cube K →ₗ[K] Cube K →ₗ[K] K :=
  (exteriorPower.wedge K (Fin 6 → K) 3 3).compr₂
    (exteriorPower.topEquiv (Pi.basisFun K (Fin 6)) : _ →ₗ[K] K)

theorem beta1_card (I : Set.powersetCard (Fin 6) 3) : I.val.card = 3 := I.prop

theorem beta_cubeBasis_of_not_disjoint {I J : Set.powersetCard (Fin 6) 3}
    (h : ¬ Disjoint I.val J.val) : beta K (cubeBasis K I) (cubeBasis K J) = 0 := by
  have hw : exteriorPower.wedge K (Fin 6 → K) 3 3 (cubeBasis K I) (cubeBasis K J) = 0 := by
    unfold cubeBasis
    exact exteriorPower.wedge_apply_of_not_disjoint (Pi.basisFun K (Fin 6)) h
  show exteriorPower.topEquiv (Pi.basisFun K (Fin 6))
    (exteriorPower.wedge K (Fin 6 → K) 3 3 (cubeBasis K I) (cubeBasis K J)) = 0
  rw [hw, map_zero]

theorem beta_cubeBasis_ne_zero_of_disjoint {I J : Set.powersetCard (Fin 6) 3}
    (h : Disjoint I.val J.val) : beta K (cubeBasis K I) (cubeBasis K J) ≠ 0 := by
  have hcard : (I.val ∪ J.val).card = Fintype.card (Fin 6) := by
    simp [Finset.card_union_of_disjoint h, beta1_card I, beta1_card J]
  obtain ⟨tp, htp⟩ : ∃ tp : Set.powersetCard (Fin 6) 6, tp.val = Finset.univ :=
    ⟨⟨Finset.univ, (by simp : (Finset.univ : Finset (Fin 6)).card = 6)⟩, rfl⟩
  have hIJ : I.val ∪ J.val = tp.val := by
    rw [htp]
    exact Finset.eq_univ_of_card _ hcard
  have hk : (3 : ℕ) + 3 = Fintype.card (Fin 6) := by simp
  have h1 := exteriorPower.wedge_apply_of_disjoint (Pi.basisFun K (Fin 6)) hk h
  have hw : exteriorPower.wedge K (Fin 6 → K) 3 3 (cubeBasis K I) (cubeBasis K J) =
      Set.powersetCard.sign I • (Pi.basisFun K (Fin 6)).exteriorPower 6 tp := by
    unfold cubeBasis
    apply Subtype.ext
    rw [SetLike.val_smul_of_tower, h1, hIJ, ExteriorAlgebra.basis_eq_coe_basis]
  have hX : exteriorPower.topEquiv (Pi.basisFun K (Fin 6))
      ((Pi.basisFun K (Fin 6)).exteriorPower 6 tp) ≠ 0 :=
    (exteriorPower.topEquiv (Pi.basisFun K (Fin 6))).map_ne_zero_iff.mpr
      (((Pi.basisFun K (Fin 6)).exteriorPower 6).ne_zero tp)
  show exteriorPower.topEquiv (Pi.basisFun K (Fin 6))
    (exteriorPower.wedge K (Fin 6 → K) 3 3 (cubeBasis K I) (cubeBasis K J)) ≠ 0
  rw [hw, map_zsmul_unit]
  rcases Int.units_eq_one_or (Set.powersetCard.sign I) with h' | h' <;> rw [h'] <;> simpa using hX

@[expose] def cmpl (I : Set.powersetCard (Fin 6) 3) : Set.powersetCard (Fin 6) 3 :=
  ⟨Finset.univ \ I.val, by
    show (Finset.univ \ I.val).card = 3
    rw [Finset.card_univ_diff, Fintype.card_fin, I.prop]⟩

theorem disjoint_cmpl (I : Set.powersetCard (Fin 6) 3) : Disjoint I.val (cmpl I).val := by
  show Disjoint I.val (Finset.univ \ I.val)
  exact Finset.disjoint_sdiff

theorem eq_of_disjoint_cmpl {I I' : Set.powersetCard (Fin 6) 3} (h : Disjoint I'.val (cmpl I).val) :
    I' = I := by
  apply Subtype.ext
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    by_contra hxI
    exact Finset.disjoint_left.mp h hx
      (show x ∈ Finset.univ \ I.val from Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxI⟩)
  · exact le_of_eq (by rw [beta1_card I, beta1_card I'])

theorem disjoint_cmpl_left (I : Set.powersetCard (Fin 6) 3) : Disjoint (cmpl I).val I.val :=
  (disjoint_cmpl I).symm

theorem beta1_expand_left (ξ η : Cube K) :
    beta K ξ η = ∑ I : Set.powersetCard (Fin 6) 3, coord K ξ I * beta K (cubeBasis K I) η := by
  conv_lhs => rw [← (cubeBasis K).sum_repr ξ]
  simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, coord]

theorem beta1_expand_right (ξ η : Cube K) :
    beta K ξ η = ∑ J : Set.powersetCard (Fin 6) 3, coord K η J * beta K ξ (cubeBasis K J) := by
  conv_lhs => rw [← (cubeBasis K).sum_repr η]
  simp only [map_sum, map_smul, smul_eq_mul, coord]

theorem beta_apply_cubeBasis_cmpl (ξ : Cube K) (I : Set.powersetCard (Fin 6) 3) :
    beta K ξ (cubeBasis K (cmpl I)) = coord K ξ I * beta K (cubeBasis K I) (cubeBasis K (cmpl I)) := by
  rw [beta1_expand_left ξ (cubeBasis K (cmpl I)), Finset.sum_eq_single I]
  · intro I' _ hne
    rw [beta_cubeBasis_of_not_disjoint (I := I') (J := cmpl I)
      (fun hd => hne (eq_of_disjoint_cmpl hd)), mul_zero]
  · intro hI
    exact absurd (Finset.mem_univ I) hI

theorem beta_cubeBasis_cmpl_apply (η : Cube K) (I : Set.powersetCard (Fin 6) 3) :
    beta K (cubeBasis K (cmpl I)) η = coord K η I * beta K (cubeBasis K (cmpl I)) (cubeBasis K I) := by
  rw [beta1_expand_right (cubeBasis K (cmpl I)) η, Finset.sum_eq_single I]
  · intro J _ hne
    rw [beta_cubeBasis_of_not_disjoint (I := cmpl I) (J := J)
      (fun hd => hne (eq_of_disjoint_cmpl hd.symm)), mul_zero]
  · intro hI
    exact absurd (Finset.mem_univ I) hI

theorem beta_ιMulti (v w : Fin 3 → Fin 6 → K) :
    beta K (ιMulti K 3 v) (ιMulti K 3 w) = (Matrix.of (Fin.append v w)).det := by
  have hwedge : exteriorPower.wedge K (Fin 6 → K) 3 3 (ιMulti K 3 v) (ιMulti K 3 w) =
      ιMulti K 6 (Fin.append v w) := by
    apply Subtype.ext
    simp only [DirectSum.gMulLHom_apply_apply, SetLike.coe_gMul,
      exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_mul_ιMulti]
  have hdet : ∀ u : Fin 6 → Fin 6 → K, (Pi.basisFun K (Fin 6)).det u = (Matrix.of u).det := by
    intro u
    rw [Module.Basis.det_apply, ← Matrix.det_transpose (Matrix.of u)]
    congr 1
  rw [beta, LinearMap.compr₂_apply, hwedge, LinearEquiv.coe_coe,
    exteriorPower.topEquiv_apply_ιMulti]
  exact hdet _

theorem beta_rho (g : GL (Fin 6) K) (ξ η : Cube K) :
    beta K (rho K g ξ) (rho K g η) = (g : Matrix (Fin 6) (Fin 6) K).det * beta K ξ η := by
  have hrows : ∀ u : Fin 6 → Fin 6 → K,
      (Matrix.of fun i => (g : Matrix (Fin 6) (Fin 6) K).mulVec (u i)).det =
        (g : Matrix (Fin 6) (Fin 6) K).det * (Matrix.of u).det := by
    intro u
    have h : (Matrix.of fun i => (g : Matrix (Fin 6) (Fin 6) K).mulVec (u i)) =
        Matrix.of u * (g : Matrix (Fin 6) (Fin 6) K)ᵀ := by
      ext i j
      simp [Matrix.mulVec, dotProduct, Matrix.mul_apply, mul_comm]
    rw [h, Matrix.det_mul, Matrix.det_transpose, mul_comm]
  have pure : ∀ v w : Fin 3 → Fin 6 → K,
      beta K (rho K g (ιMulti K 3 v)) (rho K g (ιMulti K 3 w)) =
        (g : Matrix (Fin 6) (Fin 6) K).det * beta K (ιMulti K 3 v) (ιMulti K 3 w) := by
    intro v w
    have hA : Fin.append (fun i => (g : Matrix (Fin 6) (Fin 6) K).mulVec (v i))
        (fun i => (g : Matrix (Fin 6) (Fin 6) K).mulVec (w i)) =
        fun i => (g : Matrix (Fin 6) (Fin 6) K).mulVec (Fin.append v w i) := by
      funext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · simp only [Fin.append_left]
      · simp only [Fin.append_right]
    rw [rho_ιMulti, rho_ιMulti, beta_ιMulti, beta_ιMulti, hA, hrows]
  have key : (beta K).compl₁₂ (rho K g) (rho K g) =
      (g : Matrix (Fin 6) (Fin 6) K).det • beta K := by
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span K 3 (Fin 6 → K)) fun v => ?_
    refine LinearMap.ext_on_range (exteriorPower.ιMulti_span K 3 (Fin 6 → K)) fun w => ?_
    simp only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul]
    exact pure v w
  have h := congrArg (fun F : Cube K →ₗ[K] Cube K →ₗ[K] K => F ξ η) key
  simpa only [LinearMap.compl₁₂_apply, LinearMap.smul_apply, smul_eq_mul] using h

end CFSG.RankThree.GF2n.Smith81.A5Cube
