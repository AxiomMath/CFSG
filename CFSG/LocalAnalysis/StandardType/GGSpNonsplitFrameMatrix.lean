module

public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrameInd
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionNonsplitRestMatrix

public section

open Polynomial Module Matrix

namespace CFSG.StandardType

namespace SpNS

section JForm

variable (n : ℕ) (K : Type) [Field K]

@[expose] def jMat : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K := fromBlocks 0 1 (-1) 0

@[expose] noncomputable def jForm : LinearMap.BilinForm K (Fin n ⊕ Fin n → K) :=
  Matrix.toBilin' (jMat n K)

variable {n K}

theorem jForm_apply (u v : Fin n ⊕ Fin n → K) : jForm n K u v = u ⬝ᵥ (jMat n K *ᵥ v) :=
  Matrix.toBilin'_apply' _ _ _

theorem jForm_isAlt : (jForm n K).IsAlt := fun v => by
  rw [jForm_apply, jMat, fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, zero_mulVec, one_mulVec, neg_mulVec, zero_add,
    add_zero, Pi.neg_apply, Function.comp_apply, mul_neg, Finset.sum_neg_distrib]
  rw [add_neg_eq_zero]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem jMat_mul_neg : jMat n K * -jMat n K = 1 := by
  rw [jMat, fromBlocks_neg, fromBlocks_multiply]
  simp only [neg_zero, neg_neg, Matrix.mul_zero, Matrix.mul_one, Matrix.mul_neg, zero_add,
    add_zero, fromBlocks_one]

theorem jForm_nondegenerate : (jForm n K).Nondegenerate :=
  Matrix.nondegenerate_toBilin'_iff.2 (Matrix.nondegenerate_iff_det_ne_zero.2
    (Matrix.det_ne_zero_of_right_inverse jMat_mul_neg))

theorem jForm_mulVec (M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) (u v : Fin n ⊕ Fin n → K) :
    jForm n K (M *ᵥ u) (M *ᵥ v) = Matrix.toBilin' (Mᵀ * jMat n K * M) u v := by
  rw [jForm, Matrix.toBilin'_apply', Matrix.toBilin'_apply', mulVec_mulVec, dotProduct_mulVec,
    ← vecMul_transpose, vecMul_vecMul, ← Matrix.mul_assoc, ← dotProduct_mulVec]

theorem transpose_mul_jMat_mul_eq {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : ∀ u v, jForm n K (M *ᵥ u) (M *ᵥ v) = jForm n K u v) : Mᵀ * jMat n K * M = jMat n K := by
  apply Matrix.toBilin'.injective
  refine LinearMap.ext₂ fun u v => ?_
  rw [← jForm_mulVec, h]
  rfl

theorem jForm_mulVec_of_eq {M : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K}
    (h : Mᵀ * jMat n K * M = jMat n K) (u v : Fin n ⊕ Fin n → K) :
    jForm n K (M *ᵥ u) (M *ᵥ v) = jForm n K u v := by
  rw [jForm_mulVec, h]
  rfl

end JForm

section Coords

variable {K : Type} [Field K] {D : Type} [AddCommGroup D] [Module K D] {e s r : ℕ}
  {ι κ : Type}

@[expose] noncomputable def dCoords (β : Basis (Fin e) K D) (eι : ι ≃ Fin s) (eκ : κ ≃ Fin r) :
    ((ι → D) × (κ → K)) ≃ₗ[K] ((Fin e × Fin s) ⊕ Fin r → K) where
  toFun uw := Sum.elim (fun p => β.repr (uw.1 (eι.symm p.2)) p.1) (fun j => uw.2 (eκ.symm j))
  map_add' uw uw' := by
    funext x
    rcases x with ⟨a, i⟩ | j <;> simp
  map_smul' c uw := by
    funext x
    rcases x with ⟨a, i⟩ | j <;> simp
  invFun v := (fun i => ∑ a, v (Sum.inl (a, eι i)) • β a, fun j => v (Sum.inr (eκ j)))
  left_inv uw := by
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp only [Sum.elim_inl, Equiv.symm_apply_apply]
      exact β.sum_repr (uw.1 i)
    · simp
  right_inv v := by
    funext x
    rcases x with ⟨a, i⟩ | j
    · simp only [Sum.elim_inl, Equiv.apply_symm_apply, Basis.repr_sum_self]
    · simp

theorem dCoords_apply_inl (β : Basis (Fin e) K D) (eι : ι ≃ Fin s) (eκ : κ ≃ Fin r)
    (u : ι → D) (w : κ → K) (a : Fin e) (i : Fin s) :
    dCoords β eι eκ (u, w) (Sum.inl (a, i)) = β.repr (u (eι.symm i)) a := rfl

theorem dCoords_apply_inr (β : Basis (Fin e) K D) (eι : ι ≃ Fin s) (eκ : κ ≃ Fin r)
    (u : ι → D) (w : κ → K) (j : Fin r) :
    dCoords β eι eκ (u, w) (Sum.inr j) = w (eκ.symm j) := rfl

theorem dCoords_mul (β : Basis (Fin e) K D) (eι : ι ≃ Fin s) (eκ : κ ≃ Fin r) (c : D →ₗ[K] D)
    (k : ι → ℕ) (u : ι → D) (w : κ → K) :
    dCoords β eι eκ (fun i => (c ^ k i) (u i), w) =
      SLNS.nsCore (r := r) (LinearMap.toMatrix β β c) (k ∘ eι.symm) *ᵥ dCoords β eι eκ (u, w) := by
  funext x
  rcases x with ⟨a, i⟩ | j
  · rw [dCoords_apply_inl, SLNS.nsCore, fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply,
      zero_mulVec, Pi.zero_apply, add_zero, NSFrame.blockDiagonal_mulVec_apply,
      Function.comp_apply, LinearMap.toMatrix_pow, ← LinearMap.toMatrix_mulVec_repr β β]
    rfl
  · rw [dCoords_apply_inr, SLNS.nsCore, fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply,
      zero_mulVec, Pi.zero_apply, zero_add, one_mulVec]
    rfl

end Coords

section FrameMatrix

variable {K : Type} [Field K] {ℓ : ℕ} {D : Type} [AddCommGroup D] [Module K D]
  [FiniteDimensional K D] [Nontrivial D] {c : D →ₗ[K] D} {e n : ℕ}

theorem exists_spFrame_matrix (hD : SpBlockExists K ℓ D c) (hℓ : 1 ≤ ℓ) (β : Basis (Fin e) K D)
    (S : Set (Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) (hSc : ∀ x ∈ S, ∀ y ∈ S, Commute x y)
    (hSp : ∀ x ∈ S, x ^ ℓ = 1) (hSJ : ∀ x ∈ S, xᵀ * jMat n K * x = jMat n K) :
    ∃ (s r : ℕ) (ε : Fin n ⊕ Fin n ≃ (Fin e × Fin s) ⊕ Fin r) (A₀ : GL (Fin n ⊕ Fin n) K),
      (∀ x ∈ S, ∃ k : Fin s → ℕ, x = (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (SLNS.nsCore (LinearMap.toMatrix β β c) k).submatrix ε ε *
          ((A₀⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) ∧
      ∀ k : Fin s → ℕ, ((A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (SLNS.nsCore (LinearMap.toMatrix β β c) k).submatrix ε ε *
          ((A₀⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K))ᵀ *
        jMat n K * ((A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) *
        (SLNS.nsCore (LinearMap.toMatrix β β c) k).submatrix ε ε *
          ((A₀⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)) =
        jMat n K := by
  classical
  obtain ⟨ι, κ, _, _, Φ, hΦS, hΦB⟩ := exists_spFrame hD hℓ (jForm n K)
    (Matrix.toLinAlgEquiv' '' S) jForm_isAlt jForm_nondegenerate
    (by
      rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      exact (hSc x hx y hy).map _)
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hSp x hx, map_one])
    (by
      rintro _ ⟨x, hx, rfl⟩ u w
      rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLinAlgEquiv'_apply]
      exact jForm_mulVec_of_eq (hSJ x hx) u w)
  set eι := Fintype.equivFin ι with heι
  set eκ := Fintype.equivFin κ with heκ
  set Ψ := (dCoords β eι eκ).symm.trans Φ with hΨ
  have hcard : Fintype.card ((Fin e × Fin (Fintype.card ι)) ⊕ Fin (Fintype.card κ)) =
      Fintype.card (Fin n ⊕ Fin n) := by
    have h1 := Ψ.finrank_eq
    rwa [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h1
  set ε := (Fintype.equivOfCardEq hcard).symm with hε
  set Ψ' := (LinearEquiv.funCongrLeft K K ε).symm.trans Ψ with hΨ'
  set Q := LinearMap.toMatrix' (Ψ' : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K)) with hQ
  set Q' := LinearMap.toMatrix' (Ψ'.symm : (Fin n ⊕ Fin n → K) →ₗ[K] (Fin n ⊕ Fin n → K))
    with hQ'
  have hQQ' : Q * Q' = 1 := by
    rw [hQ, hQ', ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.symm_trans_self,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  have hQ'Q : Q' * Q = 1 := by
    rw [hQ, hQ', ← LinearMap.toMatrix'_comp, LinearEquiv.comp_coe, LinearEquiv.self_trans_symm,
      LinearEquiv.refl_toLinearMap, LinearMap.toMatrix'_id]
  set A₀ : GL (Fin n ⊕ Fin n) K := ⟨Q, Q', hQQ', hQ'Q⟩ with hA₀
  have hA₀v : (A₀ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Q := rfl
  have hA₀i : ((A₀⁻¹ : GL (Fin n ⊕ Fin n) K) : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K) = Q' :=
    rfl
  have hΨ'symm : ∀ dw, Ψ'.symm (Φ dw) = dCoords β eι eκ dw ∘ ε := by
    intro dw
    funext x
    simp [hΨ', hΨ, LinearEquiv.funCongrLeft_apply]
  have hΨ'app : ∀ dw, Ψ' (dCoords β eι eκ dw ∘ ε) = Φ dw := by
    intro dw
    rw [← hΨ'symm, LinearEquiv.apply_symm_apply]
  have hkey : ∀ (k : ι → ℕ) (d : ι → D) (w : κ → K),
      (Q * (SLNS.nsCore (LinearMap.toMatrix β β c) (k ∘ eι.symm)).submatrix ε ε * Q') *ᵥ
        Φ (d, w) = Φ (fun i => (c ^ k i) (d i), w) := by
    intro k d w
    have h1 : Q' *ᵥ Φ (d, w) = dCoords β eι eκ (d, w) ∘ ε := by
      rw [hQ', LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe, hΨ'symm]
    have h2 : ∀ z, Q *ᵥ z = Ψ' z := fun z => by
      rw [hQ, LinearMap.toMatrix'_mulVec, LinearEquiv.coe_coe]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, submatrix_mulVec_equiv,
      Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id, ← dCoords_mul, h2, hΨ'app]
  refine ⟨Fintype.card ι, Fintype.card κ, ε, A₀, fun x hx => ?_, fun k => ?_⟩
  · obtain ⟨k, hk⟩ := hΦS (Matrix.toLinAlgEquiv' x) ⟨x, hx, rfl⟩
    refine ⟨k ∘ eι.symm, ?_⟩
    rw [hA₀v, hA₀i]
    refine Matrix.toLin'.injective (LinearMap.ext fun v => ?_)
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply]
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective v
    rw [hkey]
    have h1 := hk d w
    rw [Matrix.toLinAlgEquiv'_apply] at h1
    exact h1
  · apply transpose_mul_jMat_mul_eq
    intro u v
    obtain ⟨⟨d, w⟩, rfl⟩ := Φ.surjective u
    obtain ⟨⟨d', w'⟩, rfl⟩ := Φ.surjective v
    have e1 : k = (k ∘ eι) ∘ eι.symm := by
      funext i
      simp
    rw [hA₀v, hA₀i, e1, hkey, hkey]
    exact hΦB (k ∘ eι) d d' w w'

end FrameMatrix

end SpNS

end CFSG.StandardType
