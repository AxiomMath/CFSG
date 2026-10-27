module

public import CFSG.RankThree.GF2n.Stroth80.Sec3Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.Open.StatedAPI Matrix

variable {G : Type} [Group G] {K : Type} [Field K]

@[expose] def reindexGL {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (σ : ι ≃ ι') : GL ι K ≃* GL ι' K :=
  Units.mapEquiv (Matrix.reindexAlgEquiv K K σ).toMulEquiv

theorem coe_reindexGL {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (σ : ι ≃ ι') (A : GL ι K) :
    ((reindexGL σ A : GL ι' K) : Matrix ι' ι' K) =
      (A : Matrix ι ι K).submatrix σ.symm σ.symm :=
  rfl

theorem NaturalRep.reindex {ι ι' : Type} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (σ : ι ≃ ι') {X : Subgroup (GL ι K)} {R V Z N : Subgroup G}
    (h : NaturalRep (ι := ι) K X R V Z N) :
    NaturalRep (ι := ι') K (X.map (reindexGL σ).toMonoidHom) R V Z N := by
  obtain ⟨φ, hrange, hker, hnorm, hZ, ψ, hψ⟩ := h
  refine ⟨(reindexGL σ).toMonoidHom.comp φ, ?_, ?_, hnorm, hZ,
    ψ.trans (LinearEquiv.funCongrLeft K K σ.symm).toAddEquiv.toMultiplicative, ?_⟩
  · rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map, hrange]
  · exact (MonoidHom.ker_mulEquiv_comp φ (reindexGL σ)).trans hker
  · intro s v w hw
    have h1 := hψ s v w hw
    show (Multiplicative.toAdd (ψ (QuotientGroup.mk w))) ∘ σ.symm =
      ((((reindexGL σ).toMonoidHom.comp φ) s : GL ι' K) : Matrix ι' ι' K) *ᵥ
        ((Multiplicative.toAdd (ψ (QuotientGroup.mk v))) ∘ σ.symm)
    rw [h1]
    show _ = ((φ s : Matrix ι ι K).submatrix σ.symm σ.symm) *ᵥ _
    rw [submatrix_mulVec_equiv]
    congr 2
    funext i
    simp

@[expose] def sumFinTwo : Fin 1 ⊕ Fin 1 ≃ Fin 2 := finSumFinEquiv

theorem transpose_mul_J_mul (A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) :
    Aᵀ * (fromBlocks 0 1 (-1) 0 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) * A =
      A.det • (fromBlocks 0 1 (-1) 0 : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) := by
  have hdet : A.det = A (Sum.inl 0) (Sum.inl 0) * A (Sum.inr 0) (Sum.inr 0) -
      A (Sum.inl 0) (Sum.inr 0) * A (Sum.inr 0) (Sum.inl 0) := by
    rw [← Matrix.det_reindex_self finSumFinEquiv A, Matrix.det_fin_two]
    rfl
  rw [hdet]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.one_apply, Fin.fin_one_eq_zero] <;> ring

theorem map_reindexGL_statedSp_one :
    (StatedSp 1 K).map (reindexGL sumFinTwo).toMonoidHom = StatedSL 2 K := by
  ext B
  rw [Subgroup.mem_map_equiv, mem_statedSp_iff, mem_statedSL_iff]
  set A : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K := (((reindexGL sumFinTwo).symm B : GL _ K) :
    Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) K) with hA
  have hdet : A.det = (B : Matrix (Fin 2) (Fin 2) K).det := by
    rw [hA]
    exact Matrix.det_reindex_self sumFinTwo.symm _
  rw [transpose_mul_J_mul, ← hdet]
  constructor
  · intro h
    have := congrFun (congrFun h (Sum.inl 0)) (Sum.inr 0)
    simpa using this
  · intro h
    rw [h, one_smul]

theorem NaturalRep.sp_one_to_sl_two {R V Z N : Subgroup G}
    (h : NaturalRep (ι := Fin 1 ⊕ Fin 1) K (StatedSp 1 K) R V Z N) :
    NaturalRep (ι := Fin 2) K (StatedSL 2 K) R V Z N := by
  have := NaturalRep.reindex sumFinTwo h
  rwa [map_reindexGL_statedSp_one] at this

end CFSG.RankThree.GF2n.Stroth80
