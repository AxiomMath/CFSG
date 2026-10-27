module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6BridgeFactors

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge

open Matrix Module Representation
open CFSG.Theory.Representation CFSG.QuasithinUnique.Setup.X7
open CFSG.RankThree.GF2n.Stroth80.Sp6NoEmb (piRep piRep_apply)
open scoped TensorProduct

variable {F K k G : Type} [Field F] [Field K] [Field k]
  [Algebra F K] [Algebra F k] [Group G]

@[expose] def matrixRestrictRep {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : G →* Matrix ι ι K) : Representation F G (ι → K) where
  toFun g := ((A g).mulVecLin).restrictScalars F
  map_one' := by ext v i; simp
  map_mul' g h := by
    ext v i
    simp

@[expose] def matrixMapRep {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : G →* Matrix ι ι K) (φ : K →+* k) : Representation k G (ι → k) where
  toFun g := ((A g).map φ).mulVecLin
  map_one' := by ext v i; simp
  map_mul' g h := by
    ext v i
    simp [Matrix.map_mul]

theorem exists_finite_split_tensor [FiniteDimensional F K] [Algebra.IsSeparable F K]
    [IsAlgClosed k] : ∃ n : ℕ, Nonempty ((k ⊗[F] K) ≃ₐ[k] (Fin n → k)) := by
  have : Algebra.FormallyEtale F K := Algebra.FormallyEtale.of_isSeparable F K
  have : Algebra.FormallyEtale k (k ⊗[F] K) := inferInstance
  have : Module.Finite k (k ⊗[F] K) := inferInstance
  exact Algebra.IsFiniteSplit.nonempty_algEquiv_fun k (k ⊗[F] K)

section Split

variable {ι : Type} [Fintype ι] [DecidableEq ι] {m : ℕ}
  (e : (k ⊗[F] K) ≃ₐ[k] (Fin m → k))

@[expose] def splitEmbedding (j : Fin m) : K →+* k :=
  (Pi.evalRingHom (fun _ : Fin m => k) j).comp
    (e.toRingHom.comp Algebra.TensorProduct.includeRight.toRingHom)

@[expose] def splitVectorEquiv : (k ⊗[F] (ι → K)) ≃ₗ[k] (Fin m → ι → k) :=
  ((TensorProduct.piRight F k k (fun _ : ι => K)).trans
    (LinearEquiv.piCongrRight fun _ : ι => e.toLinearEquiv)).trans
    { toFun := fun v j i => v i j
      invFun := fun v i j => v j i
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

theorem splitVectorEquiv_tmul (a : k) (v : ι → K) (j : Fin m) (i : ι) :
    splitVectorEquiv e (a ⊗ₜ[F] v) j i = a * splitEmbedding e j (v i) := by
  change e ((TensorProduct.piRight F k k (fun _ : ι => K)) (a ⊗ₜ[F] v) i) j = _
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  dsimp only
  rw [show a ⊗ₜ[F] v i = a • ((1 : k) ⊗ₜ[F] v i) by
    rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]]
  change e.toLinearEquiv (a • ((1 : k) ⊗ₜ[F] v i)) j = _
  rw [e.toLinearEquiv.map_smul]
  rfl

@[expose] def splitMatrixRepEquiv (A : G →* Matrix ι ι K) :
    (extendScalars k (matrixRestrictRep (F := F) A)).Equiv
      (piRep fun j : Fin m => matrixMapRep A (splitEmbedding e j)) :=
  Representation.Equiv.mk (splitVectorEquiv e) fun g => by
    apply LinearMap.ext
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a v =>
      ext j i
      change splitVectorEquiv e
        ((extendScalars k (matrixRestrictRep (F := F) A) g) (a ⊗ₜ[F] v)) j i =
        ((A g).map (splitEmbedding e j) *ᵥ splitVectorEquiv e (a ⊗ₜ[F] v) j) i
      rw [extendScalars_apply, LinearMap.baseChange_tmul, splitVectorEquiv_tmul]
      simp only [matrixRestrictRep, MonoidHom.coe_mk, OneHom.coe_mk,
        LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
        map_sum, map_mul, Matrix.map_apply, splitVectorEquiv_tmul]
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun u _ => by ring
    | add u v hu hv => simpa using congrArg₂ (· + ·) hu hv

end Split

section Bounds

variable {ι : Type} [Fintype ι] [DecidableEq ι]

@[expose] def reindexMatrixRepEquiv {κ : Type} [Fintype κ] [DecidableEq κ]
    (A : G →* Matrix ι ι K) (φ : K →+* k) (e : κ ≃ ι) :
    (matrixMapRep A φ).Equiv (matrixMapRep
      { toFun := fun g => (A g).submatrix e e
        map_one' := by ext i j; simp [Matrix.one_apply, e.injective.eq_iff]
        map_mul' g h := by rw [map_mul, Matrix.submatrix_mul_equiv] } φ) :=
  Representation.Equiv.mk (LinearEquiv.funCongrLeft k k e) fun g => by
    apply LinearMap.ext
    intro v
    ext i
    change ((A g).map φ *ᵥ v) (e i) =
      (((A g).submatrix e e).map φ *ᵥ (v ∘ e)) i
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.submatrix_apply,
      Function.comp_apply]
    exact (Equiv.sum_comp e fun j => φ (A g (e i) j) * v j).symm

theorem factorsFinrankLe_matrixMapRep_of_lower_block_zero
    (A : G →* Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) (φ : K →+* k)
    (hA : ∀ g i j, A g (Sum.inr i) (Sum.inl j) = 0) :
    FactorsFinrankLe (matrixMapRep A φ) 2 := by
  let ρ := matrixMapRep A φ
  let N : Subrepresentation ρ :=
    { toSubmodule := LinearMap.ker (LinearMap.funLeft k k (Sum.inr : Fin 2 → Fin 2 ⊕ Fin 2))
      apply_mem_toSubmodule := by
        intro g v hv
        rw [LinearMap.mem_ker] at hv ⊢
        ext i
        have hv' : ∀ j : Fin 2, v (Sum.inr j) = 0 := fun j => congrFun hv j
        change ((A g).map φ *ᵥ v) (Sum.inr i) = 0
        simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, hA, hv'] }
  have hN : finrank k N.toSubmodule = 2 := by
    let b : (Fin 2 → k) ≃ₗ[k] N.toSubmodule :=
      { toFun := fun v => ⟨Sum.elim v 0, rfl⟩
        invFun := fun v => (v : Fin 2 ⊕ Fin 2 → k) ∘ Sum.inl
        left_inv := fun _ => rfl
        right_inv := by
          intro v
          apply Subtype.ext
          ext (i | i)
          · rfl
          · exact (congrFun (LinearMap.mem_ker.mp v.2) i).symm
        map_add' := fun _ _ => by ext (i | i) <;> simp
        map_smul' := fun _ _ => by ext (i | i) <;> simp }
    rw [← b.finrank_eq, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  have hQ : finrank k ((Fin 2 ⊕ Fin 2 → k) ⧸ N.toSubmodule) = 2 := by
    have hdim := Submodule.finrank_quotient_add_finrank N.toSubmodule
    simp only [hN, Module.finrank_fintype_fun_eq_card, Fintype.card_sum,
      Fintype.card_fin] at hdim
    omega
  exact factorsFinrankLe_of_exact (CFSG.QuasithinUnique.Setup.X7b.subIncl ρ N)
    (CFSG.QuasithinUnique.Setup.X7b.quotProj ρ N) N.toSubmodule.injective_subtype
    N.toSubmodule.mkQ_surjective (LinearMap.exact_subtype_mkQ N.toSubmodule)
    (factorsFinrankLe_of_finrank_le _ hN.le) (factorsFinrankLe_of_finrank_le _ hQ.le)

end Bounds

theorem factorsFinrankLe_extend_matrixRestrict
    [FiniteDimensional F K] [Algebra.IsSeparable F K] [IsAlgClosed k]
    {ι : Type} [Fintype ι] [DecidableEq ι] (A : G →* Matrix ι ι K) {n : ℕ}
    (h : ∀ φ : K →+* k, FactorsFinrankLe (matrixMapRep A φ) n) :
    FactorsFinrankLe (extendScalars k (matrixRestrictRep (F := F) A)) n := by
  obtain ⟨m, ⟨e⟩⟩ := exists_finite_split_tensor (F := F) (K := K) (k := k)
  apply factorsFinrankLe_of_equiv (splitMatrixRepEquiv e A).symm
  exact factorsFinrankLe_pi _ fun j => h (splitEmbedding e j)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5.Sp6Bridge
