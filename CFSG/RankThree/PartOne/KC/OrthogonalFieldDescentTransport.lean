module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSimilarity

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Matrix Module CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField

variable {K : Type} [Field K] {d : ℕ}

theorem inr_mem_similarityPairs (Q' : QuadraticForm K (Fin d → K)) (σ : K ≃+* K)
    (h : ∀ v, Q' (fun i => σ (v i)) = σ (Q' v)) :
    (SemidirectProduct.inr σ : coordinateSemilinearGroup d K) ∈ similarityPairs Q' := by
  refine ⟨1, fun v => ?_⟩
  have hv : coordinateSemilinearMap (SemidirectProduct.inr σ : coordinateSemilinearGroup d K) v =
      fun i => σ (v i) := by
    rw [coordinateSemilinearMap_apply]
    simp
  rw [hv, h]
  simp

theorem exists_extension_matrix {ι : Type} [Fintype ι] (e : ι ≃ Fin d)
    (U : coordinateSemilinearGroup d K) (bK : Basis ι K (Fin d → K))
    (hfix : ∀ a, coordinateSemilinearMap U (bK a) = bK a) :
    ∃ S : GL (Fin d) K, (∀ v, (S : Matrix (Fin d) (Fin d) K) *ᵥ v =
        fun j => bK.equivFun v (e.symm j)) ∧
      S * U.left = glFieldAut (Fin d) K U.right S := by
  classical
  let L : (Fin d → K) ≃ₗ[K] (Fin d → K) :=
    bK.equivFun.trans (LinearEquiv.funCongrLeft K K e.symm)
  have hL : ∀ v, L v = fun j => bK.equivFun v (e.symm j) := fun v => rfl
  refine ⟨matrixLinearIso.symm L, ?_, ?_⟩
  · intro v
    have h : matrixLinearIso (matrixLinearIso.symm L) v = L v := by
      rw [MulEquiv.apply_symm_apply]
    rw [hL] at h
    exact h
  · set S : GL (Fin d) K := matrixLinearIso.symm L with hSdef
    have hS : ∀ v, (S : Matrix (Fin d) (Fin d) K) *ᵥ v = L v := fun v => by
      have h : matrixLinearIso S v = L v := by rw [hSdef, MulEquiv.apply_symm_apply]
      exact h
    have hint : ∀ v, L (coordinateSemilinearMap U v) = fun j => U.right (L v j) := by
      intro v
      have hv := bK.sum_equivFun v
      set c := bK.equivFun v with hc
      have h1 : coordinateSemilinearMap U v = ∑ a, U.right (c a) • bK a := by
        conv_lhs => rw [← hv]
        rw [map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [coordinateSemilinearMap_smul, hfix]
      rw [h1, hL]
      funext j
      have h2 := bK.repr_sum_self (fun a => U.right (c a))
      simp only [Basis.equivFun_apply, h2]
      rfl
    have hmat : ∀ u : Fin d → K,
        ((S * U.left : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u =
          ((glFieldAut (Fin d) K U.right S : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ u := by
      intro u
      set v : Fin d → K := fun i => U.right.symm (u i) with hvdef
      have hu : (fun i => U.right (v i)) = u := funext fun i => U.right.apply_symm_apply (u i)
      rw [← hu]
      have h1 : ((S * U.left : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
          (fun i => U.right (v i)) = L (coordinateSemilinearMap U v) := by
        rw [Units.val_mul, ← Matrix.mulVec_mulVec, ← coordinateSemilinearMap_apply, hS]
      have h2 : ((glFieldAut (Fin d) K U.right S : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *ᵥ
          (fun i => U.right (v i)) = fun j => U.right (L v j) := by
        funext j
        rw [← hS v]
        exact (U.right.toRingHom.map_mulVec (S : Matrix (Fin d) (Fin d) K) v j).symm
      rw [h1, h2, hint]
    exact Units.ext (Matrix.ext_iff_mulVec.mpr hmat)

theorem equivFun_coe {ι : Type} [Fintype ι] (U : coordinateSemilinearGroup d K)
    (bk : Basis ι (fixedField U) (fixedSpace U)) (bK : Basis ι K (Fin d → K))
    (hb : ∀ a, bK a = ((bk a : fixedSpace U) : Fin d → K)) (w : fixedSpace U) (a : ι) :
    bK.equivFun (w : Fin d → K) a = ((bk.equivFun w a : fixedField U) : K) := by
  have hw := bk.sum_equivFun w
  have key : ∀ (c : fixedField U) (x : fixedSpace U),
      ((c • x : fixedSpace U) : Fin d → K) = (c : K) • (x : Fin d → K) := fun c x => rfl
  have h1 : (w : Fin d → K) = ∑ a, ((bk.equivFun w a : fixedField U) : K) • bK a := by
    have h3 := congrArg (fun z : fixedSpace U => (z : Fin d → K)) hw.symm
    simp only [Submodule.coe_sum, key] at h3
    rw [h3]
    exact Finset.sum_congr rfl fun a _ => by rw [hb]
  have h2 := bK.repr_sum_self (fun a => ((bk.equivFun w a : fixedField U) : K))
  rw [h1, Basis.equivFun_apply]
  exact congrFun h2 a

theorem transports_of_basis {ι : Type} [Fintype ι] (e : ι ≃ Fin d)
    (Q Q' : QuadraticForm K (Fin d → K)) (U : similarityPairs Q)
    (bk : Basis ι (fixedField U.val) (fixedSpace U.val)) (bK : Basis ι K (Fin d → K))
    (hb : ∀ a, bK a = ((bk a : fixedSpace U.val) : Fin d → K)) (ν : Kˣ)
    (hν : ∀ v, Q' (fun j => bK.equivFun v (e.symm j)) = ν * Q v)
    (g' : similarityPairs Q') (hl : g'.val.left = 1) (hr : g'.val.right = U.val.right) :
    TransportsToCoordinateField e Q Q' U bk.equivFun := by
  have hfix : ∀ a, coordinateSemilinearMap U.val (bK a) = bK a := fun a => by
    rw [hb]
    exact (bk a).2
  obtain ⟨S, hS, hSU⟩ := exists_extension_matrix e U.val bK hfix
  have hSq : ∀ v, Q' (matrixLinearIso S v) = ν * Q v := fun v => by
    have h : matrixLinearIso S v = fun j => bK.equivFun v (e.symm j) := hS v
    rw [h]
    exact hν v
  refine ⟨S, ν, fun v => ?_, fun w => ?_, hSU, matrixProjectiveSimilarityEquiv Q Q' S ν hSq,
    fun A => ?_, g', hl, hr, ?_⟩
  · rw [hS v]
    exact hν v
  · rw [hS (w : Fin d → K)]
    funext j
    exact equivFun_coe U.val bk bK hb w (e.symm j)
  · obtain ⟨B, hB⟩ := exists_conj_mem_matrixDerived Q Q' S ν hSq A
    exact ⟨B, hB, matrixProjectiveSimilarityEquiv_mk Q Q' S ν hSq A B hB⟩
  · intro x
    exact matrixProjectiveSimilarityEquiv_conj Q Q' S ν hSq U g' hl hr hSU x

end CFSG.RankThree.PartOne.KCOrthogonalDescent
