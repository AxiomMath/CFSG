module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmPlusSemi
public import CFSG.LieType.Universal.Spin.Action
public import CFSG.LieType.Universal.Spin.Forms
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlus
import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaPlusOTwo
import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataConjugation

public section

namespace CFSG.StandardType.KGOm

open CFSG.LieType.Universal.Spin
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.RankThree.PartOne.AUTSL

variable {K : Type} [Field K] {n : ℕ}

section Reindex

private theorem reindex_coordinateFieldMap (σ : K ≃+* K) (y : Fin n ⊕ Fin n → K) :
    reindexVectorEquiv (plusIndexEquiv n) (fun m => σ (y m)) =
      coordinateFieldMap (2 * n) σ (reindexVectorEquiv (plusIndexEquiv n) y) := by
  funext i
  rfl

private theorem reindex_vPlusS [Finite K] [CharP K 2] (hn : 1 ≤ n) :
    reindexVectorEquiv (K := K) (plusIndexEquiv n) (vPlusS (K := K) hn) =
      AutOm.vPlus (K := K) hn := by
  rw [AutOm.vPlus, AutOm.plusUnitVector_eq, vPlusS, map_add]

private theorem reindex_plusSemi_false (hn : 1 ≤ n) (σ : K ≃+* K)
    (y : Fin n ⊕ Fin n → K) :
    reindexVectorEquiv (plusIndexEquiv n) (plusSemi hn false σ y) =
      coordinateSemilinearMap (AutOm.gField (n := n) σ).val
        (reindexVectorEquiv (plusIndexEquiv n) y) := by
  rw [plusSemi_false, AutOm.coordinateSemilinearMap_fieldPair]
  exact reindex_coordinateFieldMap σ y

private theorem reindex_plusSemi_true [Finite K] [CharP K 2] (hn : 1 ≤ n) (σ : K ≃+* K)
    (y : Fin n ⊕ Fin n → K) :
    reindexVectorEquiv (plusIndexEquiv n) (plusSemi hn true σ y) =
      coordinateSemilinearMap (AutOm.gRefl hn * AutOm.gField (n := n) σ).val
        (reindexVectorEquiv (plusIndexEquiv n) y) := by
  rw [plusSemi_true, map_add, map_smul, AutOm.gReflField_map, AutOm.reflMat_vPlus_mulVec,
    ← AutOm.polar_reindex_plus (n := n) (vPlusS hn) (fun m => σ (y m)),
    reindex_coordinateFieldMap σ y, reindex_vPlusS hn]

end Reindex

section Transport

private theorem spinAction_plusSemi_of_semilinear (hn : 1 ≤ n)
    (πe : spinGroup (quadPlus n K) ≃* matrixDerived (coordinateQuadPlus n K))
    (hπe : ∀ (x : spinGroup (quadPlus n K)) (v : Fin n ⊕ Fin n → K),
      Matrix.mulVec ((πe x : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K)
          (reindexVectorEquiv (plusIndexEquiv n) v) =
        reindexVectorEquiv (plusIndexEquiv n) (spinAction (quadPlus n K) x v))
    (g : similarityPairs (coordinateQuadPlus n K)) (ε : Bool) (τ : K ≃+* K)
    (hco : ∀ z : Fin n ⊕ Fin n → K,
      reindexVectorEquiv (plusIndexEquiv n) (plusSemi hn ε τ z) =
        coordinateSemilinearMap g.val (reindexVectorEquiv (plusIndexEquiv n) z))
    (k : spinGroup (quadPlus n K)) (y : Fin n ⊕ Fin n → K) :
    spinAction (quadPlus n K)
        (πe.symm (conjAct (coordinateQuadPlus n K) g (πe k))) (plusSemi hn ε τ y) =
      plusSemi hn ε τ (spinAction (quadPlus n K) k y) := by
  apply (reindexVectorEquiv (plusIndexEquiv n)).injective
  rw [hco (spinAction (quadPlus n K) k y), ← hπe k y,
    ← hπe (πe.symm (conjAct (coordinateQuadPlus n K) g (πe k))) (plusSemi hn ε τ y),
    MulEquiv.apply_symm_apply, hco y]
  have hval : ((↑(((conjAct (coordinateQuadPlus n K)) g (πe k)) :
      GL (Fin (2 * n)) K))) =
      matrixConjugation g.val ((πe k).val) := by
    rw [conjAct_apply, matrixDerivedConjugation_val, matrixConjugation_apply]
  rw [show Matrix.mulVec ((↑(((conjAct (coordinateQuadPlus n K)) g (πe k)) :
        GL (Fin (2 * n)) K)) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
        (coordinateSemilinearMap g.val (reindexVectorEquiv (plusIndexEquiv n) y)) =
      coordinateSemilinearMap g.val (Matrix.mulVec ((πe k : GL (Fin (2 * n)) K) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K) (reindexVectorEquiv (plusIndexEquiv n) y))
    from by
      rw [hval]
      simpa only [matrixLinearEquiv_apply, AddEquiv.symm_apply_apply] using
        matrixConjugation_vector g.val (πe k).val
          (coordinateSemilinearMap g.val (reindexVectorEquiv (plusIndexEquiv n) y))]

end Transport

theorem exists_conj_plusSemi_of_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn5 : 5 ≤ n) {G : Type*} [Group G] {ψ : spinGroup (quadPlus n K) →* G}
    (hψ : Function.Injective ψ) {a : G} (ha : a ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (γ : spinGroup (quadPlus n K))
      (c : spinGroup (quadPlus n K) →* spinGroup (quadPlus n K)) (ε : Bool) (τ : K ≃+* K),
      (∀ k, a * ψ k * a⁻¹ = ψ (γ * c k * γ⁻¹)) ∧
      ∀ (k : spinGroup (quadPlus n K)) (y : Fin n ⊕ Fin n → K),
        spinAction (quadPlus n K) (c k) (plusSemi (by omega) ε τ y) =
          plusSemi (by omega) ε τ (spinAction (quadPlus n K) k y) := by
  classical
  have hn : 3 ≤ n := by omega
  have hn1 : 1 ≤ n := by omega
  let πe : spinGroup (quadPlus n K) ≃* matrixDerived (coordinateQuadPlus n K) :=
    MulEquiv.ofBijective (AutOm.spinModelPlus hn)
      ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩
  have hπe : ∀ (x : spinGroup (quadPlus n K)) (v : Fin n ⊕ Fin n → K),
      Matrix.mulVec ((πe x : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K)
          (reindexVectorEquiv (plusIndexEquiv n) v) =
        reindexVectorEquiv (plusIndexEquiv n) (spinAction (quadPlus n K) x v) :=
    fun x v => AutOm.spinModelPlus_mulVec hn x v
  let Θ : matrixDerived (coordinateQuadPlus n K) ≃* ψ.range :=
    πe.symm.trans (MonoidHom.ofInjective hψ)
  let cAut : MulAut ψ.range := CFSG.LocalAnalysis.ComponentInitial.conjAut ψ.range ha
  let α : MulAut (matrixDerived (coordinateQuadPlus n K)) := (Θ.trans cAut).trans Θ.symm
  obtain ⟨ι, hι, c₀, hc₀, hα⟩ := AutOm.exists_inner_mul_plusCompl (K := K) hn5 α
  change ι ∈ (MulAut.conj : matrixDerived (coordinateQuadPlus n K) →*
    MulAut (matrixDerived (coordinateQuadPlus n K))).range at hι
  obtain ⟨γ', hγ'⟩ := MonoidHom.mem_range.1 hι
  let γ : spinGroup (quadPlus n K) := πe.symm γ'
  let c : spinGroup (quadPlus n K) →* spinGroup (quadPlus n K) :=
    πe.symm.toMonoidHom.comp (c₀.toMonoidHom.comp πe.toMonoidHom)
  have hΘ : ∀ x : spinGroup (quadPlus n K), Θ (πe x) = ⟨ψ x, ⟨x, rfl⟩⟩ := by
    intro x
    have h : Θ (πe x) = MonoidHom.ofInjective hψ x := by
      simp [Θ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [h]
    exact Subtype.ext (MonoidHom.ofInjective_apply hψ)
  have hconj : ∀ k : spinGroup (quadPlus n K), a * ψ k * a⁻¹ = ψ (γ * c k * γ⁻¹) := by
    intro k
    have hmem : a * ψ k * a⁻¹ ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp ha (ψ k)).mp ⟨k, rfl⟩
    have h1 : Θ (α (πe k)) = ⟨a * ψ k * a⁻¹, hmem⟩ := by
      change Θ (Θ.symm (cAut (Θ (πe k)))) = _
      rw [hΘ k, MulEquiv.apply_symm_apply]
      exact Subtype.ext (CFSG.LocalAnalysis.ComponentInitial.coe_conjAut ha ⟨ψ k, ⟨k, rfl⟩⟩)
    have h2 : Θ (α (πe k)) = ⟨ψ (γ * c k * γ⁻¹), ⟨_, rfl⟩⟩ := by
      have hπek : πe (γ * c k * γ⁻¹) = γ' * c₀ (πe k) * γ'⁻¹ := by
        simp [γ, c, map_mul, map_inv]
      calc Θ (α (πe k)) = Θ (MulAut.conj γ' (c₀ (πe k))) := by
            rw [hα, ← hγ']
            rfl
        _ = Θ (πe (γ * c k * γ⁻¹)) := by
            rw [MulAut.conj_apply, ← hπek]
        _ = ⟨ψ (γ * c k * γ⁻¹), ⟨_, rfl⟩⟩ := hΘ _
    exact congrArg Subtype.val (h1.symm.trans h2)
  rw [AutOm.mem_plusCompl] at hc₀
  rcases hc₀ with ⟨τ, hc₀ | hc₀⟩
  · have hc : c = πe.symm.toMonoidHom.comp
        ((AutOm.fieldAutP n τ).toMonoidHom.comp πe.toMonoidHom) := by
      rw [← hc₀]
    refine ⟨γ, πe.symm.toMonoidHom.comp
      ((AutOm.fieldAutP n τ).toMonoidHom.comp πe.toMonoidHom), false, τ, ?_, ?_⟩
    · rw [← hc]
      exact hconj
    · intro k y
      have hc' : πe.symm.toMonoidHom.comp
          ((AutOm.fieldAutP n τ).toMonoidHom.comp πe.toMonoidHom) =
        πe.symm.toMonoidHom.comp
          ((conjAct (coordinateQuadPlus n K) (AutOm.gField (n := n) τ)).toMonoidHom.comp
            πe.toMonoidHom) := by
        rw [AutOm.fieldAutP_eq]
      rw [hc']
      exact spinAction_plusSemi_of_semilinear hn1 πe hπe (AutOm.gField τ) false τ
        (reindex_plusSemi_false hn1 τ) k y
  · have hc : c = πe.symm.toMonoidHom.comp
        ((AutOm.plusRefl hn1 * AutOm.fieldAutP n τ).toMonoidHom.comp πe.toMonoidHom) := by
      rw [← hc₀]
    refine ⟨γ, πe.symm.toMonoidHom.comp
      ((AutOm.plusRefl hn1 * AutOm.fieldAutP n τ).toMonoidHom.comp πe.toMonoidHom),
      true, τ, ?_, ?_⟩
    · rw [← hc]
      exact hconj
    · intro k y
      have hc' : πe.symm.toMonoidHom.comp
          ((AutOm.plusRefl hn1 * AutOm.fieldAutP n τ).toMonoidHom.comp πe.toMonoidHom) =
        πe.symm.toMonoidHom.comp
          ((conjAct (coordinateQuadPlus n K)
            (AutOm.gRefl hn1 * AutOm.gField (n := n) τ)).toMonoidHom.comp
            πe.toMonoidHom) := by
        rw [AutOm.plusRefl_mul_fieldAutP_eq]
      rw [hc']
      exact spinAction_plusSemi_of_semilinear hn1 πe hπe
        (AutOm.gRefl hn1 * AutOm.gField τ) true τ (reindex_plusSemi_true hn1 τ) k y

end CFSG.StandardType.KGOm
