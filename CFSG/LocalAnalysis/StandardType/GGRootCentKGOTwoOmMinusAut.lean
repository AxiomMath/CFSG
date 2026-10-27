module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGOTwoOmMinusSemi

import CFSG.LocalAnalysis.StandardType.GGSixAutSteinbergOmegaMinus
import CFSG.LocalAnalysis.ComponentInitial.ThreeFactorFactor
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataConjugation
import CFSG.LocalAnalysis.ComponentInitial.GeneralizedFittingProduct

public section

namespace CFSG.StandardType.KGOm

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.PartOne.AUTSL

private theorem spinAction_minusSemi_of_semilinear {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (πe : spinGroup (quadMinus n K b c) ≃* matrixDerived (Qm n hn4 b c))
    (hπe : ∀ (x : spinGroup (quadMinus n K b c)) (v : Vm n K),
      Matrix.mulVec ((πe x : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K)
          (reindexVectorEquiv (minusIndexEquiv n (by omega)) v) =
        reindexVectorEquiv (minusIndexEquiv n (by omega))
          (spinAction (quadMinus n K b c) x v))
    (g : similarityPairs (Qm n hn4 b c)) (k : ℕ)
    (hco : ∀ y : Vm n K,
      reindexVectorEquiv (minusIndexEquiv n (by omega)) (minusSemi (by omega) hirr k y) =
        coordinateSemilinearMap g.val
          (reindexVectorEquiv (minusIndexEquiv n (by omega)) y))
    (x : spinGroup (quadMinus n K b c)) (y : Vm n K) :
    spinAction (quadMinus n K b c)
        (πe.symm (conjAct (Qm n hn4 b c) g (πe x))) (minusSemi (by omega) hirr k y) =
      minusSemi (by omega) hirr k (spinAction (quadMinus n K b c) x y) := by
  apply (reindexVectorEquiv (minusIndexEquiv n (by omega))).injective
  rw [hco (spinAction (quadMinus n K b c) x y), ← hπe x y,
    ← hπe (πe.symm (conjAct (Qm n hn4 b c) g (πe x))) (minusSemi (by omega) hirr k y),
    MulEquiv.apply_symm_apply, hco y]
  have hval : ((↑(((conjAct (Qm n hn4 b c)) g (πe x)) : GL (Fin (2 * n)) K))) =
      matrixConjugation g.val ((πe x).val) := by
    rw [conjAct_apply, matrixDerivedConjugation_val, matrixConjugation_apply]
  rw [show Matrix.mulVec ((↑(((conjAct (Qm n hn4 b c)) g (πe x)) :
        GL (Fin (2 * n)) K)) : Matrix (Fin (2 * n)) (Fin (2 * n)) K)
        (coordinateSemilinearMap g.val
          (reindexVectorEquiv (minusIndexEquiv n (by omega)) y)) =
      coordinateSemilinearMap g.val (Matrix.mulVec ((πe x : GL (Fin (2 * n)) K) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K)
        (reindexVectorEquiv (minusIndexEquiv n (by omega)) y))
    from by
      rw [hval]
      simpa only [matrixLinearEquiv_apply, AddEquiv.symm_apply_apply] using
        matrixConjugation_vector g.val (πe x).val
          (coordinateSemilinearMap g.val
            (reindexVectorEquiv (minusIndexEquiv n (by omega)) y))]

theorem exists_conj_minusSemi_of_mem_normalizer {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn4 : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {G : Type*}
    [Group G] {ψ : spinGroup (quadMinus n K b c) →* G} (hψ : Function.Injective ψ) {a : G}
    (ha : a ∈ Subgroup.normalizer (ψ.range : Set G)) :
    ∃ (γ : spinGroup (quadMinus n K b c))
      (φ : spinGroup (quadMinus n K b c) →* spinGroup (quadMinus n K b c)) (k : ℕ),
      (∀ z, a * ψ z * a⁻¹ = ψ (γ * φ z * γ⁻¹)) ∧
      ∀ (z : spinGroup (quadMinus n K b c)) (y : Vm n K),
        spinAction (quadMinus n K b c) (φ z) (minusSemi (by omega) hirr k y) =
          minusSemi (by omega) hirr k (spinAction (quadMinus n K b c) z y) := by
  classical
  have hn : 1 ≤ n := by omega
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, -, hf⟩ := FiniteField.card K 2
  have hf' : Nat.card K = 2 ^ (f : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hf
  let πe : spinGroup (quadMinus n K b c) ≃* matrixDerived (Qm n hn4 b c) :=
    MulEquiv.ofBijective (AutOm.spinModelMinus hn4 hirr)
      ⟨AutOm.spinModelMinus_injective hn4 hirr, AutOm.spinModelMinus_surjective hn4 hirr⟩
  have hπe : ∀ (x : spinGroup (quadMinus n K b c)) (v : Vm n K),
      Matrix.mulVec ((πe x : GL (Fin (2 * n)) K) :
          Matrix (Fin (2 * n)) (Fin (2 * n)) K)
          (reindexVectorEquiv (minusIndexEquiv n hn) v) =
        reindexVectorEquiv (minusIndexEquiv n hn) (spinAction (quadMinus n K b c) x v) :=
    fun x v => AutOm.spinModelMinus_mulVec hn4 hirr x v
  let Θ : matrixDerived (Qm n hn4 b c) ≃* ψ.range :=
    πe.symm.trans (MonoidHom.ofInjective hψ)
  let cAut : MulAut ψ.range := CFSG.LocalAnalysis.ComponentInitial.conjAut ψ.range ha
  let α : MulAut (matrixDerived (Qm n hn4 b c)) := (Θ.trans cAut).trans Θ.symm
  obtain ⟨ι, hι, k, hα⟩ := AutOm.exists_inner_mul_frobAut_pow (K := K) hn4 hirr hf' α
  change ι ∈ (MulAut.conj : matrixDerived (Qm n hn4 b c) →*
    MulAut (matrixDerived (Qm n hn4 b c))).range at hι
  obtain ⟨γ', hγ'⟩ := MonoidHom.mem_range.1 hι
  let γ : spinGroup (quadMinus n K b c) := πe.symm γ'
  let φ : spinGroup (quadMinus n K b c) →* spinGroup (quadMinus n K b c) :=
    πe.symm.toMonoidHom.comp ((AutOm.frobAut hn4 hirr ^ k).toMonoidHom.comp πe.toMonoidHom)
  have hΘ : ∀ x : spinGroup (quadMinus n K b c), Θ (πe x) = ⟨ψ x, ⟨x, rfl⟩⟩ := by
    intro x
    have h : Θ (πe x) = MonoidHom.ofInjective hψ x := by
      simp [Θ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [h]
    exact Subtype.ext (MonoidHom.ofInjective_apply hψ)
  have hconj : ∀ z : spinGroup (quadMinus n K b c), a * ψ z * a⁻¹ = ψ (γ * φ z * γ⁻¹) := by
    intro z
    have hmem : a * ψ z * a⁻¹ ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp ha (ψ z)).mp ⟨z, rfl⟩
    have h1 : Θ (α (πe z)) = ⟨a * ψ z * a⁻¹, hmem⟩ := by
      change Θ (Θ.symm (cAut (Θ (πe z)))) = _
      rw [hΘ z, MulEquiv.apply_symm_apply]
      exact Subtype.ext (CFSG.LocalAnalysis.ComponentInitial.coe_conjAut ha ⟨ψ z, ⟨z, rfl⟩⟩)
    have h2 : Θ (α (πe z)) = ⟨ψ (γ * φ z * γ⁻¹), ⟨_, rfl⟩⟩ := by
      have hπez : πe (γ * φ z * γ⁻¹) = γ' * (AutOm.frobAut hn4 hirr ^ k) (πe z) * γ'⁻¹ := by
        simp [γ, φ, map_mul, map_inv]
      calc Θ (α (πe z)) = Θ (MulAut.conj γ' ((AutOm.frobAut hn4 hirr ^ k) (πe z))) := by
            rw [hα, ← hγ']
            rfl
        _ = Θ (πe (γ * φ z * γ⁻¹)) := by
            rw [MulAut.conj_apply, ← hπez]
        _ = ⟨ψ (γ * φ z * γ⁻¹), ⟨_, rfl⟩⟩ := hΘ _
    exact congrArg Subtype.val (h1.symm.trans h2)
  have hfrob : AutOm.frobAut hn4 hirr ^ k = conjAct (Qm n hn4 b c)
      (frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k) := by
    rw [AutOm.frobAut, ← map_pow]
  have hφ : ∀ z : spinGroup (quadMinus n K b c), φ z = πe.symm (conjAct (Qm n hn4 b c)
      (frobPair n hn b c (ne_zero_of_irreducible_tail b c hirr) ^ k) (πe z)) := by
    intro z
    change πe.symm ((AutOm.frobAut hn4 hirr ^ k) (πe z)) = _
    rw [hfrob]
  refine ⟨γ, φ, k, hconj, ?_⟩
  intro z y
  rw [hφ z]
  exact spinAction_minusSemi_of_semilinear hn4 hirr πe hπe _ k
    (reindex_minusSemi hn hirr k) z y

end CFSG.StandardType.KGOm
