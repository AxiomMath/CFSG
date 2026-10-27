module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
import CFSG.RankThree.PartOne.KC.OrthogonalCentralizerBlocks

public section

namespace CFSG.RankThree.PartOne.KCPrimary

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem primaryComponent_minpoly_eq_top (T : Module.End K V) :
    primaryComponent T (minpoly K T) = ⊤ := by
  simp only [primaryComponent, minpoly.aeval, LinearMap.ker_zero]

variable [FiniteDimensional K V]

theorem primaryFactors_eq_singleton_of_irreducible_minpoly (T : Module.End K V)
    (hT : Irreducible (minpoly K T)) :
    primaryFactors T = {minpoly K T} := by
  classical
  have hmonic : (minpoly K T).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral T)
  simp only [primaryFactors, UniqueFactorizationMonoid.normalizedFactors_irreducible hT,
    hmonic.normalize_eq_self, Multiset.toFinset_singleton]

noncomputable def commutantUnitsEquivGeneralLinearGroupOfIrreducibleMinpoly
    (T : Module.End K V) (hT : Irreducible (minpoly K T)) :
    (commutant T)ˣ ≃*
      LinearMap.GeneralLinearGroup (AdjoinRoot (minpoly K T))
        (primaryComponent T (minpoly K T)) := by
  classical
  have hfactor := primaryFactors_eq_singleton_of_irreducible_minpoly T hT
  let a : primaryFactors T := ⟨minpoly K T, by
    rw [hfactor]
    exact Finset.mem_singleton_self _⟩
  let : Unique (primaryFactors T) :=
    { default := a
      uniq := fun b => Subtype.ext (by
        simpa only [hfactor, Finset.mem_singleton] using b.property) }
  exact (commutantUnitsEquivPi hT.squarefree).trans (MulEquiv.piUnique _)

noncomputable def centralizerEquivGeneralLinearGroupOfIrreducibleMinpoly
    (T : V ≃ₗ[K] V) (hT : Irreducible (minpoly K T.toLinearMap)) :
    Subgroup.centralizer ({T} : Set (V ≃ₗ[K] V)) ≃*
      LinearMap.GeneralLinearGroup (AdjoinRoot (minpoly K T.toLinearMap))
        (primaryComponent T.toLinearMap (minpoly K T.toLinearMap)) :=
  (CFSG.RankThree.PartOne.KCOrthogonal.centralizerUnits T).trans
    (commutantUnitsEquivGeneralLinearGroupOfIrreducibleMinpoly T.toLinearMap hT)

theorem finrank_eq_natDegree_minpoly_mul_finrank_primaryComponent (T : Module.End K V)
    [Fact (Irreducible (minpoly K T))] :
    Module.finrank K V = (minpoly K T).natDegree *
      Module.finrank (AdjoinRoot (minpoly K T)) (primaryComponent T (minpoly K T)) := by
  have hdim : Module.finrank K (primaryComponent T (minpoly K T)) =
      Module.finrank K V := by
    rw [primaryComponent_minpoly_eq_top, finrank_top]
  exact hdim.symm.trans (finrank_primaryComponent T (minpoly K T))

theorem natCard_adjoinRoot_minpoly [Finite K] (T : Module.End K V) :
    Nat.card (AdjoinRoot (minpoly K T)) = Nat.card K ^ (minpoly K T).natDegree := by
  let : Module.Finite K (AdjoinRoot (minpoly K T)) :=
    (AdjoinRoot.powerBasis (minpoly_ne_zero (K := K) T)).finite
  rw [Module.natCard_eq_pow_finrank (K := K),
    (AdjoinRoot.powerBasis (minpoly_ne_zero (K := K) T)).finrank,
    AdjoinRoot.powerBasis_dim]

end CFSG.RankThree.PartOne.KCPrimary
