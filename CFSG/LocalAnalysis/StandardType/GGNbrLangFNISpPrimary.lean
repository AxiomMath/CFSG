module

public import CFSG.RankThree.PartOne.KC.PrimaryDecomposition
import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorFix
import CFSG.RankThree.PartOne.KC.LinearCommutantFactors

public section

namespace CFSG.StandardType.ClassicalBlocks

theorem primaryFactors_map_eq_self_of_semilinear {K V : Type} [Field K] [Finite K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {p : ℕ} (hp : p.Prime) (hpK : (p : K) ≠ 0)
    {x : Module.End K V} (hxp : x ^ p = 1) {σ : K ≃+* K} (hσp : σ ^ p = 1) (S : V ≃+ V)
    (hS : ∀ (c : K) (v : V), S (c • v) = σ c • S v) (hSx : ∀ v, S (x v) = x (S v)) :
    ∀ a ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors x, a.map (σ : K →+* K) = a := by
  intro a ha
  exact CFSG.RankThree.PartOne.KCOrthComm.map_eq_self_of_pow_eq_one hp
    (CFSG.RankThree.PartOne.KCLinComm.squarefree_minpoly_of_pow_eq_one hpK hxp) hxp
    (j := 1) (by simpa using hσp)
    (CFSG.RankThree.PartOne.KCOrthComm.map_minpoly_eq (σ := σ) (F := S) hS hSx) ha

end CFSG.StandardType.ClassicalBlocks
