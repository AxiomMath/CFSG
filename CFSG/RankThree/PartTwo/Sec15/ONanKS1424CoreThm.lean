module

public import CFSG.RankThree.PartTwo.Sec15.Item1424StepsProofCore
public import CFSG.RankThree.PartTwo.Sec15.ONanKS1424Model
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreOddM
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreOddT
import CFSG.RankThree.PartTwo.Sec15.ONanKS1424CoreDFT

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartTwo.Sec15.KS1424

theorem exists_lmodel_gen {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (h : Sec4.IsoLThreePi X p e) :
    ∃ (π : Bool) (K : Type) (_ : Field K), PiField π p e K ∧ ModThree π (p ^ e) ∧
      Nonempty (LModel π p e K X) := by
  rcases h with ⟨hq3, ⟨φ⟩⟩ | ⟨hq3, ⟨φ⟩⟩
  · refine ⟨true, GaloisField p e, inferInstance, ⟨Fact.out, he, ?_⟩, hq3,
      ⟨LModel.ofEquiv (φ.trans (MulEquiv.subgroupCongr (Sec4.projSL_eq_projImage _ _)))⟩⟩
    rw [GaloisField.card p e (by omega)]
    rfl
  · refine ⟨false, GaloisField p (2 * e), inferInstance, ⟨Fact.out, he, ?_⟩, hq3,
      ⟨LModel.ofEquiv (φ.trans (MulEquiv.subgroupCongr (Sec4.projSU_eq_projImage _ _)))⟩⟩
    rw [GaloisField.card p (2 * e) (by omega)]
    change p ^ (2 * e) = (p ^ e) ^ 2
    rw [← pow_mul, mul_comm]

theorem ks1424Core : KS1424Core := by
  intro X _ _ hX R hR1 hR2 H hH n hn T _ hT φ hφ
  obtain ⟨p, e, hp, he, hXiso⟩ := hX
  obtain ⟨π, K, _, hK, hq, ⟨M⟩⟩ := exists_lmodel_gen he hXiso
  obtain ⟨π', K', _, hK', hq', ⟨M'⟩⟩ := exists_lmodel (by omega : 1 ≤ n) hT
  have := hK'.finite
  have : Finite T := Finite.of_surjective M'.μ M'.surjective
  by_cases hp2 : p = 2
  · subst hp2
    have : IsSimpleGroup T := Proof1424Steps.isSimpleGroup_of_isoLThreePi_two (by omega) hT
    obtain ⟨t₄, ht4⟩ := exists_order_four hK' hq' M'
    exact core_even hK M hR1 hR2 hH ht4 φ hφ
  · obtain ⟨F, hF, hFc⟩ := exists_elem_abelian_big hn hK' hq' M'
    exact core_odd hK hp2 M hF hFc φ hφ

end CFSG.RankThree.PartTwo.Sec15
