module

public import CFSG.Quasithin.Background.G2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.GroupTheory.QuaternionAutPrime
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.F1Models
public import CFSG.RankThree.PartOne.S9.MinTwoAction.FixedRankFrattini
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup
open CFSG.GroupTheory
open CFSG.RankThree.PartOne.FixedRank36
open scoped IsMulCommutative

theorem orderOf_mk'_pCore_eq_of_prime {M : Type} [Group M] [Finite M] {b : M} {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 M) b) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hdvd : orderOf (QuotientGroup.mk' (CFSG.pCore 2 M) b) ∣ r := by
    rw [← hbr]
    exact orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 M)) b
  rcases (Nat.dvd_prime hr).mp hdvd with h1 | hr'
  · exfalso
    have hmem : b ∈ CFSG.pCore 2 M :=
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 M) (x := b)).mp
        (orderOf_eq_one_iff.mp h1)
    have hodd : Odd (orderOf b) := by rw [hbr]; exact hr.odd_of_ne_two hr2
    have hb1 : b = 1 := CFSG.Quasithin.eq_one_of_odd_orderOf_of_mem CFSG.pCore_isPGroup hmem hodd
    rw [hb1, orderOf_one] at hbr
    exact hr.ne_one hbr.symm
  · exact hr'

end CFSG.LocalAnalysis.UniquenessCase.UCK
