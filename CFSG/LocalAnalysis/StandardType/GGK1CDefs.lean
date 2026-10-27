module

public import CFSG.LocalAnalysis.StandardType.GGK1Defs
public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.Classical.SteinbergBJSymplecticCrossPrimeBlocks

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open Polynomial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.Classical (spEnd IsReciprocalTransversal)
open CFSG.RankThree.PartOne.KCPrimary

@[expose] noncomputable def ggK1CSelfDualFactors {K : Type} [Field K] {r : ℕ}
    (x : ↥(StatedSp r K)) : Finset K[X] := by
  classical
  exact (primaryFactors (spEnd x)).filter (fun h => h ≠ X - 1)

structure GGK1CMultOf (p nf d r : ℕ) (K : Type) [Field K]
    (x : ↥(StatedSp r K)) (m : List ℕ) : Prop where
  length_eq : m.length = (p - 1) / 2 + 1
  sum_eq : m.sum = r
  head_eq : m.headD 0 = Module.finrank K (primaryComponent (spEnd x) (X - 1)) / 2
  blocks_eq : (d = 1 ∧ ∃ P : Finset K[X], IsReciprocalTransversal (spEnd x) P ∧
      Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
        P.val.map (primaryMultiplicity (spEnd x))) ∨
    (d = 2 ∧ Multiset.ofList (m.tail.filter (fun j => decide (j ≠ 0))) =
      (ggK1CSelfDualFactors x).val.map (primaryMultiplicity (spEnd x)))

end CFSG.StandardType

end
