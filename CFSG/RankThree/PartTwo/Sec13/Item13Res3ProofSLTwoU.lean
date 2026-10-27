module

public import CFSG.RankThree.PartTwo.Sec13.Item13Res2ProofSLTwoE
import CFSG.RankThree.PartTwo.Sec16.Item16Tail15

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Step131bSLTwoInEUOdd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec13Data G A c L → Sec4.IsSLThreePiTwo (lBarA c L A) →
    (∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = (2 ^ f) ^ 2 ∧
      2 ^ f % 3 = 2 ∧
      Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ f) K)) →
    ∀ E : Subgroup G, E ≤ (L ⊔ A) ⊓ Subgroup.normalizer (A : Set G) →
      CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      ¬ IsCyclic (E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) →
      ¬ IsCyclic (E ⊓ L : Subgroup G) →
      (∀ x ∈ E, x ≠ 1 → Odd (Nat.card
        (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G))))) →
      E ∈ partTwoE G

theorem step131bSLTwoInEU_of_odd (hU : Step131bSLTwoInEUOdd) : Step131bSLTwoInEU := by
  intro G _ _ A c L hD hSL hSU E hEle hEe hE27 hEC hEL
  by_cases hodd : ∀ x ∈ E, x ≠ 1 → Odd (Nat.card
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({x} : Set G))))
  · exact hU G A c L hD hSL hSU E hEle hEe hE27 hEC hEL hodd
  · push Not at hodd
    obtain ⟨x, hxE, -, hev⟩ := hodd
    have hEx : E ≤ Subgroup.centralizer ({x} : Set G) := fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (hEe.1.is_comm.comm ⟨y, hy⟩ ⟨x, hxE⟩))
    exact Sec16.mem_partTwoE_of_thetaCen hEe hE27 hEx hev

end CFSG.RankThree.PartTwo.Sec13
