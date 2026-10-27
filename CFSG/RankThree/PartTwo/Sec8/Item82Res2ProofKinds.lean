module

public import CFSG.RankThree.PartTwo.Sec8.Item82ProofDefs

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item82Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts
open CFSG.Assembly.RankThreeEven (projSL)

section Kinds


@[expose] def KF82LThreeModel : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G) (x : G) (n : ℕ) (k : AutKind), Even n →
    1 ≤ n → Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 2 n)) →
    InducesStdKind L x k → InducesKindPSL 3 (GaloisField 2 n) L x k

theorem kF82TwoLThreeKinds_of (hM : KF82LThreeModel) : KF82TwoLThreeKinds := by
  intro G _ _ L x n hn hn1 hL _ hdiag
  have hd := hM G L x n .diagonal hn hn1 hL hdiag
  refine ⟨fun hf => ?_, fun hgf => ?_⟩
  · have := inducesKindPSL_unique L le_rfl hd (hM G L x n .field hn hn1 hL hf)
    exact AutKind.noConfusion this
  · have := inducesKindPSL_unique L le_rfl hd (hM G L x n .graphField hn hn1 hL hgf)
    exact AutKind.noConfusion this

end Kinds

end CFSG.RankThree.PartTwo.Sec8.Item82Proof
