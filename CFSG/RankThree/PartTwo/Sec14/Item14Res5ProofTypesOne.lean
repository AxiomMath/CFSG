module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesA7
public import CFSG.RankThree.PartTwo.Sec14.Item14Res5ProofTypesM12

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS

@[expose] noncomputable def Step142TypesL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G)
    (h : Sec14Std G A c L),
    letI := ker142_normal (LB := lB A) h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
    ∀ Q ∈ maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A
        (piCompl 3),
      k142 A (lB A) c = L ⊔ pPrimeCoreOf 3 (Subgroup.normalizer (Subgroup.zpowers c : Set G)) ⊔
          pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) →
      IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) →
      ∃ (a : G) (ha : a ∈ A), alpha142 A (lB A) c a ha ≠ 1 ∧
        img142 A (lB A) c Q =
          thetaC142 A (lB A) c (alpha142 A (lB A) c a ha) ⊔ thetaCA142 A (lB A) c

theorem step142TypesOne_of
    (h131 : Item131)
    (hL3 : Step142TypesL3) : Step142TypesOne := by
  intro G _ _ A c L h Q hQ hK hT
  have : (ker142 A (lB A) c).Normal :=
    ker142_normal h.toSec13Data.isElemAbelian.1 h.toSec13Data.mem_A
  rcases hT with hL | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · exact hL3 G A c L h Q hQ hK hL
  · exact Res5TypesA7.typesOne_A7 h131 h hQ hK φ
  · exact Res5TypesM12.typesOne_M12 h131 h hQ hK φ

end CFSG.RankThree.PartTwo.Sec14
