module

import CFSG.RankThree.PartTwo.Sec4.Item413Cases
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.PartTwo.Sec4.Item417ResProofOut

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU)


section Certs


@[expose] def Item417OutCharThreeRest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L A E : Subgroup G) (c : G) (m : ℕ),
    IsInnerOutConf417 L A E c m →
      ((∃ e : ℕ, 1 ≤ e ∧ e ≤ 2 ∧
          (Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 3 (GaloisField 3 e)) ∨
            Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 3 3 e))) ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSL 4 (GaloisField 3 1)) ∨
        ChevalleyExceptionalModel (L ⧸ aschbacherSolvableCore 3 L) .G2 3 1 ∨
        Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* projSU 4 3 1)) → False

theorem item417OutCharThree_of (hR : Item417OutCharThreeRest) : Item417OutCharThree := by
  intro G _ _ L A E c m hconf hX
  exfalso
  have hZ := hconf.2.2.2.2.2.2.2.2.2.2.1
  refine hR G L A E c m hconf ?_
  rcases hX with h | h | ⟨-, hG2 | ⟨⟨φ⟩⟩⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
        (quotientCenterEquivOfBot hZ).symm hG2)))
  · exact Or.inr (Or.inr (Or.inr ⟨(quotientCenterEquivOfBot hZ).symm.trans φ⟩))

end Certs

end CFSG.RankThree.PartTwo.Sec4
