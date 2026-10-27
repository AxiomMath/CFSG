module

public import CFSG.RankThree.PartTwo.KFacts.AutKinds
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.KFacts

@[expose] def KS167D4 : Prop :=
  ∀ (J : Type) [Group J] [Finite J] (n : ℕ), 4 ≤ n → ¬ 3 ∣ n →
    CFSG.Blueprint.ChevalleyExceptionalModel J .trialityD4 2 n →
    ∀ α : MulAut J, α ^ 3 = 1 → ¬ IsInnerAut α →
    ∀ L : Subgroup J, L ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J) →
      Sec4.IsoLThreePi ↥L 2 n →
      (L.subgroupOf (MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id J))).IsSubnormal →
    ∀ E : Subgroup J, E ≤ L → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
    ∀ T : Subgroup J, IsPGroup 2 T → T.map α.toMonoidHom = T →
      E ≤ Subgroup.normalizer (T : Set J) → T = ⊥

end CFSG.RankThree.PartTwo.KFacts
