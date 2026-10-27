module

public import CFSG.Blueprint.NativeSporadic
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut

@[expose] def ONAutFact : Prop :=
  ∀ (R : Subgroup (MulAut CFSG.Blueprint.NativeSporadic.ON))
    (X : Subgroup CFSG.Blueprint.NativeSporadic.ON),
    IsPGroup 2 R →
    ((∃ (_ : Fact (Nat.Prime 7))
        (f : ↥X →* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)),
        Function.Surjective f) ∨
      ∃ f : ↥X →* alternatingGroup (Fin 7), Function.Surjective f) →
    (∀ x ∈ X, MulAut.conj x ∈
      Subgroup.normalizer (R : Set (MulAut CFSG.Blueprint.NativeSporadic.ON))) →
    R = ⊥

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut
