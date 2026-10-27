module

public import CFSG.GroupTheory.ABGLocalTools.Basic
public import CFSG.RankThree.PartTwo.Sec4.StatementsGraphField

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

@[expose] def Step183Cb :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (B X H : Subgroup G) (s : G), Sec18Std G B X →
    H ∈ scriptH B X → Sec4.Concl4442 B X H s →
    ∀ D : Subgroup G, D ≤ B → Nat.card D = 3 →
      inSubgroup perfectResidual H ⊓ Subgroup.normalizer (B : Set G) ≤
        Subgroup.normalizer (D : Set G) →
      (D : Set G) ⊆ sectionCentralizer B (inSubgroup perfectResidual H)
        (CFSG.Open.pCoreOf 2 (inSubgroup perfectResidual H))

@[expose] def Step183S : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M N L S : Subgroup G), Sec18Std G A M →
    IsMaximalTwoLocal N → A ≤ N → N ≠ M →
    inSubgroup (CFSG.pPrimeCore 3) M = inSubgroup (CFSG.pPrimeCore 3) (M ⊓ N) →
    CFSG.Open.pCoreOf 2 (M ⊓ N) = CFSG.Open.pCoreOf 2 M →
    L ∈ oTwoComponentsIn N →
    CFSG.ABGLocalTools.IsSylowOf 2 S (inSubgroup (CFSG.pPrimeCore 3) (N ⊓ M)) →
    L ⊔ A ⊔ S ∈ scriptH A M →
    CFSG.Open.pCoreOf 2 ((L ⊔ A ⊔ S) ⊓ M) ≤ CFSG.Open.pCoreOf 2 (M ⊓ N)

end CFSG.RankThree.PartTwo.Sec18
