module

public import CFSG.RankThree.PartTwo.Sec20.One

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def Item1810Hyp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M H : Subgroup G) (c : G), Sec18H G A M H c →
    Hyp187 A M H c →
      ∀ P : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 P (Subgroup.normalizer (A : Set G)) →
        conjugatesIn (Subgroup.zpowers c) P = {Subgroup.zpowers c}

end CFSG.RankThree.PartTwo.Sec18

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late

theorem Ctx20One.hyp201One {G : Type} [Group G] [Finite G] {A M L N : Subgroup G} {c : G}
    {T : Subgroup G} (h : Ctx20One G A M L N c T) : Hyp201One G A M L N c :=
  ⟨h.toHyp201, h.one⟩

@[expose] def Item202One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201One G A M L N c →
    scriptM ((A ⊔ kTwenty M c : Subgroup G) : Set G) = {M}

@[expose] def Item203One1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201One G A M L N c →
    M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G)

@[expose] def Item203One2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G), Hyp201One G A M L N c →
    Sec4.HasSection (Sec4.autIn M (A ⊓ L)) (QuaternionGroup 2)

@[expose] def Item207One : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G),
    Ctx20One G A M L N c T → T ≤ N →
      kTwenty M c ⊓ Subgroup.centralizer (zTwenty T : Set G) ≤ N

end CFSG.RankThree.PartTwo.Sec20
