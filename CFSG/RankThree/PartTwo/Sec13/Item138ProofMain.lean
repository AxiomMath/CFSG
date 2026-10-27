module

public import CFSG.RankThree.PartTwo.Sec13.Item138N

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

@[expose] def Item138PGLN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → Sec8.IsZ3PGLThreePi (lBarA c L E)

@[expose] def Item138SylowN : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E : Subgroup G),
    Hyp138 A c L E → ∀ F : Subgroup G, IsF138N L E F →
      Sec8.IsZ3PGLThreePi (lBarA c L E) →
        CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F) (Subgroup.normalizer (Subgroup.zpowers c : Set G))

theorem item138MainN_of (hPGL : Item138PGLN) (hSyl : Item138SylowN) : Item138MainN :=
  fun G _ _ A c L E hH F hF =>
    ⟨hPGL G A c L E hH, hSyl G A c L E hH F hF (hPGL G A c L E hH)⟩

end CFSG.RankThree.PartTwo.Sec13
