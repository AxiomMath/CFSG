module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenSixDefs

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven

@[expose] def YamakiSp62CharTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    CFSG.Open.IsCharTwoType G →
    ∀ (S : Sylow 2 G) (z : G), orderOf z = 2 → z ∈ (S : Subgroup G) →
      (∀ s ∈ (S : Subgroup G), s * z = z * s) →
      Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃* YamakiHat) →
      CFSG.Blueprint.LieModel G .PSp 3 2 1

theorem inCatalog_of_yamakiCharTwo (hY : YamakiSp62CharTwo)
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hchar : CFSG.Open.IsCharTwoType G) (S : Sylow 2 G) {z : G} (hz : orderOf z = 2)
    (hzS : z ∈ (S : Subgroup G)) (hzc : ∀ s ∈ (S : Subgroup G), s * z = z * s)
    (he : Nonempty (↥(Subgroup.centralizer ({z} : Set G)) ≃* YamakiHat)) :
    CFSG.Assembly.InCatalog G :=
  inCatalog_of_yamakiConcl (Or.inl (hY G hs hnab hchar S z hz hzS hzc he))

end CFSG.RankThree.PartTwo.Sec19.SolEven
