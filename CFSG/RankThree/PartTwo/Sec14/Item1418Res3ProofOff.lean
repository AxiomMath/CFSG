module

public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec15.HypR

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Late
  CFSG.GH74.GLS

namespace Proof1418Res3

variable {G : Type} [Group G] [Finite G]

theorem max_of_sec13 {A L : Subgroup G} {c : G} (hD : Sec13Data G A c L) :
    (∀ x ∈ A, x ^ 3 = 1) ∧ (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      ∀ y : G, y ^ 3 = 1 → (∀ a ∈ A, a * y = y * a) → y ∈ A :=
  ⟨hD.isElemAbelian.2, fun _ hx _ hy => hD.commute hx hy,
    fun _ hy3 hyA => Sec15.mem_of_mem_partTwoF hD.mem_partTwoF hy3 fun a ha =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hyA a ha)⟩

end Proof1418Res3

end CFSG.RankThree.PartTwo.Sec14
