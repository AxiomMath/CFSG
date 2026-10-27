module

public import CFSG.RankThree.PartTwo.Sec11.Item1120Proof

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

section Statements

@[expose] def Step1120G : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R Y : Subgroup G) (d x s r g : G), Sec11Big G A c L a R Y d x s r g →
      Subgroup.closure ({r, s} : Set G) ≠ Subgroup.closure {a, s} →
      g ∈ Subgroup.normalizer ((Subgroup.closure {s, x, a} : Subgroup G) : Set G)

end Statements

section Provers

theorem item1120_of_G (h45 : Sec4.Item4_5) (h113 : Item113) (hG : Step1120G) : Item1120 := by
  intro G _ _ A c L a R Y d x s r g hbig
  have h := hbig.toSec11Data
  by_cases hrs : Subgroup.closure ({r, s} : Set G) = Subgroup.closure {a, s}
  · rw [Item1120Proof.closure_eq_R h hrs]
    exact sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr h.g_mem_normalizer)
  · exact sup_le (Item1120Proof.R_le_normalizer_V h45 h113 h)
      (Subgroup.zpowers_le.mpr (hG G A c L a R Y d x s r g hbig hrs))

end Provers

end CFSG.RankThree.PartTwo.Sec11
