module

public import CFSG.RankThree.PartTwo.Sec15.Item155RProof
public import CFSG.RankThree.PartTwo.Sec16.Item161Proof

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

theorem sec15R_of_basePoint {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec15R G A c L) {c' : G} {L' : Subgroup G}
    (hc' : Subgroup.zpowers c' ∈ omegaA A) (hL' : L' ∈ lA A c') : Sec15R G A c' L' :=
  { h with zpowers_mem_omegaA := hc', mem_lA := hL' }

@[expose] noncomputable def Item154PiR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Sec16.Item154Pi A (lB A) L

theorem item154R_of_item154PiR (h : Item154PiR) : Item154R :=
  fun G _ _ A c L hR => Sec16.item154_of_item154Pi (h G A c L hR)

end CFSG.RankThree.PartTwo.Sec15
