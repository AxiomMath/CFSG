module

public import CFSG.RankThree.PartTwo.Sec16.Item1617StepsProofTools
import CFSG.RankThree.PartTwo.Sec16.Item16Tail
public import CFSG.RankThree.PartTwo.Sec16.Item16Tail19

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] def KS1619CUL : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L D U : Subgroup G) (n : ℕ), IsSimpleGroup ↥L → 1 ≤ n →
    ¬ 3 ∣ n → Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) 2 n →
    D ≤ L → CFSG.Assembly.IsElemAbelian 3 D → Nat.card D = 9 →
    IsPGroup 2 U → U ≤ Subgroup.normalizer (L : Set G) → D ≤ Subgroup.normalizer (U : Set G) →
    (∃ E N : Subgroup G, N ≤ E ∧ E ≤ U ∧ ∃ _ : (N.subgroupOf E).Normal,
        IsElementaryAbelian 2 (↥E ⧸ N.subgroupOf E) ∧ Nat.card (↥E ⧸ N.subgroupOf E) = 2 ^ 4) →
      U ⊓ Subgroup.centralizer (L : Set G) ≠ ⊥

theorem step1619CU_of (h138 : Item138N) (hK : KS1619CUL) : Step1619CU := by
  intro G _ _ A c L h hLs n hz U hU2 hUc hAU hsec
  have hn3 := Proof1617.not_three_dvd_of_isZ3 h h138 hz
  obtain ⟨-, h9, -⟩ := Proof1617.facts_of_isZ3 h hz
  have hUN : U ≤ Subgroup.normalizer (L : Set G) :=
    hUc.trans (Proof1617.centralizer_le_normalizer_L h hz)
  exact hK G L (A ⊓ L) U n hLs hz.1 hn3 hz.2.1 inf_le_right
    (Proof169.isElemAbelian_of_le h.isElemAbelian inf_le_left) h9 hU2 hUN
    (inf_le_left.trans hAU) hsec

end CFSG.RankThree.PartTwo.Sec16
