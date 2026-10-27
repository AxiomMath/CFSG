module

public import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15.Proof158Steps CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projImage)

@[expose] noncomputable def Step158NineE : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ (p e : ℕ) [Fact p.Prime], 1 ≤ e →
    Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e →
    (p ^ e % 9 = 1 ∨ p ^ e % 9 = 8) →
    ∀ Y ∈ scriptY0 A (lB A), MeetsY4 A (lB A) L Y →
    ∀ P : Subgroup G, A ≤ P →
      CFSG.ABGLocalTools.IsSylowOf 3 P
        (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)) →
      A ≠ omegaOneThree P → ∃ E : Subgroup G, E ≤ P ∧ E ≤ Subgroup.normalizer (L : Set G) ∧
        CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 27 ∧ c ∈ E ∧
        Late.sectionCentralizer E L ((aschbacherSolvableCore 3 L).map L.subtype) =
          (Subgroup.zpowers c : Set G) ∧
        Sec4.IsTypeCOn E L

theorem step158CartanNineR_of_nineE (h138 : Item138N) (hE : Step158NineE) :
    Step158CartanNineR := by
  intro G _ _ A c L hR p e _ he hL3 h9 Y hY hmeet P hAP hP hΩ
  obtain ⟨E, hEP, hEN, hE3, hE27, hcE, hsec, hTC⟩ :=
    hE G A c L hR p e he hL3 h9 Y hY hmeet P hAP hP hΩ
  exfalso
  have hL3pi : IsLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) := ⟨p, e, inferInstance, he, hL3⟩
  have hEE : E ∈ partTwoE G :=
    mem_partTwoE_of_le_normalizer hY.2 hE3 hE27 ((hEP.trans hP.le).trans inf_le_right)
  obtain ⟨-, hmod9, -⟩ := h138 G A c L hR.toSec13Data hL3pi E hcE hE3 hE27 hEN hsec
    (Or.inr (hypT_of_mem_of_mem hR hEE hcE)) hTC
  exact hmod9 p e he hL3 h9

end CFSG.RankThree.PartTwo.Sec15
