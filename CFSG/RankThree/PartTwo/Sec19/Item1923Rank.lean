module

import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKO3
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.RankThree.PartTwo.Sec19.Item194Five
public import CFSG.RankThree.PartTwo.Sec19.Item19Res3ProofAsc93

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem exists_card_eq_pow_of_isElemAbelian {p : ℕ} (hp : p.Prime) {X : Type} [Group X]
    [Finite X] {E : Subgroup X} (hE : CFSG.Open.IsElemAbelian p E) :
    ∃ k : ℕ, Nat.card E = p ^ k := by
  haveI := Fact.mk hp
  have hP : IsPGroup p E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  exact hP.exists_card_eq

theorem Hyp1921.card_le_of_isElemAbelian_quotient (h : Hyp1921 G A M N L)
    {E : Subgroup (M ⧸ CFSG.pCore 2 M)} (hE : CFSG.Assembly.IsElemAbelian 3 E) :
    Nat.card E ≤ 27 := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian Nat.prime_three hE
  have hkle : k ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (M ⧸ CFSG.pCore 2 M)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top hE hk
  have hres : CFSG.pRank 3 (M ⧸ CFSG.pCore 2 M) ≤ CFSG.Open.pRank 3 M :=
    CFSG.RankThree.PartTwo.Sec20.Res11.pRank_quotient_le M Nat.prime_three (by norm_num)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top 3 (M ⧸ CFSG.pCore 2 M)] at hres
  have hq : CFSG.Open.pRank 3 (⊤ : Subgroup (M ⧸ CFSG.pCore 2 M)) ≤ 3 :=
    hres.trans h.setting194.pRank_three_le
  calc Nat.card E = 3 ^ k := hk
    _ ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (hkle.trans hq)
    _ = 27 := by norm_num

theorem Hyp1921.card_le_of_isElemAbelian_quotient_of_five_le (h : Hyp1921 G A M N L) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) {E : Subgroup (M ⧸ CFSG.pCore 2 M)}
    (hE : CFSG.Assembly.IsElemAbelian p E) : Nat.card E ≤ p ^ 2 := by
  obtain ⟨k, hk⟩ := exists_card_eq_pow_of_isElemAbelian hp hE
  have hkle : k ≤ CFSG.Open.pRank p (⊤ : Subgroup (M ⧸ CFSG.pCore 2 M)) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hE hk
  have hres : CFSG.pRank p (M ⧸ CFSG.pCore 2 M) ≤ CFSG.Open.pRank p M :=
    CFSG.RankThree.PartTwo.Sec20.Res11.pRank_quotient_le M hp (by omega)
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top p (M ⧸ CFSG.pCore 2 M)] at hres
  have hq : CFSG.Open.pRank p (⊤ : Subgroup (M ⧸ CFSG.pCore 2 M)) ≤ 2 :=
    hres.trans (h.setting194.pRank_le_two hp (by omega))
  calc Nat.card E = p ^ k := hk
    _ ≤ p ^ 2 := Nat.pow_le_pow_right hp.pos (hkle.trans hq)

end CFSG.RankThree.PartTwo.Late
