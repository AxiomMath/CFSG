module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.SuzukiCover
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_dvd_card_of_isSz {X : Type} [Group X] {n : ℕ} (h : IsSz X n) :
    2 ^ n - 1 ∣ Nat.card X := by
  obtain ⟨a, ha, rfl, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 h
  rw [Nat.card_congr (e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv a)).toEquiv,
    CFSG.SectionRank.card_suzukiMatrixGroup a ha]
  exact dvd_mul_left _ _

theorem uc22ine229_exists_sub {L : Subgroup G} {n : ℕ} (hLS : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n)
    {s : ℕ} (hsn : s ∣ n) {r : ℕ} (hr : r.Prime) (hrs : r ∣ 2 ^ s - 1) :
    ∃ A : Subgroup G, Nat.card A = r ∧ A ≤ L := by
  have hrn : r ∣ 2 ^ n - 1 := hrs.trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hsn)
  have hrB : r ∣ Nat.card (Bar2 L) := by
    rcases hLS with hL | hS
    · rw [uc22p22r_L2_card hL]
      exact Dvd.dvd.mul_left (hrn.trans (Nat.sub_one_dvd_pow_sub_one (2 ^ n) 2)) _
    · exact hrn.trans (uc22ine229_dvd_card_of_isSz hS)
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) r
    (hrB.trans (Subgroup.card_quotient_dvd_card _))
  refine ⟨Subgroup.zpowers (x : G), ?_, (Subgroup.zpowers_le).2 x.2⟩
  rw [Nat.card_zpowers, Subgroup.orderOf_coe, hx]

end CFSG.LocalAnalysis.UniquenessCase.UC22
