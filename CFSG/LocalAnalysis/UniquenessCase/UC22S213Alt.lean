module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UCFront10K101
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.OrdinaryProofs.AltThreeRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive)

variable {G : Type} [Group G] [Finite G]

theorem uc22s213_not_centralizesBar_of_isAlt (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) (hPart : PartIAt S.M) (hSE : StronglyEmbeddedFive)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic) {L : Subgroup G}
    (hL : L ∈ calC S.M) (hZ : ¬ 3 ∣ Nat.card (center (Bar2 L))) {m : ℕ} (hm : 6 ≤ m)
    (hA : IsAlt (BarInf L) m) (h3 : CFSG.Open.pRank 3 L ≤ 2)
    (hk1 : IsStronglyPEmbedded 3 S.M → CFSG.Open.pRank 3 L ≤ 1) {a : G}
    (hodd : Odd (orderOf a)) (hpr : (orderOf a).Prime)
    (hN : CFSG.Open.pRank S.p (normalizer ((zpowers a : Subgroup G) : Set G) ⊓ S.M) ≤ 1) :
    ¬ CentralizesBar a L := by
  obtain ⟨e⟩ := hA
  have he := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
  have hb := uc22s213_pRank_three_barInf hL.2.2 hZ
  have hm8 : m ≤ 8 := by
    by_contra h
    have h9 := CFSG.SectionRank.three_le_pRank_alternating (n := m) (by omega)
    omega
  have h27 : ¬ 27 ∣ Nat.card (BarInf L) := by
    rw [Nat.card_congr e.toEquiv]
    clear he hb
    interval_cases m <;>
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] <;> decide
  have h2 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (BarInf L)) := by
    rw [he]
    exact CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs.two_le_pRank_three_alternating hm
  refine uc22s213_not_centralizesBar_of_inner hS hU S hσ hPart hSE hOut hL hZ (fun σ hσ' => ?_)
    h27 h2 hk1 hodd hpr hN
  obtain ⟨x, hx⟩ := F10.exists_conj_of_odd_orderOf_alt (by omega) e σ hσ'
  exact ⟨x, hx.symm⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
