module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Norm
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsFive
import CFSG.LocalAnalysis.UniquenessCase.UC22R847O3Lift
import CFSG.LocalAnalysis.UniquenessCase.UC22U3PairLoss
import CFSG.LocalAnalysis.UniquenessCase.UC22U3Loss0
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107E3Pair
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z6
import CFSG.LocalAnalysis.UniquenessCase.UC22S206c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.RankThreeUC.TheoremDCentralizerReduction
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.R847O3

open CFSG.Open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive
  StronglyEmbeddedFiveZ)

variable {G : Type} [Group G] [Finite G]

theorem r847OrderThree_dataOfSetup (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hKThin : KThinSimple) (hS : RankThreeUC.Standing G)
    (S : RankThreeUC.Setup G) (hSg : UC6S846.SigmaStd (dataOfSetup hS S)) :
    R8107E3.R847OrderThree (dataOfSetup hS S) := by
  intro Y hY r X hXY hX p hp _ hs
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYM : Y ≤ S.M := hY.1.le
  by_cases hsp3 : IsStronglyPEmbedded 3 S.M
  · exact hsp3.normalizer_le (fun h => by rw [h, Subgroup.card_bot] at hX; omega)
      (IsPGroup.of_card (n := 1) (by rw [hX, pow_one])) (hXY.trans hYM)
  obtain ⟨hpp, hp2⟩ := (dataOfSetup hS S).sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  have hp5 : 5 ≤ p := R8107E3.five_le_of_mem_sig hSg hsp3 hY hp
  have hsp : IsStronglyPEmbedded p S.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  have h3 := R8107Shape.three_dvd_card_bar2 r
  obtain ⟨hZ, hloss⟩ : center (Bar2 Y) = ⊥ ∧ LossPairAt (Bar2 Y) p := by
    rcases hs with s | ⟨n, hn⟩
    · have hZ := R8107Shape.center_eq_bot_of_thin8 hY s
      exact ⟨hZ, lossPairAt_of_thinShape (R8107Shape.thinShape_of_thin8 _ hKThin hY s h3) hZ
        hY.2.2.1 h3 ((uc22s206c_pRank_le Y Nat.prime_three (by norm_num)).trans r.le) hpp hp2
        fun B hB => R8107Shape.isCyclic_of_isPGroup_of_thin8 s hpp hp2 hB⟩
    · exact ⟨(U3Loss.isSU3_of_isU3 hn).2, lossPairAt_of_isU3 hn hpp hp5⟩
  obtain ⟨B, hBM, hB, hBc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank hpp (hSg.three_le p hp)
  have hBN := uc22ine229_le_normalizer hY hpp hp5 Nat.prime_three (by norm_num) hXY hX
    (by rw [hZ, Subgroup.card_bot]; norm_num) (R8107E3.pRank_three_le_three_of_not_sp hSg hsp3 hY)
    hBM hB
  obtain ⟨Q, hQB, hQc, x, hxY, hx3, t, ht, ht2, hc⟩ :=
    exists_involution_of_lossPairAt hpp hp2 hloss hBN hB
  obtain ⟨c, hcY, hcX⟩ := RankThreeUC.exists_mem_map_conj_eq_of_card_eq_prime r.le hXY
    (zpowers_le.2 hxY) hX (by rw [Nat.card_zpowers, hx3])
  suffices hN : normalizer ((zpowers x : Subgroup G) : Set G) ≤ S.M by
    intro g hg
    have hcg : c * g * c⁻¹ ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
      rw [← hcX, ← map_equiv_normalizer_eq]
      exact ⟨g, hg, rfl⟩
    have hcM := hYM hcY
    have h := mul_mem (mul_mem (inv_mem hcM) (hN hcg)) hcM
    rwa [show c⁻¹ * (c * g * c⁻¹) * c = g by group] at h
  by_contra hnot
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 (hB.isPGroup.to_le hQB)
  have hj2 : 2 ≤ j := by
    by_contra hlt
    have h1 : p * Nat.card Q ≤ p ^ 2 := by
      rw [hj, ← pow_succ']
      exact Nat.pow_le_pow_right hpp.pos (by omega)
    exact absurd ((hBc ▸ hQc).trans h1) (not_le.2 (Nat.pow_lt_pow_right hpp.one_lt (by norm_num)))
  obtain ⟨A, hAc, -, hAQ⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hpp (H := ⊥) (L := Q)
    (n := 2) (by rw [Subgroup.card_bot]; exact one_dvd _) (by rw [hj]; exact pow_dvd_pow p hj2)
    bot_le
  have hA : IsElemAbelian p A := hB.mono (hAQ.trans hQB)
  have hAN : A ≤ normalizer ((zpowers x : Subgroup G) : Set G) := fun a ha =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 (by
      rintro _ ⟨i, rfl⟩
      exact ((show Commute a x from (hc a (hAQ ha)).1).zpow_right i).eq.symm))
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx3; omega
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hpp hp2 hsp
    (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have h75 := k.step75 hp5 hSE
  have hH := k.config_normalizer (zpowers_ne_bot.2 hx1) (zpowers_le.2 (hYM hxY))
    (CFSG.SectionRank.le_pRank hpp.one_lt (le_inf (hAQ.trans (hQB.trans hBM)) hAN) hA hAc) hnot
  exact k.false_of_involution h75 hH (k.goodZ_of_kIDExcluded hp5
    (k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)) hH hSEZ h75).1
    (le_inf hAN (hAQ.trans (hQB.trans hBM))) hA hAc (mem_inf.2 ⟨ht.2, hYM ht.1⟩) ht2
    fun a ha => (hc a (hAQ ha)).2

end CFSG.LocalAnalysis.UniquenessCase.UC22.R847O3

end
