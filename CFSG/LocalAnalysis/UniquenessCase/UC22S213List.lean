module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213L2
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.List857
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOne
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Inner
import CFSG.LocalAnalysis.UniquenessCase.UC22S213Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S216J1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.RankThreeTheoremC.KFacts.L28.OutThree.Main
import CFSG.RankThree.PartTwo.KFacts.KS14Sz
import CFSG.CGT.Timmesfeld75.NodeAux
import CFSG.GroupTheory.PGroup.PrimePartTransport
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_3List (L : Subgroup G) : Prop :=
  3 ∣ Nat.card (center (Bar2 L)) ∨
    (CFSG.Open.pRank 3 L = 2 ∧
      (PartOne.Section8.List857 (BarInf L) ∨ PartOne.Section8.IsSL3PiType (BarInf L))) ∨
    (CFSG.Open.pRank 3 L = 1 ∧
      ((∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel (BarInf L) .PSL 3 p f) ∨
        (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel (BarInf L) .PSU 3 p f)))

section List

set_option linter.unusedSectionVars false


theorem uc22s213_list_of_calC (h33 : UCK.K33)
    (h31 : CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.KFactThreeRankOneSimple)
    {D : Data G} {L : Subgroup G} (hL : L ∈ calC D.M) (hL2 : ¬ S21_3ClosedL2 L)
    (hthin : ¬ F08.Thin8 L) (h3 : CFSG.Open.pRank 3 L ≤ 2) : S21_3List L := by
  by_cases hZ : 3 ∣ Nat.card (center (Bar2 L))
  · exact Or.inl hZ
  obtain ⟨hsimp, hnab⟩ := uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)
  haveI := hsimp
  have hrank := uc22s213_pRank_three_barInf hL.2.2 hZ
  obtain ⟨e0⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hLtop : L ≠ ⊤ :=
    ne_top_of_le_ne_top (uc22p20a_M_ne_top D) (CFSG.Quasithin.A3.subnormal_le hL.1)
  obtain ⟨i, ⟨f⟩⟩ := uc22p20d_inCatalog_bar2 D.standing.kProper hLtop hL.2.2
  have hi : Nonempty (BarInf L ≃* i.Group) := ⟨e0.trans f⟩
  rcases (by omega : CFSG.Open.pRank 3 L = 0 ∨ CFSG.Open.pRank 3 L = 1 ∨
      CFSG.Open.pRank 3 L = 2) with h0 | h1 | h2
  ·
    exfalso
    have h3' : ¬ 3 ∣ Nat.card (BarInf L) := by
      have h := CFSG.GroupTheory.not_dvd_card_of_pRank_eq_zero Nat.prime_three
        (H := (⊤ : Subgroup (BarInf L))) (hrank.trans h0)
      rwa [Subgroup.card_top] at h
    obtain ⟨n, hn⟩ := CFSG.RankThree.PartTwo.KFacts.KS14.suzukiModel_of_inCatalog_of_not_three_dvd
      (BarInf L) hnab ⟨i, hi⟩ h3'
    haveI : Group.IsPerfect (Bar2 L) := Group.isPerfect_def.mpr hL.2.2.1
    have h2 : IsPGroup 2 (center (Bar2 L)) :=
      CFSG.Quasithin.isPGroup_two_of_isSz (center (Bar2 L)) le_rfl
        (CFSG.CGT.Timmesfeld75.suzukiModel_of_mulEquiv e0 hn)
    haveI := CFSG.GH74.Generic.eq_bot_of_isPGroup_two_of_odd h2 (uc22p20p_odd_center_bar2 ↥L)
    obtain ⟨e1⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 (Subgroup.eq_bot_of_subsingleton _)
    exact hthin (PartTwo.S17.thin8_of_isSz (CFSG.Blueprint.LieModel.of_mulEquiv e1
      (CFSG.CGT.Timmesfeld75.lieModel_twistedB2_iff.mpr hn)))
  ·
    obtain ⟨⟨d, hv⟩, hfam, ⟨e⟩⟩ | ⟨⟨eJ⟩⟩ | ⟨⟨eA⟩⟩ :=
      h31 (BarInf L) hsimp hnab i hi (hrank.trans h1)
    · rcases hfam with ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ | ⟨q, hq, hd⟩ <;> simp only at hd <;> subst hd
      ·
        refine (hL2 ⟨q.p, q.exponent, q.prime_p, fun h9 => hq ?_, Or.inl ⟨by decide,
          CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.statedClassicalModel_psl_of_typeA
            1 q hv e⟩⟩).elim
        have h3 : q.p ∣ 3 ^ 2 := by
          rw [show (3 : ℕ) ^ 2 = 9 by norm_num, ← h9]
          exact dvd_pow_self q.p q.exponent_pos.ne'
        exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_three).1
          (q.prime_p.dvd_of_dvd_pow h3)
      ·
        refine Or.inr (Or.inr ⟨h1, Or.inl ⟨q.p, q.exponent, ?_, Or.inl ⟨by decide,
          CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.statedClassicalModel_psl_of_typeA
            2 q hv e⟩⟩⟩)
        rw [← TauCeti.PrimePower.card_def]
        exact hq
      ·
        refine Or.inr (Or.inr ⟨h1, Or.inr ⟨q.p, q.exponent, ?_, Or.inl ⟨by decide,
          CFSG.LocalAnalysis.RankThreeTheoremC.L28.OutThree.statedClassicalModel_psu_of_twistedA
            q hv e⟩⟩⟩)
        rw [← TauCeti.PrimePower.card_def]
        exact hq
    ·
      exfalso
      obtain ⟨g⟩ := CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
      exact hthin (PartTwo.S17.thin8_of_isJ1
        (uc22s216_isJ1_bar2_of_isJ1_barInf hL ⟨eJ.trans g.symm⟩))
    ·
      exact (hthin (uc22s213_thin8_of_isAlt_five hL.2.1 ⟨e0.symm.trans eA⟩)).elim
  ·
    refine Or.inr (Or.inl ⟨h2, ?_⟩)
    by_cases hSL : PartOne.Section8.IsSL3PiType (BarInf L)
    · exact Or.inr hSL
    obtain ⟨hQ, hZb⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
    have hZp : IsPGroup 3 (center (BarInf L)) := by
      rw [hZb]
      exact IsPGroup.of_bot
    obtain ⟨e⟩ := hi
    exact Or.inl (PartOne.Section8.list857_of_K33 h33
      (CFSG.Quasithin.A3.isQuasisimple_iff_open.mp hQ)
      ⟨i, ⟨((QuotientGroup.quotientMulEquivOfEq hZb).trans QuotientGroup.quotientBot).trans e⟩⟩
      hZp (hrank.trans h2) hSL)

end List

end CFSG.LocalAnalysis.UniquenessCase.UC22
