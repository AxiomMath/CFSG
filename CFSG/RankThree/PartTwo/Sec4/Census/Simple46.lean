module

public import CFSG.RankThree.PartTwo.Sec4.Census.Open46
import CFSG.RankThree.PartTwo.Sec4.Census.Witness46
import CFSG.RankThree.PartTwo.Sec4.Census.Alternating46
import CFSG.RankThree.PartTwo.Sec4.Census.Blocks46
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
import CFSG.RankThree.PartTwo.Sec4.Census.BridgeSuzuki
import CFSG.RankThree.PartTwo.Sec4.Census.Symplectic46
import CFSG.RankThree.PartTwo.Sec4.Census.Sporadic46
import CFSG.LocalAnalysis.SectionRank.NativeKGroup
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface46

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 TauCeti
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus f4TwoIndex
  localRank)

theorem isChevTwoRankTwoModel_of (hB : BridgeExceptional46) {X : Type} [Group X]
    (h : IsChevTwoRankTwo X) : IsChevTwoRankTwoModel X := by
  rcases h with h | ⟨q, hq2, hv, ⟨f⟩⟩ | ⟨q, hv, hq2, ⟨f⟩⟩ | ⟨m, hm, ⟨f⟩⟩ | ⟨m, hm, ⟨f⟩⟩ |
    ⟨ht, ⟨f⟩⟩
  · exact Or.inl h
  · exact Or.inr ⟨q.exponent, Or.inl
      (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv f (hB.g2Even q hv hq2))⟩
  · exact Or.inr ⟨q.exponent, Or.inr (Or.inl
      (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv f (hB.trialityD4 q hv hq2)))⟩
  · exact Or.inr ⟨2 * m + 1, Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.suzukiModel_of_mulEquiv f (suzukiModel_of_index m hm))))⟩
  · exact Or.inr ⟨2 * m + 1, Or.inr (Or.inr (Or.inr (Or.inl
      (CFSG.SectionRank.reeTitsModel_of_mulEquiv f (hB.reeF4 m hm)))))⟩
  · exact Or.inr ⟨1, Or.inr (Or.inr (Or.inr (Or.inr
      (CFSG.SectionRank.reeTitsModel_of_mulEquiv f (hB.tits ht)))))⟩

theorem mod_three_of_prime {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) : p % 3 = 1 ∨ p % 3 = 2 := by
  have : p % 3 ≠ 0 := fun h0 => by
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h0)
    omega
  omega

theorem mem_sporadics42not46 {s : SporadicName} (hs : s ∈ sporadics42) (hs46 : s ∉ sporadics46) :
    s ∈ sporadics42not46 := by
  revert hs hs46
  cases s <;> decide

theorem isList46_of_list42 {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (hZ : Subgroup.center X = ⊥) (hrank : localRank 3 X ≤ 2) (hW : RankThree46)
    (hB : BridgeExceptional46) (h : List42 X) : IsList46 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hno : ∀ {Y : Type} [Group Y], (X ≃* Y) → (∀ [Finite Y], 3 ≤ localRank 3 Y) → False :=
    fun e hY => false_of_three_le_localRank_three hrank e hY
  have hZ3 : Nat.card (Subgroup.center X) ≤ 3 := by
    rw [hZ, Subgroup.card_bot]
    norm_num
  rcases h with ⟨p, e, _, hp, he, ⟨f⟩⟩ | ⟨p, e, _, hp, he, he2, ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩⟩ | ⟨hr, ⟨f⟩⟩ |
    ⟨p, _, hp, ⟨q, hqp, hqf, hv, ⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩⟩ | ⟨n, hn5, hn, ⟨f⟩⟩ |
    ⟨s, hs, ⟨f⟩⟩ | h7 | h8 | h9
  · exact IsList46.one p e hp he f
  · exact IsList46.two_SL p e hp he he2 f
  · exact IsList46.two_SU p e hp he he2 f
  · exact (hno f (hW.ree27 hr)).elim
  · have hG := chevalleyExceptionalModel_G2_of_odd q hv (by omega)
    rw [hqp, hqf] at hG
    exact IsList46.three_G2 p hp (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv f hG)
  · exact IsList46.three_Sp p hp f
  · rcases mod_three_of_prime Fact.out hp with h1 | h2
    · exact (hno f (three_le_localRank_projSL_four_odd p hp h1)).elim
    · exact IsList46.three_SL p hp h2 f
  · rcases mod_three_of_prime Fact.out hp with h1 | h2
    · exact IsList46.three_SU p hp h1 f
    · exact (hno f (three_le_localRank_projSU_four_odd p hp h2)).elim
  · by_cases hn9 : n ≤ 9
    · exact IsList46.four_alt hn9 f
    · exact (hno f (three_le_localRank_alternating (by omega))).elim
  · by_cases hs46 : s ∈ sporadics46
    · have : IsSimpleGroup s.Group := f.symm.isSimpleGroup
      obtain ⟨b⟩ := nonempty_carrier_mulEquiv_of_mem46 hs46
      exact IsList46.five_spor hs46 (f.trans b.symm)
    · exact (hno f (hW.sporadic s (mem_sporadics42not46 hs hs46))).elim
  · exact IsList46.six_model (isChevTwoRankTwoModel_of hB h7)
  · rcases h8 with ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ |
      ⟨b, c, hbc, ⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · exact IsList46.seven_SL52 f
    · exact (hno f (three_le_localRank_projSU_two le_rfl (by norm_num) le_rfl
        (Or.inr (by norm_num)))).elim
    · exact (hno f (three_le_localRank_projSL_two le_rfl)).elim
    · exact (hno f (three_le_localRank_projSU_two le_rfl (by norm_num) (by norm_num)
        (Or.inl le_rfl))).elim
    · exact (hno f (three_le_localRank_projSL_two (by norm_num))).elim
    · exact IsList46.seven_Sp62 f
    · exact (hno f three_le_localRank_projSp_four_two).elim
    · exact (hno f hW.omega8PlusTwo).elim
    · exact (hno f (hW.omega8MinusTwo b c hbc)).elim
    · exact (hno f three_le_localRank_projSL_four_four).elim
    · exact (hno f three_le_localRank_projSp_three_four).elim
    · exact IsList46.seven_SU54 f
    · exact (hno f (three_le_localRank_projSU_two (by norm_num) (by norm_num) le_rfl
        (Or.inr (by norm_num)))).elim
    · exact (hno f hW.f4Two).elim
  · rcases h9 with ⟨e, he, he3, ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩ | ⟨⟨f⟩⟩
    · rcases (show e ≤ 2 ∨ e = 3 by omega) with he2 | rfl
      · exact IsList46.eight_SL3 he he2 f
      · exact (hno f (le_localRank_projSL_three (p := 3) (by norm_num) (by norm_num))).elim
    · rcases (show e ≤ 2 ∨ e = 3 by omega) with he2 | rfl
      · exact IsList46.eight_SU3 he he2 f
      · exact (hno f (le_localRank_projSU_three (p := 3) (by norm_num) (by norm_num))).elim
    · exact IsList46.eight_G23 hZ3 (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
        ((quotientCenterEquivOfEqBot hZ).trans f)
          (chevalleyExceptionalModel_G2_three ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
            g2ThreeIndex.2 rfl rfl))
    · exact IsList46.eight_SL43 f
    · exact IsList46.eight_U43 hZ3 ((quotientCenterEquivOfEqBot hZ).trans f)

end CFSG.RankThree.PartTwo.Sec4.Census
