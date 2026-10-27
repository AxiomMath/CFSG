module

public import CFSG.LocalAnalysis.StandardType.GGRealKGThree
public import CFSG.LocalAnalysis.StandardType.GGRealKGThreeLin
public import CFSG.LocalAnalysis.StandardType.GGRealKGLinNsRoot
public import CFSG.LocalAnalysis.StandardType.GGRealKGSpRoot
public import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaRow
public import CFSG.LocalAnalysis.StandardType.GGRealKGUSplitRoot
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerNinePGL
public import CFSG.LocalAnalysis.StandardType.GGKGForkSmallRow
public import CFSG.LocalAnalysis.StandardType.Marking
public import CFSG.LocalAnalysis.StandardType.MarkingClassical
public import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
public import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ChevSimple

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly


theorem ggRealKGThreeRow_aNonsplit : GGRealKGThreeRow .aNonsplit := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨hp3, ⟨htag, hpn, -⟩, -⟩ := hs
  subst hp3
  have hM := SCFourCover.largeEvenLabelAll_markedModel_classical hlab (Or.inl htag) Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hl1 : 1 ≤ l := hlab.2.1
  dsimp only [LargeEvenRawDatum] at hM ⊢
  obtain ⟨K, _, _, hK, hQ', hmark⟩ := hM
  have hF4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact four_le_two_pow hl.2.1
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusRootSL2_aNonsplit hp (by norm_num) hF4 hK hpn (by omega) hmark⟩

theorem ggRealKGThreeRow_aNonsplitDvd : GGRealKGThreeRow .aNonsplitDvd := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨hp3, ⟨htag, hpn, -⟩, -⟩ := hs
  subst hp3
  have hM := SCFourCover.largeEvenLabelAll_markedModel_classical hlab (Or.inl htag) Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hl1 : 1 ≤ l := hlab.2.1
  dsimp only [LargeEvenRawDatum] at hM ⊢
  obtain ⟨K, _, _, hK, hQ', hmark⟩ := hM
  have hF4 : 4 ≤ Nat.card K := by
    rw [hK]
    exact four_le_two_pow hl.2.1
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusRootSL2_aNonsplit hp (by norm_num) hF4 hK hpn (by omega) hmark⟩

theorem ggRealKGThreeRow_spNonsplit : GGRealKGThreeRow .spNonsplit := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨hp3, ⟨htag, hpn⟩, -⟩ := hs
  subst hp3
  have hM := SCFourCover.largeEvenLabelAll_markedModel_classical hlab
    (by rcases htag with h | h <;> simp [h]) Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  rcases htag with rfl | rfl <;>
  · have hl2 : 2 ≤ l := hlab.2.1
    dsimp only [LargeEvenRawDatum] at hM ⊢
    obtain ⟨K, _, _, hK, hQ', hmark⟩ := hM
    have hF4 : 4 ≤ Nat.card K := by
      rw [hK]
      exact four_le_two_pow hl.2.1
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusRootSL2_spNonsplit hp (by norm_num) hF4 hK hpn hl2 hmark⟩

theorem ggRealKGThreeRow_dNonsplit : GGRealKGThreeRow .dNonsplit := by
  intro p lab hp hlab hl hs
  obtain ⟨hp3, ⟨htag, hpn⟩, -⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hl3 : 3 ≤ l := hlab.2
  rcases (show l = 3 ∨ 4 ≤ l by omega) with rfl | hl4
  · have hp4 : ¬ (3 : ℕ) ∣ 3 + 1 := by norm_num
    have hA' : ¬ GGTypeALabel 3 ⟨.A, 3, n⟩ := by
      rintro (⟨-, h1, -⟩ | ⟨h, -⟩ | ⟨h, -⟩)
      · have hsub : (3 : ℕ) ∣ (2 ^ n + 1) - (2 ^ n - 1) := Nat.dvd_sub hpn h1
        have heq : (2 ^ n + 1) - (2 ^ n - 1) = 2 := by
          have := Nat.one_le_two_pow (n := n)
          omega
        rw [heq] at hsub
        norm_num at hsub
      · cases h
      · cases h
    exact ggRealKGThreeRow_aNonsplit 3 ⟨.A, 3, n⟩ hp
      ⟨hlab.1, by norm_num, by norm_num⟩ hl ⟨rfl, ⟨rfl, hpn, hp4⟩, hA'⟩
  · intro Q hQ
    have hM := SCFourCover.largeEvenLabelAll_markedModel_classical hlab (by simp) Q hQ
    dsimp only [LargeEvenRawDatum] at hM ⊢
    split_ifs at hM ⊢ with h3
    · omega
    · obtain ⟨K, _, _, hK, hQ', hmark⟩ := hM
      have hF4 : 4 ≤ Nat.card K := by
        rw [hK]
        exact four_le_two_pow hl.2.1
      exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusRootSL2_dNonsplit hp
        (by norm_num) hF4 hK hpn hl4
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
          (isChevTwo_of_markedModel hmark))⟩

theorem ggRealKGThreeRow_twdNonsplit : GGRealKGThreeRow .twdNonsplit := by
  intro p lab hp hlab hl hs
  obtain ⟨hp3, ⟨htag, hpn⟩, hA⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hl2 : 2 ≤ l := hlab.2
  rcases (show l = 2 ∨ l = 3 ∨ 4 ≤ l by omega) with rfl | rfl | hl4
  · refine (hA (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))).elim
    rw [show (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) by
      rw [← Nat.sq_sub_sq, one_pow]]
    exact Dvd.dvd.mul_right hpn _
  · exact ggRealKGThreeRow_uNonsplit 3 ⟨.twA, 3, n⟩ hp
      ⟨hlab.1, by norm_num, by norm_num⟩ hl
      ⟨rfl, ⟨rfl, hpn, by norm_num⟩, fun h => by
        rcases h with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> cases h⟩
  · intro Q hQ
    have hn : 1 ≤ n := hlab.1
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    split_ifs at hQ ⊢ with h2 h3
    · omega
    · omega
    · obtain ⟨K, _, _, hK, b, c, hbc, hQ'⟩ := hQ
      have hmark : MarkedModel ⟨.twD, l, n⟩ (OrthRest.RMinus K (l - 1) b c) := by
        simp only [MarkedModel, markTag, markRank, markChar, markDeg, h2, h3, if_false]
        exact Or.inl ⟨by decide, statedClassicalModel_omegaMinus l n hK b c hbc
          ⟨Nat.prime_two, hn, hl4⟩⟩
      have hF4 : 4 ≤ Nat.card K := by
        rw [hK]
        exact four_le_two_pow hl.2.1
      exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ',
        ggTorusRootSL2_twdNonsplit hp (by norm_num) hF4 hK hpn (by omega : 3 ≤ l - 1) hbc
          (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
            (isChevTwo_of_markedModel hmark))⟩

theorem ggRealKGThreeRow_uSplit : GGRealKGThreeRow .uSplit := by
  intro p lab hp hlab hl hs Q hQ
  obtain ⟨hp3, ⟨htag, hpn, hpl⟩, -⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hpl
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hn2 : 2 ≤ n := hl.2.1
  have hl2 : 2 ≤ l := hlab.2.1
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have hmark : MarkedModel ⟨.twA, l, n⟩
      (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) := by
    simp only [MarkedModel, markTag, markRank, markChar, markDeg]
    refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
      ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
    have h2 : 2 ^ n = 2 ^ 1 := congrArg Prod.snd h
    have := Nat.pow_right_injective le_rfl h2
    omega
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggTorusRootSL2_uSplit hp (by norm_num) (fun _ hpd => hpl hpd) hK hn hpn (by omega)
      (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
        (isChevTwo_of_markedModel hmark))⟩

theorem ggRealKGThreeRow_uSplitDvd : GGRealKGThreeRow .uSplitDvd := by
  intro p lab hp hlab hl hs
  obtain ⟨hp3, ⟨htag, hpn, -⟩, -⟩ := hs
  subst hp3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hn : 1 ≤ n := hlab.1
  have hn2 : 2 ≤ n := hl.2.1
  have hl2 : 2 ≤ l := hlab.2.1
  rcases (show l = 2 ∨ 3 ≤ l by omega) with rfl | hl3
  · intro Q hQ
    obtain ⟨K, i1, i2, hK, hQ', hpc⟩ :=
      largeEvenLabelAll_card_lt_unitaryThree_all (lab := ⟨.twA, 2, n⟩)
        hp (by norm_num) hlab rfl rfl Q hQ
    have hmark : MarkedModel ⟨.twA, 2, n⟩
        (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) := by
      simp only [MarkedModel, markTag, markRank, markChar, markDeg]
      refine Or.inl ⟨by decide, statedClassicalModel_unitary 3 n hK
        ⟨Nat.prime_two, hn, by norm_num, fun h => ?_⟩⟩
      have h2 : 2 ^ n = 2 ^ 1 := congrArg Prod.snd h
      have := Nat.pow_right_injective le_rfl h2
      omega
    have hS : IsSimpleGroup (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) :=
      CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.isSimpleGroup_of_isChevSimple_two
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
          (isChevTwo_of_markedModel hmark))
    have hnc : ∃ a b : LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)),
        a * b ≠ b * a := by
      have := hS.toNontrivial
      obtain ⟨x, hx⟩ := exists_ne (1 : LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n)))
      by_contra hcon
      push Not at hcon
      apply hx
      have hxc : x ∈ Subgroup.center
          (LargeEvenProj (LargeEvenSUGroup (Fin 3) K (2 ^ n))) :=
        Subgroup.mem_center_iff.mpr fun z => hcon z x
      have hdq : (3, 2 ^ n) ≠ (3, 2) := by
        intro heq
        have h2 : 2 ^ n = 2 ^ 1 := congrArg Prod.snd heq
        have := Nat.pow_right_injective le_rfl h2
        omega
      rw [TableBUE.center_proj_eq_bot hK (by norm_num) hdq] at hxc
      exact Subgroup.mem_bot.mp hxc
    have := (TableBU.unitaryFieldData_of_card hK hn).charP
    refine ⟨K, i1, i2, hK, hQ', 0,
      TypeA.ggTorusLift_zero (two_dvd_card_statedProj_statedSU (d := 3) (f := n) (K := K)
        (by norm_num)), ?_⟩
    intro L' _ _ ψ A hA
    exact (ggTorusTBGroup_false_of_card_lt (hpc hS hnc) hA).elim
  · intro Q hQ
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    have hmark : MarkedModel ⟨.twA, l, n⟩
        (LargeEvenProj (LargeEvenSUGroup (Fin (l + 1)) K (2 ^ n))) := by
      simp only [MarkedModel, markTag, markRank, markChar, markDeg]
      refine Or.inl ⟨by decide, statedClassicalModel_unitary (l + 1) n hK
        ⟨Nat.prime_two, hn, by omega, fun h => ?_⟩⟩
      have h2 : 2 ^ n = 2 ^ 1 := congrArg Prod.snd h
      have := Nat.pow_right_injective le_rfl h2
      omega
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggTorusRootSL2_uSplit hp (by norm_num) (fun h _ => by omega) hK hn hpn (by omega)
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
          (isChevTwo_of_markedModel hmark))⟩

end CFSG.StandardType

end
