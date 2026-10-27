module

public import CFSG.LocalAnalysis.StandardType.GGRealKG
public import CFSG.LocalAnalysis.StandardType.GGKGForkRows
public import CFSG.LocalAnalysis.StandardType.GGKGForkLayerGen
import CFSG.LocalAnalysis.StandardType.GGRealKGOmegaRoot
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
import CFSG.LocalAnalysis.StandardType.GGKGForkOrthRow
import CFSG.LocalAnalysis.StandardType.GGKGForkLatticeElt
import CFSG.LocalAnalysis.StandardType.GGTableBTypeATorus
import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
import CFSG.LocalAnalysis.StandardType.GGKnownInputsNoU6Classical
import CFSG.LocalAnalysis.StandardType.MarkingClassical
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1315b
import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622K3ChevSimple
import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG CFSG.Assembly OrthNs OrthExc CFSG.Yardstones.Md0ec50421ce4
open CFSG.RankThree.Classical2 (orthDerived)

private theorem isChevSimple_of_mulEquiv_orth {r : ℕ} {A B : Type} [Group A] [Group B]
    (e : A ≃* B) (h : IsChevSimple r B) : IsChevSimple r A := by
  rcases h with ⟨i, hi, ⟨f⟩⟩ | ⟨i, hi, ⟨f⟩⟩
  · exact Or.inl ⟨i, hi, ⟨e.trans f⟩⟩
  · exact Or.inr ⟨i, hi, ⟨e.trans f⟩⟩

private theorem ggKGRootDatum_orthDerived
    {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] {Q : QuadraticForm F V} (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card F + 1) (hF4 : 4 ≤ Nat.card F)
    {ℓ : ℕ} (hdim : Module.finrank F V = 2 * ℓ) (hℓ : 4 ≤ ℓ) [Finite ↥(orthDerived Q)]
    (hchev : IsChevSimple 2 ↥(orthDerived Q)) : GGKGRootDatum p 0 ↥(orthDerived Q) := by
  have hS : IsSimpleGroup ↥(orthDerived Q) :=
    CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.isSimpleGroup_of_isChevSimple_two hchev
  intro E hE _ _ hsc
  refine RealKGOmega.ggKGRootDatumAt_orthDerived hQ hp hp2 hpq hF4 hdim hℓ hE hsc
    fun a ha J hJ hJa => ?_
  by_cases hJb : J = ⊥
  · rw [hJb]
    exact bot_le
  have hnc : ∃ a b : ↥(orthDerived Q), a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply hJb
    rw [← hJ, eq_bot_iff]
    exact Subgroup.commutator_le.mpr fun x _ y _ => by
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hcon x y
  exact ggKG_layer_of_chevSimple hS hnc hchev hp hp2 (hE.2 a ha) hJ hJa

theorem ggTorusRootSL2_dNonsplit
    {K : Type} [Field K] [Finite K] {n l p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF4 : 4 ≤ Nat.card K) (hK : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1) (hl4 : 4 ≤ l)
    (hchevR : IsChevSimple 2 (OrthRest.RPlus K l)) :
    ∃ r, GGTorusLift p r (OrthRest.RPlus K l) ∧
      GGTorusRootSL2 p r (OrthRest.RPlus K l) (LargeEvenInnSet _) := by
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  obtain ⟨hZ, hcp⟩ := center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
  refine ⟨0, TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_plus hl4),
    ggTorusRootSL2_of_rootDatum hp (fun φ hφ _ => hφ) hZ hcp ?_⟩
  let α := OrthTorus.rPlusEquiv K (by omega : 1 ≤ l)
  haveI : Finite ↥(orthDerived (TableBOrth.qPlusForm K l)) := Finite.of_equiv _ α.toEquiv
  refine ggKGRootDatum_of_mulEquiv α (ggKGRootDatum_orthDerived
    (TableBOrth.nondegenerate_qPlusForm (K := K) l) hp hp2 hpK hF4 (ℓ := l) ?_ hl4
    (isChevSimple_of_mulEquiv_orth α.symm hchevR))
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  ring

theorem ggTorusRootSL2_twdNonsplit
    {K : Type} [Field K] [Finite K] {n m p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hF4 : 4 ≤ Nat.card K) (hK : Nat.card K = 2 ^ n) (hpn : p ∣ 2 ^ n + 1) (hm : 3 ≤ m)
    {b c : K}
    (hbc : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hchevR : IsChevSimple 2 (OrthRest.RMinus K m b c)) :
    ∃ r, GGTorusLift p r (OrthRest.RMinus K m b c) ∧
      GGTorusRootSL2 p r (OrthRest.RMinus K m b c) (LargeEvenInnSet _) := by
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
  obtain ⟨hZ, hcp⟩ := center_data_omegaMinus (K := K) hp hp2 hm hbc
  refine ⟨0, TypeA.ggTorusLift_zero (ggKGOrth_two_dvd_card_minus hm b c hbc),
    ggTorusRootSL2_of_rootDatum hp (fun φ hφ _ => hφ) hZ hcp ?_⟩
  let α := OrthTorus.rMinusEquiv K m b c
  haveI : Finite ↥(orthDerived (TableBOrth.qMinusForm K m b c)) := Finite.of_equiv _ α.toEquiv
  refine ggKGRootDatum_of_mulEquiv α (ggKGRootDatum_orthDerived
    (TableBOrth.nondegenerate_qMinusForm m hbc) hp hp2 hpK hF4 (ℓ := m + 1) ?_ (by omega)
    (isChevSimple_of_mulEquiv_orth α.symm hchevR))
  simp only [Module.finrank_fintype_fun_eq_card, LargeEvenMinusIdx, Fintype.card_sum,
    Fintype.card_fin]
  ring

theorem ggRealRootSL2On_dNonsplit_four :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .dNonsplit p lab ∧ 4 ≤ lab.rank := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp5, ⟨htag, hpn⟩, hl4⟩ := hs
  have hM := SCFourCover.largeEvenLabelAll_markedModel_classical hlab (by simp [htag]) Q hQ
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hl4
  subst htag
  dsimp only [LargeEvenRawDatum] at hM ⊢
  split_ifs at hM ⊢ with h3
  · omega
  · obtain ⟨K, _, _, hK, hQ', hmark⟩ := hM
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have hp2 : p ≠ 2 := by omega
    have hF4 : 4 ≤ Nat.card K := by
      have := Nat.le_of_dvd (by omega) hpK
      omega
    exact ⟨K, inferInstance, inferInstance, hK, hQ', ggTorusRootSL2_dNonsplit hp hp2 hF4 hK hpn
      hl4 (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
        (isChevTwo_of_markedModel hmark))⟩

theorem ggRealRootSL2On_twdNonsplit_four :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .twdNonsplit p lab ∧ 4 ≤ lab.rank := by
  intro p lab hp hlab _ hs Q hQ
  obtain ⟨hp5, ⟨htag, hpn⟩, hl4⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn hl4
  subst htag
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
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpn
    have hp2 : p ≠ 2 := by omega
    have hF4 : 4 ≤ Nat.card K := by
      have := Nat.le_of_dvd (by omega) hpK
      omega
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hQ',
      ggTorusRootSL2_twdNonsplit hp hp2 hF4 hK hpn (by omega : 3 ≤ l - 1) hbc
        (CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1315b.isChevSimple_two_of_isChevTwo
          (isChevTwo_of_markedModel hmark))⟩

theorem ggRealRootSL2On_twdNonsplit_ne_three :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .twdNonsplit p lab ∧ lab.rank ≠ 3 := by
  intro p lab hp hlab hl hs
  obtain ⟨hp5, ⟨htag, hpn⟩, h3⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn h3
  subst htag
  have hl2 : 2 ≤ l := hlab.2
  rcases (show l = 2 ∨ 4 ≤ l by omega) with rfl | hl4
  · refine ggRealRootSL2On_typeA p _ hp hlab hl (Or.inr (Or.inr ⟨rfl, rfl, ?_⟩))
    rw [show (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) by rw [← Nat.sq_sub_sq, one_pow]]
    exact Dvd.dvd.mul_right hpn _
  · exact ggRealRootSL2On_twdNonsplit_four p _ hp hlab hl ⟨hp5, ⟨rfl, hpn⟩, hl4⟩

theorem ggRealRootSL2On_dNonsplit_of_aNonsplit
    (hA : GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .aNonsplit p lab) :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .dNonsplit p lab := by
  intro p lab hp hlab hl hs
  obtain ⟨hp5, ⟨htag, hpn⟩⟩ := hs
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htag hpn
  subst htag
  have hl3 : 3 ≤ l := hlab.2
  rcases (show l = 3 ∨ 4 ≤ l by omega) with rfl | hl4
  · have hp4 : ¬ p ∣ 3 + 1 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    exact hA p ⟨.A, 3, n⟩ hp ⟨hlab.1, by norm_num, by norm_num⟩ hl ⟨hp5, rfl, hpn, hp4⟩
  · exact ggRealRootSL2On_dNonsplit_four p _ hp hlab hl ⟨hp5, ⟨rfl, hpn⟩, hl4⟩

theorem ggRealRootSL2On_twdNonsplit_of_uNonsplit
    (hU : GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .uNonsplit p lab) :
    GGRealRootSL2On fun p lab => 5 ≤ p ∧ GGKGRowLabel .twdNonsplit p lab := by
  intro p lab hp hlab hl hs
  obtain ⟨hp5, ⟨htag, hpn⟩⟩ := hs
  by_cases h3 : lab.rank = 3
  · obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hpn h3
    subst htag h3
    have hp4 : ¬ p ∣ 3 + 1 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    exact hU p ⟨.twA, 3, n⟩ hp ⟨hlab.1, by norm_num, by norm_num⟩ hl ⟨hp5, rfl, hpn, hp4⟩
  · exact ggRealRootSL2On_twdNonsplit_ne_three p lab hp hlab hl ⟨hp5, ⟨htag, hpn⟩, h3⟩

end CFSG.StandardType

end
