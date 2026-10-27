module

public import CFSG.LocalAnalysis.StandardType.GGF4H1Exceptional
public import CFSG.LocalAnalysis.StandardType.GGTBXDatumResRest2
public import CFSG.LocalAnalysis.StandardType.GGTBWeylRowResRest2Cases
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylE6TwoThree
import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylTwE6Lift
import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRankExc
import CFSG.LocalAnalysis.StandardType.GGSecFiveRowMemberAux
import CFSG.LocalAnalysis.StandardType.GGTPNNonExc
import CFSG.LocalAnalysis.StandardType.GGTableBTwoThreeTorus
import CFSG.LocalAnalysis.StandardType.GGTypeANbrLabels
import CFSG.LocalAnalysis.StandardType.GGB48Assembly

public section
namespace CFSG.StandardType
open CFSG CFSG.Assembly

theorem ggF4H1_not_rowSeven {p : ℕ} {lab : LargeEvenLabel}
    (hs : LargeEvenSplit p lab) : ¬ ggRowSeven p lab lab := by
  rintro ⟨rfl, h⟩
  rcases h with rfl | rfl | rfl | rfl | rfl <;>
    norm_num [LargeEvenSplit, LargeEvenUntwisted] at hs

theorem ggF4H1_not_twE6_sub {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {lab : LargeEvenLabel} (ht : lab.tag = .twE6)
    (hs : LargeEvenSplit p lab) (hd : p ∣ 2 ^ lab.n - 1) : False := by
  have hs' : LargeEvenSplit p ⟨.twA, 2, lab.n⟩ := by
    simpa [LargeEvenSplit, LargeEvenUntwisted, ht] using hs
  exact not_split_twA_dvd_sub hp hp2 rfl hs' hd

theorem ggF4H1_large_linear_two_lift {lab : LargeEvenLabel}
    (h : lab.tag = .A ∧ 7 ≤ lab.rank ∧ lab.n = 1) :
    LargeEvenLabelAll lab fun R _ _ _ => ∃ r, 4 ≤ r ∧ GGTorusLift 3 r R := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hn⟩ := h
  dsimp only at ht hl hn
  subst ht hn
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  have hK2 : Nat.card K = 2 := by simpa using hK
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (le_refl 1) hK
  refine ⟨K, inferInstance, inferInstance, hK, hQK, (l + 1) / 2, by omega, ?_⟩
  exact TypeA.ggTorusLift_of_mulEquiv (TypeA.recipeEquiv (l + 1) K)
    (TwoThree.ggTorusLift_two hK2 (by omega))

theorem ggF4H1_no_linear_seven_two
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ lab = ⟨.A, 6, 1⟩) p Bs L)
    (h24 : Nat.card (ggAutomizer L Bs) = 24) : False := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hSlab, hN, hInd⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨rfl, rfl⟩ := hSlab
  have hHas : GGHasLabel ⟨.A, 6, 1⟩ (L ⧸ Subgroup.center L) :=
    largeEvenRawDatum_mono (fun R _ I F hQ => by
      obtain ⟨-, -, θ, -⟩ := hQ
      exact ⟨θ⟩) hraw
  have hmodel := statedClassicalModel_of_hasLabel_typeA hlab hHas
  have h48 := ggB48_of_sl_two (m := 4) (Or.inr rfl)
    hcfg.2.1 hperf hN (by simpa using hmodel)
  omega

theorem ggF4H1_no_large_linear_two
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hcard : Nat.card Bs = p ^ 4)
    (hM : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .A ∧ 7 ≤ lab.rank ∧ lab.n = 1) p Bs L) : False := by
  refine false_of_original_torusLift_ge_four hcfg hcard hM ?_
  intro lab hlab h
  obtain ⟨rfl, h⟩ := h
  exact ggF4H1_large_linear_two_lift h


section

theorem ggF4H1_no_E6_two
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hcard : Nat.card Bs = p ^ 4)
    (hM : GGInnerDiagOnLabel GGNbrNonSplitE6TwoLabel p Bs L) : False := by
  refine false_of_original_torusLift_ge_four hcfg hcard hM ?_
  intro lab hlab h
  obtain ⟨ht, hn, rfl⟩ := h
  exact (largeEvenLabelAll_torusLift_E6_two ⟨ht, hn⟩).mono
    (fun _ _ _ _ h => ⟨4, le_refl 4, h⟩)

theorem ggF4H1_residual_marking
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hM : GGInnerDiagOnLabel (fun p lab => LargeEvenSplit p lab ∧ ¬ GGTBTorCov p lab)
      p Bs L) :
    GGInnerDiagOnLabel (fun p lab => LargeEvenSplit p lab ∧ GGTBWeylRowRes p lab)
      p Bs L := by
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hSlab, hN, hInd⟩ := largeEvenRawDatum_exists hraw
  have hF4 : lab.tag ≠ .twF4 := by
    intro ht
    have hm : GGInnerDiagOnLabel (fun p lab => lab.tag = .twF4 ∧
        (p ∣ 2 ^ lab.n - 1 ∨ p ∣ 2 ^ lab.n + 1)) p Bs L := by
      refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      intro R _ I F hQ
      obtain ⟨hs, hna, θ, hP⟩ := hQ
      exact ⟨hs, hna, θ, ⟨ht, tne_halfSplit_dvd (c := True) (Or.inr ht) (Or.inl hSlab.1)⟩,
        hP.2⟩
    exact ggInndiag_pRank_le_two_twF4 hp hp2
      (ggInnerDiagOnLabel_L_pRank_ge_three hcfg hm)
  have hF4d : lab.tag ≠ .twF4der := by
    intro ht
    have hm : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twF4der) p Bs L := by
      refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
      intro R _ I F hQ
      obtain ⟨hs, hna, θ, hP⟩ := hQ
      exact ⟨hs, hna, θ, ht, hP.2⟩
    exact ggInndiag_pRank_le_two_twF4der hp hp2
      (ggInnerDiagOnLabel_L_pRank_ge_three hcfg hm)
  refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  intro R _ I F hQ
  obtain ⟨hs, hna, θ, hP⟩ := hQ
  exact ⟨hs, hna, θ, ⟨hSlab.1, hSlab.2, Or.inl hSlab.1,
    ggF4H1_not_rowSeven hSlab.1, hF4, hF4d⟩, hP.2⟩

end

section

theorem ggF4H1_no_residual_label
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hT : GGNoTransvection p Bs) (hcard : Nat.card Bs = p ^ 4)
    (hM : GGInnerDiagOnLabel (fun p lab => LargeEvenSplit p lab ∧ ¬ GGTBTorCov p lab)
      p Bs L) (h24 : Nat.card (ggAutomizer L Bs) = 24) : False := by
  have hp : p.Prime := hcfg.tableB_facts.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hlab, hraw⟩ := ggF4H1_residual_marking hcfg hM
  obtain ⟨R, _, I, F, -, -, θ, hS, hN, hInd⟩ := largeEvenRawDatum_exists hraw
  have hmark : ∀ (T : ℕ → LargeEvenLabel → Prop), T p lab →
      GGInnerDiagOnLabel T p Bs L := by
    intro T ht
    refine ⟨hperf, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
    intro R _ I F hQ
    obtain ⟨hs, hna, θ, hP⟩ := hQ
    exact ⟨hs, hna, θ, ht, hP.2⟩
  by_cases hU : GGUnitDvd63Label p lab
  · exact no_original_unitSix_at_card_four hcfg (hmark _ hU) hcard
  have hrest : GGTBWeylRowResRest p lab := by
    refine ⟨hS.2, ?_⟩
    rintro ⟨ht, hr, hp3, hd⟩
    apply hU
    refine ⟨⟨ht, by omega, by simpa [hp3] using hd, ?_⟩, hr, hp3⟩
    rw [hr, hp3]
    norm_num
  by_cases hsmall : GGTBResSmallLabel p lab
  · exact ggTBWeylRowResRest_small_false_L hcfg (hmark _ ⟨hrest, hsmall⟩)
  have hcases := ggTBWeylRowResRest2_cases hp hp2 hlab ⟨hrest, hsmall⟩
  rcases hcases with hlin | hF4 | hE6 | htw | htw
  · by_cases hr : lab.rank = 6
    · have heq : lab = ⟨.A, 6, 1⟩ := by
        rcases lab with ⟨t, l, n⟩
        obtain ⟨ht, hl, hn, hp3⟩ := hlin
        dsimp only at ht hr hn
        subst ht hr hn
        rfl
      exact ggF4H1_no_linear_seven_two hcfg (hmark _ ⟨hlin.2.2.2, heq⟩) h24
    · exact ggF4H1_no_large_linear_two hcfg hcard
        (hmark _ ⟨hlin.2.2.2, hlin.1, by omega, hlin.2.2.1⟩)
  · exact no_original_f4Three_at_card_four hcfg hT (hmark _ hF4) hcard
  · exact ggF4H1_no_E6_two hcfg hcard (hmark _ hE6)
  · exact ggF4H1_not_twE6_sub hp hp2 htw.1 hS.1 (by simpa [htw.2.1] using htw.2.2)
  · refine false_of_original_torusLift_ge_four hcfg hcard (hmark GGTwE6BadLabel htw) ?_
    intro lab' hlab' htw'
    have hd : p ∣ 2 ^ lab'.n + 1 := by simpa [htw'.2.1] using htw'.2.2
    exact (largeEvenLabelAll_torusLift_twE6Add_holds hp hlab' ⟨htw'.1, hd⟩).mono
      (fun _ _ _ _ h => ⟨TwE6Delta.liftRank p, by
        simp [htw'.2.1, TwE6Delta.liftRank_three], h⟩)

end
end CFSG.StandardType
end
