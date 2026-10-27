module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFact1916Census
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
import CFSG.Blueprint.LieModelAPI
import CFSG.Adapters.RankThreeOutcomesReverse
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Small
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Sec19.Census194.Basic
import CFSG.RankThree.PartTwo.Sec19.Census194.RankOne
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194Core
import CFSG.RankThree.PartTwo.Sec19.Census194.Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916

open CFSG CFSG.Open CFSG.Blueprint
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open CFSG.AGLEmbedding (IsClassicalTwoOrG2 IsSmallTwoOrG2)
open CFSG.RankThree.PartTwo.Sec19
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

theorem not_rankOne_quotient_center {Y : Type} [Group Y] [Finite Y] (h2 : CFSG.pCore 2 Y = ⊥)
    {J : Subgroup Y} {T : Sylow 2 Y} (hJ : J ≠ ⊤)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J)
    (hcard : Nat.card (CFSG.Open.pCoreOf 2 J) ≠ Nat.card T) :
    (∀ f : ℕ, ¬ StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 2 f) ∧
    (∀ f : ℕ, ¬ StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU 3 2 f) ∧
    IsEmpty (Y ⧸ Subgroup.center Y ≃* alternatingGroup (Fin 5)) := by
  have hodd : Odd (Nat.card (Subgroup.center Y)) := odd_card_center_of_pCore_eq_bot h2
  have hJne : J ≠ Subgroup.normalizer ((T : Subgroup Y) : Set Y) := by
    intro hJN
    apply hcard
    rw [hJN]
    exact card_pCoreOf_normalizer_sylow T
  obtain ⟨T', J', hJ'top, hNJ', hJ'ne⟩ :=
    exists_overgroup_quotient_center T hodd hJ hNJ hJne
  refine ⟨fun f hm => ?_, fun f hm => ?_, ⟨fun e => ?_⟩⟩
  · rcases eq_normalizer_or_top_psl_two hm T' J' hNJ' with h | h
    · exact hJ'ne h
    · exact hJ'top h
  · rcases eq_normalizer_or_top_psu_three hm T' J' hNJ' with h | h
    · exact hJ'ne h
    · exact hJ'top h
  · rcases eq_normalizer_or_top_alt_five ⟨e⟩ T' J' hNJ' with h | h
    · exact hJ'ne h
    · exact hJ'top h

private theorem list19_16_5_of_isLieOf_A {Y : Type} [Group Y] [Finite Y]
    (hR : RankHyp1916 Y) (hA : Census1916SurvPSL)
    (h1 : ∀ f : ℕ, ¬ StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSL 2 2 f)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A r q).Valid)
    (hq : q.p = 2) (e : (Y ⧸ Subgroup.center Y) ≃*
      (TauCeti.CFSGIndex.lie ⟨.A r q, hv⟩).Group) :
    List19_16_5 (Y ⧸ Subgroup.center Y) := by
  have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
  rw [hq] at hm
  have hn2 : 2 ≤ r + 1 := hm.1.2.2.1
  obtain ⟨n, hn⟩ : ∃ n, n = r + 1 := ⟨_, rfl⟩
  rw [← hn] at hm hn2
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · obtain rfl | rfl : n = 2 ∨ n = 3 := by omega
    · exact (h1 q.exponent hm).elim
    · have hmL : LieModel (Y ⧸ Subgroup.center Y) .PSL 3 2 q.exponent :=
        (LieModel.classical_iff (t := .PSL) (n := 3) (p := 2) (f := q.exponent)
          (by decide)).2 hm
      exact Or.inl (Or.inl ⟨q.exponent, Or.inr (Or.inl hmL)⟩)
  · rcases Nat.lt_or_ge n 5 with h4 | h5
    · obtain rfl : n = 4 := by omega
      have hmL : LieModel (Y ⧸ Subgroup.center Y) .PSL 4 2 q.exponent :=
        (LieModel.classical_iff (t := .PSL) (n := 4) (p := 2) (f := q.exponent)
          (by decide)).2 hm
      exact Or.inl (Or.inl ⟨q.exponent, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmL))))⟩)
    · obtain ⟨hf, hn7⟩ := hA Y n q.exponent hR hm h5
      rw [hf] at hm
      have hmL : LieModel (Y ⧸ Subgroup.center Y) .PSL n 2 1 :=
        (LieModel.classical_iff (t := .PSL) (n := n) (p := 2) (f := 1) (by decide)).2 hm
      exact Or.inl (Or.inr ⟨n, h5, hn7, hmL⟩)

private theorem list19_16_5_of_isLieOf_twistedA {Y : Type} [Group Y] [Finite Y]
    (hR : RankHyp1916 Y) (hU : Census1916SurvPSU)
    (h3 : ∀ f : ℕ, ¬ StatedClassicalModel (Y ⧸ Subgroup.center Y) .PSU 3 2 f)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedA r q).Valid)
    (hq : q.p = 2) (e : (Y ⧸ Subgroup.center Y) ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    List19_16_5 (Y ⧸ Subgroup.center Y) := by
  have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
  rw [hq] at hm
  have hn3 : 3 ≤ r + 1 := hm.1.2.2.1
  obtain ⟨n, hn⟩ : ∃ n, n = r + 1 := ⟨_, rfl⟩
  rw [← hn] at hm hn3
  rcases Nat.lt_or_ge n 4 with hlt | hge
  · obtain rfl : n = 3 := by omega
    exact (h3 q.exponent hm).elim
  · rcases Nat.lt_or_ge n 5 with h4 | h5
    · obtain rfl : n = 4 := by omega
      have hmL : LieModel (Y ⧸ Subgroup.center Y) .PSU 4 2 q.exponent :=
        (LieModel.classical_iff (t := .PSU) (n := 4) (p := 2) (f := q.exponent)
          (by decide)).2 hm
      exact Or.inl (Or.inl ⟨q.exponent, Or.inr (Or.inr (Or.inr (Or.inl hmL)))⟩)
    · obtain ⟨hn5, hf2⟩ := hU Y n q.exponent hR hm h5
      rw [hn5, hf2] at hm
      have hmL : LieModel (Y ⧸ Subgroup.center Y) .PSU 5 2 2 :=
        (LieModel.classical_iff (t := .PSU) (n := 5) (p := 2) (f := 2) (by decide)).2 hm
      exact Or.inr (Or.inr (Or.inr hmL))

private theorem list19_16_5_of_isLieOf_B {Y : Type} [Group Y] [Finite Y]
    (hR : RankHyp1916 Y) (hB : Census1916SurvPSp)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.B r q).Valid)
    (hq : q.p = 2) (e : (Y ⧸ Subgroup.center Y) ≃*
      (TauCeti.CFSGIndex.lie ⟨.B r q, hv⟩).Group) :
    List19_16_5 (Y ⧸ Subgroup.center Y) := by
  have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
  by_cases h2' : r = 2
  · subst h2'
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
    rw [hq] at hm
    have hmL : LieModel (Y ⧸ Subgroup.center Y) .PSp 2 2 q.exponent :=
      (LieModel.classical_iff (t := .PSp) (n := 2) (p := 2) (f := q.exponent)
        (by decide)).2 hm
    exact Or.inl (Or.inl ⟨q.exponent, Or.inr (Or.inr (Or.inl hmL))⟩)
  · rcases Nat.lt_or_ge r 4 with h3 | h4
    · obtain rfl : r = 3 := by omega
      have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even 3 q hv hq
        (by omega) e
      rw [hq] at hm
      have hmL : LieModel (Y ⧸ Subgroup.center Y) .PSp 3 2 q.exponent :=
        (LieModel.classical_iff (t := .PSp) (n := 3) (p := 2) (f := q.exponent)
          (by decide)).2 hm
      exact Or.inl (Or.inl ⟨q.exponent, Or.inr (Or.inr (Or.inr (Or.inr
        (Or.inr (Or.inl hmL)))))⟩)
    · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hq
        (by omega) e
      rw [hq] at hm
      exact (hB Y r q.exponent hR hm h4).elim

private theorem list19_16_5_of_isLieOf_D {Y : Type} [Group Y] [Finite Y]
    (hR : RankHyp1916 Y) (hD : Census1916SurvPOmegaPlus)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.D r q).Valid)
    (hq : q.p = 2) (e : (Y ⧸ Subgroup.center Y) ≃*
      (TauCeti.CFSGIndex.lie ⟨.D r q, hv⟩).Group) :
    List19_16_5 (Y ⧸ Subgroup.center Y) := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hq e
  rw [hq] at hm
  exact (hD Y r q.exponent hR hm).elim

private theorem list19_16_5_of_isLieOf_twistedD {Y : Type} [Group Y] [Finite Y]
    (hR : RankHyp1916 Y) (h2D : Census1916SurvPOmegaMinus)
    {r : ℕ} {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.twistedD r q).Valid)
    (hq : q.p = 2) (e : (Y ⧸ Subgroup.center Y) ≃*
      (TauCeti.CFSGIndex.lie ⟨.twistedD r q, hv⟩).Group) :
    List19_16_5 (Y ⧸ Subgroup.center Y) := by
  have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv hq e
  rw [hq] at hm
  have hr4 : 4 ≤ r := hm.1.2.2
  rcases Nat.lt_or_ge r 5 with hlt | hge
  · obtain rfl : r = 4 := by omega
    have hmL : LieModel (Y ⧸ Subgroup.center Y) .POmegaMinus 4 2 q.exponent :=
      (LieModel.classical_iff (t := .POmegaMinus) (n := 4) (p := 2) (f := q.exponent)
        (by decide)).2 hm
    exact Or.inl (Or.inl ⟨q.exponent, Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr hmL)))))⟩)
  · exact (h2D Y r q.exponent hR hm hge).elim

theorem list19_16_5_of_isLieOf_g2
    {X : Type} [Group X] {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.G2 q).Valid)
    (hq : q.p = 2) (e : X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hv⟩).Group) :
    List19_16_5 X := by
  have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  have hce : ChevalleyExceptionalModel X .G2 q.p q.exponent :=
    ⟨⟨q.prime_p, q.exponent_pos, rfl, by
      simpa only [TauCeti.LieTypeIndex.inStandardRange_iff, TauCeti.PrimePower.card_def]
        using hrange⟩,
      CFSG.TauCetiBridge.Even.untwistedModel_of_bridgeEven
        CFSG.TauCetiBridge.Even.untwistedBridgeEven_G2 q hv hq e⟩
  rw [hq] at hce
  have hm : LieModel X .G2 0 2 q.exponent :=
    (LieModel.chevalleyExceptional_iff (t := .G2) (n := 0) (p := 2) (f := q.exponent)
      (by decide)).2 ⟨rfl, hce⟩
  exact Or.inl (Or.inl ⟨q.exponent, Or.inl hm⟩)

theorem list19_16_5_of_isSmallTwoOrG2 {X : Type} [Group X]
    (h5 : IsEmpty (X ≃* alternatingGroup (Fin 5))) (hS : IsSmallTwoOrG2 X) :
    List19_16_5 X := by
  rcases hS with ⟨n, hn, ⟨e⟩⟩ | ⟨⟨d, hv⟩, hd, ⟨e⟩⟩
  · rcases hn with rfl | rfl | rfl
    · exact (h5.false e).elim
    · exact Or.inr (Or.inl ⟨e⟩)
    · have hm := statedPSL_four_two_of_eight e
      have hmL : LieModel X .PSL 4 2 1 :=
        (LieModel.classical_iff (t := .PSL) (n := 4) (p := 2) (f := 1) (by decide)).2 hm
      exact Or.inl (Or.inl ⟨1, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hmL))))⟩)
  · rcases hd with ⟨q, hqcard, rfl⟩ | ⟨q, hqcard, rfl⟩
    · have hm0 := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
      obtain ⟨hp7, hf1⟩ := pe_of_card_prime (by norm_num : Nat.Prime 7) q hqcard
      have hm : StatedClassicalModel X .PSL 2 7 1 := by
        rw [hp7, hf1] at hm0
        exact hm0
      obtain ⟨eL⟩ := nonempty_projSL_three_two_of_psl_two_seven hm
      have hm3 : StatedClassicalModel X .PSL 3 2 1 :=
        CFSG.Assembly.RankThreeEven.statedClassicalModel_of_projSL
          ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩ eL
      have hmL : LieModel X .PSL 3 2 1 :=
        (LieModel.classical_iff (t := .PSL) (n := 3) (p := 2) (f := 1) (by decide)).2 hm3
      exact Or.inl (Or.inl ⟨1, Or.inr (Or.inl hmL)⟩)
    · have hm0 := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hv e
      obtain ⟨hp3, hf1⟩ := pe_of_card_prime Nat.prime_three q hqcard
      have hm : StatedClassicalModel X .PSU 3 3 1 := by
        rw [hp3, hf1] at hm0
        exact hm0
      have hmL : LieModel X .PSU 3 3 1 :=
        (LieModel.classical_iff (t := .PSU) (n := 3) (p := 3) (f := 1) (by decide)).2 hm
      exact Or.inr (Or.inr (Or.inl hmL))

theorem k_19_16_census_of_nodes
    (hA : Census1916SurvPSL) (hU : Census1916SurvPSU) (hB : Census1916SurvPSp)
    (hD : Census1916SurvPOmegaPlus) (h2D : Census1916SurvPOmegaMinus) :
    K_19_16_census := by
  intro Y _ _ hY h2 hcl hq J T hJ hNJ hcard
  have hR : RankHyp1916 Y := ⟨hY, h2, hq⟩
  have hR1 := not_rankOne_quotient_center (Y := Y) h2 hJ hNJ hcard
  rcases CFSG.AGLEmbedding.isClassicalTwoOrG2_family_cases hcl with
    hA' | hU' | hB' | hD' | h2D' | hG' | hS'
  · obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hA'
    cases d with
    | A r q => exact list19_16_5_of_isLieOf_A hR hA hR1.1 hv hd e
    | _ => exact hd.elim
  · obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hU'
    cases d with
    | twistedA r q => exact list19_16_5_of_isLieOf_twistedA hR hU hR1.2.1 hv hd e
    | _ => exact hd.elim
  · obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hB'
    cases d with
    | B r q => exact list19_16_5_of_isLieOf_B hR hB hv hd e
    | _ => exact hd.elim
  · obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hD'
    cases d with
    | D r q => exact list19_16_5_of_isLieOf_D hR hD hv hd e
    | _ => exact hd.elim
  · obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h2D'
    cases d with
    | twistedD r q => exact list19_16_5_of_isLieOf_twistedD hR h2D hv hd e
    | _ => exact hd.elim
  · obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hG'
    cases d with
    | G2 q => exact list19_16_5_of_isLieOf_g2 hv (show q.p = 2 from hd) e
    | _ => exact hd.elim
  · exact list19_16_5_of_isSmallTwoOrG2 hR1.2.2 hS'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Census1916
