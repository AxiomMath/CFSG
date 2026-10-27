module

public import CFSG.RankThree.PartTwo.Sec19.Census194.Defs
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.UnitaryTauCeti
import CFSG.RankThree.PartOne.N143.Inspect613Even
import CFSG.RankThree.PartTwo.Census.Carrier.SpinBBridge
import CFSG.RankThree.PartTwo.Census.Carrier.SpinTDBridge
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusDispatch
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.Assembly.LowTwoRank
open CFSG.AGLEmbedding (IsClassicalTwoOrG2 IsSmallTwoOrG2)

theorem isClassicalTwoOrG2_of_mulEquiv {X Z : Type} [Group X] [Group Z] (e : X ≃* Z)
    (h : IsClassicalTwoOrG2 X) : IsClassicalTwoOrG2 Z := by
  rcases h with ⟨d, hd, ⟨f⟩⟩ | ⟨n, hn, ⟨f⟩⟩ | ⟨d, hd, ⟨f⟩⟩
  · exact Or.inl ⟨d, hd, ⟨e.symm.trans f⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans f⟩⟩)
  · exact Or.inr (Or.inr ⟨d, hd, ⟨e.symm.trans f⟩⟩)

theorem ks194ClassicalCensus_of_nodes
    (hA : Census194SurvPSL) (hU : Census194SurvPSU) (hB : Census194SurvPSp)
    (hD : Census194SurvPOmegaPlus) (h2D : Census194SurvPOmegaMinus)
    (hIA : Census194IdPSL) (hIU : Census194IdPSU) (hIB : Census194IdPSp)
    (hI2D : Census194IdPOmegaMinus) (hIG : Census194IdG2) (hIS : Census194IdSmall)
    (h1 : Census194RankOne) (hA10 : ¬ IsClassicalTwoOrG2 (alternatingGroup (Fin 10))) :
    KS194ClassicalCensus := by
  intro Y _ _ hY h2 hcl h5 h3 J T hJ hNJ hcard
  have hH : Census194Hyp Y J T := ⟨⟨hY, h2, h5, h3⟩, hJ, hNJ, hcard⟩
  have hR : Census194RankHyp Y := hH.toCensus194RankHyp
  obtain ⟨hr1, hr2, hr3⟩ := h1 Y J T hH
  refine ⟨?_, ⟨fun e => ?_⟩⟩
  · rcases CFSG.AGLEmbedding.isClassicalTwoOrG2_family_cases hcl with
      hA' | hU' | hB' | hD' | h2D' | hG' | hS'
    ·
      obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hA'
      cases d with
      | A r q =>
        have hqp : q.p = 2 := hd
        have hm := CFSG.RankThree.PartOne.N143.statedClassicalModel_of_isoLie_A hv e
        rw [hqp] at hm
        left
        have hn2 : 2 ≤ r + 1 := hm.1.2.2.1
        obtain ⟨n, hn⟩ : ∃ n, n = r + 1 := ⟨_, rfl⟩
        rw [← hn] at hm hn2
        rcases Nat.lt_or_ge n 4 with hlt | hge
        · obtain rfl | rfl : n = 2 ∨ n = 3 := by omega
          · exact (hr1 q.exponent hm).elim
          · exact hIA Y 3 q.exponent hR hm (by norm_num) (Or.inl rfl)
        · have hs := hA Y n q.exponent hR hm hge
          exact hIA Y n q.exponent hR hm (by omega) (by omega)
      | _ => exact hd.elim
    ·
      obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hU'
      cases d with
      | twistedA r q =>
        have hqp : q.p = 2 := hd
        have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv e
        rw [hqp] at hm
        left
        have hn3 : 3 ≤ r + 1 := hm.1.2.2.1
        obtain ⟨n, hn⟩ : ∃ n, n = r + 1 := ⟨_, rfl⟩
        rw [← hn] at hm hn3
        rcases Nat.lt_or_ge n 4 with hlt | hge
        · obtain rfl : n = 3 := by omega
          exact (hr2 q.exponent hm).elim
        · obtain ⟨rfl, hf⟩ := hU Y n q.exponent hR hm hge
          exact hIU Y q.exponent hR hm hf
      | _ => exact hd.elim
    ·
      obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hB'
      cases d with
      | B r q =>
        have hqp : q.p = 2 := hd
        have hr := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
          ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
        left
        by_cases h2' : r = 2
        · subst h2'
          have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_typeB2 q hv e
          rw [hqp] at hm
          exact hIB Y 2 q.exponent hR hm (Or.inl rfl)
        · have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeB_even r q hv hqp
            (by omega) e
          rw [hqp] at hm
          obtain ⟨rfl, hf⟩ := hB Y r q.exponent hR hm (by omega)
          exact hIB Y 3 q.exponent hR hm (Or.inr ⟨rfl, hf⟩)
      | _ => exact hd.elim
    ·
      obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hD'
      cases d with
      | D r q =>
        have hqp : q.p = 2 := hd
        have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeD_even r q hv hqp e
        rw [hqp] at hm
        exact (hD Y r q.exponent hR hm).elim
      | _ => exact hd.elim
    ·
      obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := h2D'
      cases d with
      | twistedD r q =>
        have hqp : q.p = 2 := hd
        have hm := CFSG.RankThree.PartTwo.Census.statedClassicalModel_typeTwistedD_even r q hv
          hqp e
        rw [hqp] at hm
        obtain ⟨rfl, hf⟩ := h2D Y r q.exponent hR hm
        rw [hf] at hm
        exact Or.inl (hI2D Y hR hm)
      | _ => exact hd.elim
    ·
      obtain ⟨⟨d, hv⟩, hd, ⟨e⟩⟩ := hG'
      cases d with
      | G2 q => exact Or.inl (hIG Y q hR hd ⟨hv, ⟨e⟩⟩)
      | _ => exact hd.elim
    ·
      exact hIS Y J T hH hS'
  ·
    apply hA10
    have hc : Subgroup.center Y = ⊥ := by
      have := Subgroup.map_center_eq e
      rw [alternatingGroup.center_eq_bot (by simp)] at this
      exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp this
    exact isClassicalTwoOrG2_of_mulEquiv
      (((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot).trans e) hcl

end CFSG.RankThree.PartTwo.Sec19
