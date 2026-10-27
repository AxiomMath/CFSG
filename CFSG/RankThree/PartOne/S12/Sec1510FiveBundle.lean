module

public import CFSG.RankThree.PartOne.U5E.Reinst
public import CFSG.RankThree.PartOne.K159F.ZFive
public import CFSG.RankThree.PartOne.K159.PerfNormalizerFive
public import CFSG.RankThree.PartOne.CTP.StrongPCharPFinal
public import CFSG.RankThree.PartOne.CTP.StrongPSporadic
public import CFSG.RankThree.PartOne.SPOR.OuterSimple
public import CFSG.RankThree.PartOne.TCB.SchreierFinal
public import CFSG.RankThree.PartOne.CTP.SeitzLedger
public import CFSG.RankThree.PartOne.S15K.Node158E3
public import CFSG.RankThree.PartOne.N143.SectionListBound
import CFSG.RankThree.PartOne.N143.Sec159FiveList
import CFSG.RankThree.PartOne.K159G.CompGen
import CFSG.RankThree.PartOne.U5E.InnLayerP5
import CFSG.RankThree.PartOne.U5E.KF1510E
public import CFSG.RankThree.PartOne.S12.Sec1510FiveSyl
public import CFSG.RankThree.PartOne.S12.Sec1510Node

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

@[expose] def KF1510Reg : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec15Hyp G p A c L E → Sec12Facts G p A c L E → Outcome152Five p E A (lieGenerated p E) →
    ∀ e ∈ E, e ≠ 1 → (IsRegularIn p E e ∨ ¬ CentralizesE p E e) →
      Subgroup.centralizer ({e} : Set G) ≤ lieNormalizer p E

theorem node1510Five_of_reg_core (h155 : Node155) (h158 : Node158) (h158E3 : S15K.Node158E3)
    (h159 : Node159Five) (hR : U5E.Reinst5) (hInn : KFInnLayerFive) (hE : KF1510E)
    (hReg : KF1510Reg) : Node1510Five := by
  classical
  intro G _ _ p A c L E h15 hF hout U hUE hU1
  have h := h15.h12
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hout' : Outcome152 p E A (lieGenerated p E) := Or.inr (Or.inr (Or.inr (Or.inr hout)))
  have hEel : IsElementaryAbelian p ↥E := h.E_elem
  have hAE : A ≤ E := h.A_le_E
  have hAel : IsElementaryAbelian p ↥A := h.A_elem
  have hAcard : Nat.card ↥A = p ^ 3 := h.A_card
  have hNA : ∀ B : Subgroup G, B ≤ A → ¬ IsCyclic ↥B →
      Subgroup.normalizer (B : Set G) ≤ lieNormalizer p E := fun B hBA hBcyc =>
    h158 G p A c L E h15 hF hout' B hBA hBcyc
  have hJ : ∀ Q : Subgroup G, E ≤ Q → Q ≤ Subgroup.normalizer (E : Set G) → IsPGroup p ↥Q →
      thompsonElem p Q = E := fun Q hEQ hQW hQ =>
    Sec15FA.thompson_eq_of_node155 h155 h15 hF hout' hEQ hQW hQ
  have hWN : torusNormalizer E ≤ lieNormalizer p E := torusNormalizer_le_lieNormalizer hp E
  have hCe : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤ lieNormalizer p E := by
    intro e heE he1
    by_cases hspec : IsRegularIn p E e ∨ ¬ CentralizesE p E e
    · exact hReg G p A c L E h15 hF hout e heE he1 hspec
    · obtain ⟨hnreg, hcen'⟩ := not_or.1 hspec
      have hcen : CentralizesE p E e := not_not.1 hcen'
      have hLN : ∀ Z ∈ thetaComponentsAt p e, Z ≤ lieNormalizer p E := by
        intro Z hZ
        obtain ⟨B, hB, heB⟩ : ∃ B ∈ admissibleTriples p E, e ∈ B := by
          by_contra hcon
          exact hnreg fun B hB heB => hcon ⟨B, hB, heB⟩
        exact h159 G p A c L E h15 hF hout Z
          ⟨B, hB, mem_thetaComponentFamily_iff.2 ⟨e, heB, he1, hZ⟩⟩
      obtain ⟨P, hPsyl, hEP, hPW, hPΩ, hPc⟩ :=
        Sec1510Five.exists_sylow_cent hp h155 h15 hF hout heE hcen
      have hND : ∀ D : Subgroup G,
          (∀ x : G, x ∈ D ↔ x ∈ E ∧ ∀ l ∈ thetaLayer p e, x * l * x⁻¹ * l⁻¹ ∈ thetaCore p e) →
            ¬ IsCyclic ↥D → Subgroup.normalizer (D : Set G) ≤ lieNormalizer p E := by
        intro D hD hcD
        have hDE : D ≤ E := fun x hx => ((hD x).1 hx).1
        rcases hE G p A c L E h15 hF hout e heE he1 hcen hLN D hD with hcyc | h3 | ⟨A', hA', hDA'⟩
        · exact absurd hcyc hcD
        · exact h158E3 G p A c L E h15 hF hout D hDE h3
        · obtain ⟨c', L', h15', hF', hout''⟩ := hR G p A c L E h15 hF hout A' hA'
          exact h158 G p A' c' L' E h15' hF'
            (Or.inr (Or.inr (Or.inr (Or.inr hout'')))) D hDA' hcD
      exact Sec1510Node.centralizer_le_gen hp hEel hAE hAel hAcard hJ hWN hNA hND heE he1 hLN
        (hInn G p A c L E h15 hF hout e heE he1 hcen hLN) hPsyl hEP (hPW.trans hWN) hPΩ hPc
  obtain ⟨⟨e, heU⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hU1
  have he1' : e ≠ 1 := fun h' => he1 (Subtype.ext h')
  have hC : Subgroup.centralizer (U : Set G) ≤ lieNormalizer p E :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.2 heU)).trans (hCe e (hUE heU) he1')
  exact Sec15FA.normalizer_le_of_centralizer_le hp hEel hJ hUE hWN hC

theorem node1510Five_inputs_of_bundle
    (hS : SchreierFor InCatalog) (hSC : SchreierFor CFSG.Blueprint.Catalog)
    (h82 : LocalThetaComponentEmbeddingFrontier) (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hSLB : N143.SectionListBound) (hSeitz : CTP.SeitzResidual)
    (hMod : KFU5Mod) (hAt : KFU5At) (hFive : U5FiveInndiag)
    (h154 : Node154) (h155 : Node155) (h158 : Node158) (h158E3 : S15K.Node158E3) (h156 : KF156')
    (hR : U5E.Reinst5) (hZres : K159F.KF159ZFiveRes) :
    Node159Five ∧ KFInnLayerFive ∧ KF1510E := by
  have hZ : KF159ZFive :=
    K159F.kf159ZFive_of_inputs h155 (K159F.centerRankFive_of_griess hbridge hGA) hZres
  have h159 : Node159Five := by
    intro G _ _ p A c L E h15 hF hout X hX
    obtain ⟨B, hB, hXB⟩ := hX
    obtain ⟨c', L', h15', hF', hout'⟩ := hR G p A c L E h15 hF hout B hB
    exact N143.node159Five_core_of_list h154 h155 h158 h158E3 h156 hZ
      (N143.kf159ListFive_of_list hSLB) (N143.extSPEList_of_inputs_seitzThree
          (CTP.extSeitzThree_of_residual hSeitz) TCB.schreierFor_inCatalog_holds
          CTP.charPNoncommInput
          (CTP.sporadicStrongPInput_of_inputs SPOR.sporadicOuterOrderLeTwoSimple_holds)) N143.kf159Aut5List
      (K159F.kf159Sz_of_inputs h155 hMod) (N143.extFiveList_of_inputs_seitzThree
          (CTP.extSeitzThree_of_residual hSeitz) CTP.charPNoncommInput
          (K159F.sporadicFiveInput_of_leTwo SPOR.sporadicOuterOrderLeTwoSimple_holds))
      G p B c' L' E h15' hF' hout' X hXB
  have hEin : U5K.U5EInndiag := U5K.u5EInndiag_of hMod hAt hFive
  have hPerf : K159.KFPerfNormalizerFive :=
    K159.kfPerfNormalizerFive_of_schreier hSC hMod hAt hFive
  have hInn : KFInnLayerFive :=
    U5E.kfInnLayerFive_of_schreier' hSC hMod hAt hFive (K159.kfCompLayerFive_of hS h82 hAt hEin)
  have hE : KF1510E :=
    U5E.kf1510E_of_gen hS h82 hMod hAt hEin (S15K.layerRowFive_of_package hMod hAt hFive) hPerf
      (K159.kfCompGenFive_of hAt hEin) hGA
  exact ⟨h159, hInn, hE⟩

end CFSG.RankThree.PartOne
