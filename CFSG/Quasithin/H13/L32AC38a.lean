module

public import CFSG.Quasithin.H13.L32AC37a
public import CFSG.Quasithin.H13.L32ASk4
public import CFSG.Quasithin.EmptyFaithful.S146zUETransv
public import CFSG.Quasithin.Vol2.Ch12Sec8OneLemma6
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldNaturalAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerOddModule
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LiftMaxSL2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCentralQuotient
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.Quasithin.Background.C124B51Hyp
public import CFSG.Quasithin.Background.C124Core
public import CFSG.Quasithin.Background.C124L2PClass
public import CFSG.Quasithin.Background.C124Z3Class
public import CFSG.Quasithin.Background.C126A5Core4
public import CFSG.Quasithin.Background.C126Defs
public import CFSG.Quasithin.Background.C1GNC124
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.FFC5Final
public import CFSG.Quasithin.Background.FFC6U
public import CFSG.Quasithin.EmptyFaithful.S14110
public import CFSG.Quasithin.EmptyFaithful.T1531Close2
public import CFSG.Quasithin.EmptyFaithful.T1531In66b
public import CFSG.Quasithin.H13.A5S136b
public import CFSG.Quasithin.H13.L32AC50d
public import CFSG.Quasithin.H13.NQS1345
public import CFSG.Quasithin.H13.U3S1348T
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
public import CFSG.Quasithin.Vol2.Ch11SecD552
public import CFSG.Quasithin.Vol2.Ch11SecD556C
public import CFSG.Quasithin.Vol2.Ch11StatementsF
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem hypF98_of (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK) (S : Setting147 G T L V H) :
    HypF98 T V L (fsuV1 T V) V H :=
  L1286.hypF98_of_abelian h1222 hA37 hA38 hA39
    (S.hyp.hyp1281One (stmt13_3_2_two_of h1332) (stmtL32NModule_of_inputs h1332 h1334))
    (S.hyp.isTSub_V1 (stmtL32NModule_of_inputs h1332 h1334)) S.hyp.abelian S.hz

theorem exists_transvection_of_eq (hF : HypF98 T V L (fsuV1 T V) V H)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hD : F8.Uγ V H (g : G) = F8.Dγ V (fsuV1 T V) H (g : G)) :
    ∃ b ∈ H, b ∉ pCoreOf 2 H ∧ ∃ c ∈ conjClosure V H, c ∉ fsuV1 T V ∧
      ∀ u ∈ conjClosure V H, b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * c := by
  have hUab := hF.F911_3
  have key : ∀ {W : Subgroup G}, IsElemAbelian 2 W → W ≤ conjClosure V H →
      ⁅W, F8.Uγ V H (g : G)⁆ = fsuV1 T V →
      ∃ b ∈ H, b ∉ pCoreOf 2 H ∧ ∃ c ∈ conjClosure V H, c ∉ fsuV1 T V ∧
        ∀ u ∈ conjClosure V H, b * u * b⁻¹ = u ∨ b * u * b⁻¹ = u * c := by
    intro W hW hWV hcomm
    obtain ⟨B, C, hBH, -, hBQ, hBU, hCU, hC, hCV⟩ :=
      S146zU.UE.exists_conj_pair_of_transvection hF s hW hWV hcomm
    obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp hBQ
    obtain ⟨c, hcC, hc1⟩ : ∃ c ∈ C, c ≠ 1 := by
      by_contra h
      push Not at h
      have h1 : C = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
      rw [h1, Subgroup.card_bot] at hC
      omega
    refine ⟨b, hBH hb, hbQ, c, hCU hcC, fun hcV => hc1 ?_, fun u hu => ?_⟩
    · have : c ∈ C ⊓ fsuV1 T V := Subgroup.mem_inf.mpr ⟨hcC, hcV⟩
      rw [hCV] at this
      exact (Subgroup.mem_bot.mp this)
    · have hm : b * u * b⁻¹ * u⁻¹ ∈ C := by
        rw [← hBU, ← commutatorElement_def]
        exact Subgroup.commutator_mem_commutator hb hu
      by_cases h1 : b * u * b⁻¹ * u⁻¹ = 1
      · left
        calc b * u * b⁻¹ = b * u * b⁻¹ * u⁻¹ * u := by group
          _ = u := by rw [h1, one_mul]
      · right
        have hcu : c * u = u * c :=
          congrArg Subtype.val (hUab.1.1.1 ⟨c, hCU hcC⟩ ⟨u, hu⟩)
        have e := eq_of_card_two hC hm hcC h1 hc1
        calc b * u * b⁻¹ = b * u * b⁻¹ * u⁻¹ * u := by group
          _ = u * c := by rw [e, hcu]
  rcases hF.F916_1 s hD with ⟨-, -, -, hT⟩ | ⟨-, -, -, -, hT⟩
  · exact key hF.F911_3 (conjClosure_mono hF.Vp_le_V le_rfl) hT
  · exact key hF.elemAbelian (le_conjClosure V H) hT

end CFSG.Quasithin.H13.L32A.C
