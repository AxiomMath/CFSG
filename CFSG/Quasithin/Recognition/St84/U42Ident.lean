module

public import CFSG.GH74.QTGen4.DSGen4.Defs
public import CFSG.GH74.QTGen4.DSGen4.Leaf.SylowS
public import CFSG.GH74.QTGen4.DSGen4.Leaf.UAmalCoordsPlain
public import CFSG.GH74.QTGen4.U42.AmalgamGen
public import CFSG.GH74.QTGen4.U42.StubA4h
public import CFSG.Quasithin.Background.Harris.F112S3Big.Defs
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.S1421F112
public import CFSG.Quasithin.Recognition.GoldschmidtF112RY9
public import Certificates.Certificate113
public import Certificates.Certificate4161
public import Certificates.Certificate2012
public import CFSG.CGT.Timmesfeld75.L2Pair
public import CFSG.CGT.Timmesfeld75.ListWCBasic
public import CFSG.ClassicalGroups
public import CFSG.GH74.QTGen4.DSGen4.LeafWrappersAmal
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.GH74.QTGen4.U42.GSidePairCore
public import CFSG.GH74.QTGen4.U42.GSidePairData
public import CFSG.GH74.QTGen4.U42.MSplitB
public import CFSG.GH74.QTGen4.U42.ModelP1
public import CFSG.GH74.QTGen4.U42.ModelPairCore
public import CFSG.GH74.QTGen4.U42.StubA4b
public import CFSG.LieType.Simplicity.Classical
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Quasithin.Background.F3
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.EmptyFaithful.S1414Defs
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S141Statements
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.H13.StatementsL3
public import CFSG.Quasithin.Recognition.F4Moufang
public import CFSG.Quasithin.Recognition.F4Thirtyone
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair5
public import CFSG.Sporadic.Schreier.J4SCommGenBase1
public import CFSG.Sporadic.Schreier.J4SLocalNodes

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
  CFSG.GH74.QTGen4.DSGen4 CFSG.GH74.QTGen4.U42
  CFSG.Quasithin.Background.Harris.F112S3Big
  CFSG.Quasithin.H13.F431.U42 CFSG.Quasithin.A5Model CFSG.Quasithin.H13.A5
open scoped commutatorElement

variable {G : Type} [Group G]

structure U42PlainData (L1 L2 S : Subgroup G) : Prop where
  b6 : F112B6Loc L1 L2
  le_right : S ≤ L2
  oTwo_right : pCoreOf 2 L2 = dsQ L2 L1 S
  dsQ_right : dsQ L2 L1 S = dsZi L2 S
  card_right : Nat.card (pCoreOf 2 L2) = 2 ^ 4
  oTwo_left : pCoreOf 2 L1 = dsQ L1 L2 S
  card_left : Nat.card (pCoreOf 2 L1) = 2 ^ 5
  sup_eq : dsQ L2 L1 S ⊔ dsQ L1 L2 S = S
  not_le : ¬ dsZi L2 S ≤ dsQ L1 L2 S

theorem isAmalgamOfGroup_psu4_of_u42PlainData [Finite G]
    {L1 L2 S : Subgroup G} (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2)
    (hD : U42PlainData L1 L2 S) :
    IsAmalgamOfGroup (f112Amalgam L1 L2 S) (IsLieOverTwo .PSU 4 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  obtain ⟨e, hB, hT, hU, hH, hUB⟩ :=
    dsucp_main hR.symm hD.le_right h1 hD.b6 hD.oTwo_right hD.dsQ_right
      (by rw [hD.card_right]; norm_num) hD.oTwo_left
      (by rw [hD.card_left]; norm_num) hD.sup_eq hD.not_le
      (leafSylowS hR.symm).2.1 (leafSylowS hR).2.1
  obtain ⟨eY, hY1, hY2⟩ := exists_model_coords_plain
  have hB' : ∀ g : ↥P2, (g : Y) ∈ P1 ↔
      ((eY g : Mof (alternatingGroup (Fin 5))) : Mc) ∈ Bc := by
    intro g
    have hPB : (g : Y) ∈ P1 ↔ (g : Y) ∈ B0 := ⟨fun h => ⟨h, g.2⟩, fun h => h.1⟩
    rw [hPB, model_B0_iff g]
    have hs : ((eY g : Mof (alternatingGroup (Fin 5))) : Mc).right.sign = 1 :=
      Equiv.Perm.mem_alternatingGroup.1 (mem_Mof.1 (eY g).2)
    change _ ↔ ((eY g : Mof (alternatingGroup (Fin 5))) : Mc).right.sign = 1 ∧
      ((eY g : Mof (alternatingGroup (Fin 5))) : Mc).right 4 = 4
    rw [hY2 g] at hs ⊢
    exact ⟨fun h => ⟨hs, h⟩, fun h => h.2⟩
  have hT' : ∀ g : ↥P2, (g : Y) ∈ T ↔
      ((eY g : Mof (alternatingGroup (Fin 5))) : Mc) ∈ Tc := by
    intro g
    rw [model_T_iff g]
    change _ ↔ InK4 ((eY g : Mof (alternatingGroup (Fin 5))) : Mc).right
    rw [hY2 g]
  have hU' := model_U_iff eY hY1 hY2
  have hU0R : U0 ≤ Mof (alternatingGroup (Fin 5)) := by
    intro x hx
    refine mem_Mof.2 (Equiv.Perm.mem_alternatingGroup.2 ?_)
    have hk : InK4 x.right := (show _ ∧ InK4 x.right from hx).2
    revert hk
    generalize x.right = σ
    rintro (rfl | rfl | rfl | rfl) <;> decide +kernel
  have iso := amalgam_iso_of_coords hU0R e eY hB hB' hT hT' hU hU' hH model_pairCore hUB
  refine ⟨Y, inferInstance, lieModel_Y, T, P1, P2, isYAmalgamPair, ?_⟩
  simpa only [f112Amalgam, bigB_comm L1 L2 S] using iso

end CFSG.Quasithin.F112R.St84
