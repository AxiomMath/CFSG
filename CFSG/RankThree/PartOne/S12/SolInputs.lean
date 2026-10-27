module

public import CFSG.CGT.PushingUpLit.SolK.TightOrders
public import CFSG.CGT.PushingUpLit.LIT.Foote.E1a
public import CFSG.CGT.PushingUpLit.LIT.A4.Holds
public import CFSG.CGT.PushingUpLit.J42.S5Final
public import CFSG.CGT.PushingUpLit.Orth.OrthSol
public import CFSG.CGT.PushingUpLit.E3A.Main
public import CFSG.RankThree.PartOne.SolD3.FinalHarada
public import CFSG.CGT.PushingUpLit.E3A.ThreeMain
public import CFSG.CGT.PushingUpLit.SolKAb.Residue
public import CFSG.LocalAnalysis.EvenSporadicStandard.Finkelstein77.Lemma25
import CFSG.CGT.PushingUpLit.SolKAb.Main
import CFSG.CGT.PushingUpLit.SolKMT.ToTightCore
import CFSG.CGT.PushingUpLit.SOLT.Final
public import CFSG.CGT.PushingUpLit.SolK.CaseII
public import CFSG.CGT.PushingUpLit.SolK.HighN
public import CFSG.CGT.PushingUpLit.SolK.SevenTwo

public section

namespace CFSG.RankThree.PartOne.SolIn

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.GH74 CFSG.CGT.PushingUpLit
  CFSG.CGT.PushingUpLit.SolK

@[expose] def Inputs : Prop :=
  CFSG.CGT.PushingUpLit.SolKAb.SolomonTimmesfeldMainResidue

theorem isQuasisimple_top_of_natAlt {X : Type} [Group X] {n : ℕ} (hn : 2 ≤ n)
    (hnat : IsNaturalAltModule X n) : CFSG.IsQuasisimple (X ⧸ pCore 2 X) := by
  obtain ⟨φ, -⟩ := hnat
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv φ.symm
    (CFSG.CGT.PushingUpLit.Glue.isQuasisimple_alternating (k := 2 * n + 1) (by omega))

theorem gen4_degree_five_of_S5 (hE2 : SolomonTimmesfeldTight) (hE3a : WCBlockCentralizer)
    (hOrd : TightSmallGroupOrders) (hT75 : T75Structural) (hJ : JankoU42Gen4S5)
    {G : Type} [Group G] [Finite G] {M X : Subgroup G} (S : SolCfg G M X 2)
    (hKP : KProper InCatalog G) : SectionalTwoRankLE G 4 := by
  rcases S.tight_or_dihedral_plus hE2 hE3a hOrd hKP with hd | hsd | hTight
  · exact gen4_of_dihedral_or_semidihedral (Or.inl hd)
  · exact gen4_of_dihedral_or_semidihedral (Or.inr hsd)
  · have hrs : RSmall S := S.rSmall_of_two_le hTight
    by_cases hH : CentInM S
    · exact (false_of_tiData hT75 hKP S
        (S.tiData_of_H hTight.toTightData (SolCfg.RSmall.elem S hrs) hH)).elim
    · exact jankoU42Gen4_of_S5 hJ G M X S hKP hTight.toTightData hrs hH

theorem solomonTimmesfeldTight_of_inputs
    (hL25 : CFSG.EvenSporadicStandard.Finkelstein77.Asc76Lemma25) (h : Inputs) :
    SolomonTimmesfeldTight :=
  CFSG.CGT.PushingUpLit.SolKMT.solomonTimmesfeldTight_of_main_of_lemma25 hL25
    (CFSG.CGT.PushingUpLit.SolKAb.solomonTimmesfeldMain_of_residue hL25 h)

theorem solomonAlternatingBlockK_of_inputs
    (hL25 : CFSG.EvenSporadicStandard.Finkelstein77.Asc76Lemma25)
    (hSCL : CFSG.CGT.Timmesfeld75.SimpleCaseListStmt) (h : Inputs) :
    SolomonAlternatingBlockK := by
  have hE2 : SolomonTimmesfeldTight := solomonTimmesfeldTight_of_inputs hL25 h
  have hJ : JankoU42Gen4S5 := jankoU42Gen4S5_of_halves jankoU42Gen4S5ROne_holds
      jankoU42Gen4S5RNe1_holds
  have hF : FooteNonsolvableSimple := LIT.Foote.footeNonsolvableSimple_holds
  have hA3 : A4BlockNormalThree := A4.a4BlockNormalThree_holds
  have hE3a : WCBlockCentralizer := CFSG.CGT.PushingUpLit.E3A.wcBlockCentralizer_of_list hSCL
  have hThree : SolDegreeThreeRNe1 := SolD3.solDegreeThreeRNe1_of_harada hE2 tightSmallGroupOrders
      (CFSG.CGT.PushingUpLit.E3A.wcBlockCentralizerThree_of_list hSCL)
  have hT75 : T75Structural :=
    SOLT.t75Structural_of_list hSCL CFSG.CGT.Timmesfeld75.listWCIdentification_of_cert
  have hOrd : TightSmallGroupOrders := tightSmallGroupOrders
  have hThree' : SolDegreeThree := solDegreeThree_of_rNe1 hThree
  intro G _ _ hKP hsimple hchar M X hMmax hXM hsub hX hnat huniq
  obtain ⟨n, hn1, hnat⟩ := hnat
  have hshort : IsShortGroup ↥X := hX.1
  by_cases hn : n = 1
  · subst hn
    rcases hA3 G hsimple hKP hchar M X hMmax hXM hsub hshort hnat huniq with hnorm | hgen
    · exact hThree' G hKP hsimple hchar M X hMmax hXM hnorm hshort hnat huniq
    · exact hgen
  · have hn2 : 2 ≤ n := by omega
    have hq : CFSG.IsQuasisimple (↥X ⧸ pCore 2 ↥X) := isQuasisimple_top_of_natAlt hn2 hnat
    have hnorm := hF G hsimple hKP hchar M X hMmax hXM hsub hshort hq huniq
    have hHyp : SolHyp G M X n := ⟨hsimple, hchar, hMmax, hXM, hnorm, huniq, hshort, hnat, hn2⟩
    obtain ⟨S⟩ := exists_solCfg hHyp
    by_cases hn2' : n = 2
    · subst hn2'
      exact gen4_degree_five_of_S5 hE2 hE3a hOrd hT75 hJ S hKP
    · have hn3 : 3 ≤ n := by omega
      rcases S.tight_or_dihedral_plus hE2 hE3a hOrd hKP with hd | hsd | hTight
      · exact gen4_of_dihedral_or_semidihedral (Or.inl hd)
      · exact gen4_of_dihedral_or_semidihedral (Or.inr hsd)
      · have hrs : RSmall S := S.rSmall_of_two_le hTight
        have hH : CentInM S := by
          by_cases h3 : n = 3
          · exact S.centInM_seven hTight.toTightData hrs h3
          · exact S.centInM_of_four_le hTight.toTightData (SolCfg.RSmall.elem S hrs) hrs
              (by omega)
        exact (false_of_tiData hT75 hKP S
          (S.tiData_of_H hTight.toTightData (SolCfg.RSmall.elem S hrs) hH)).elim

end CFSG.RankThree.PartOne.SolIn
