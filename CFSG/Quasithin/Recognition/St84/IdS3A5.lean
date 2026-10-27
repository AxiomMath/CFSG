module

public import CFSG.Quasithin.Recognition.St84.Sec68E
public import CFSG.Quasithin.Recognition.St84.Sec5Main
public import CFSG.Quasithin.Recognition.St84.Sec7Main
public import CFSG.Quasithin.Recognition.St84.TransferS3A5
public import CFSG.Quasithin.Recognition.St84.J2Ident
public import CFSG.Quasithin.Recognition.St84.AutJ2Ident
public import CFSG.Quasithin.Recognition.St84.TransportS3A5
public import CFSG.Quasithin.Recognition.St84.U42DataS3A5
public import CFSG.Quasithin.Recognition.St84.J2DataS3A5

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ

theorem f112sa_exists_setup_treeData
    {G : Type} [Group G] [Finite G] {L1 L2 S : Subgroup G}
    (hF : F112Hyp L1 L2 S) (h1 : VS3 L1) (h2 : VA5 L2) :
    ∃ X₀ : Setup (f112Gold L1 L2 S).treeGraph ↥(f112EOdd L1 L2 S),
      X₀.vert 0 = baseA (f112Gold L1 L2 S) ∧ X₀.vert 1 = baseB (f112Gold L1 L2 S) ∧
      (X₀.TreeU42Data ∨ X₀.TreeJ2Data) := by
  have hH := f112sl_hyp30 (n := 2) hF h1 le_rfl h2
  have hc := f112sa_charTwoStab hF h1 le_rfl h2
  have hn : ∀ v, nOf (f112Gold L1 L2 S).treeGraph v = 1 ∨
      nOf (f112Gold L1 L2 S).treeGraph v = 2 := by
    intro v
    rcases exists_smul_base _ v with ⟨g, rfl⟩ | ⟨g, rfl⟩
    · exact Or.inl (f112sa_nOf_alpha hF h1 le_rfl h2 g)
    · exact Or.inr (f112sa_nOf_beta hF h1 le_rfl h2 g)
  have hmix : ∀ v w, (f112Gold L1 L2 S).treeGraph.Adj v w →
      nOf (f112Gold L1 L2 S).treeGraph v ≠ nOf (f112Gold L1 L2 S).treeGraph w := by
    intro v w hvw
    obtain ⟨g, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := exists_smul_edge _ hvw
    · rw [f112sa_nOf_alpha hF h1 le_rfl h2 g, f112sa_nOf_beta hF h1 le_rfl h2 g]; decide
    · rw [f112sa_nOf_alpha hF h1 le_rfl h2 g, f112sa_nOf_beta hF h1 le_rfl h2 g]; decide
  obtain ⟨s, -, hs, -, hodd, h5⟩ := sec7_S3A5 hH hc hn hmix
  have h11 : ∃ v, nOf (f112Gold L1 L2 S).treeGraph v = 2 :=
    ⟨_, f112sa_nOf_beta hF h1 le_rfl h2 1⟩
  obtain ⟨X₀, hX0, hX1⟩ := f112sa_exists_setup_baseEdge hF h1 h2
  have hY0 : X₀.n 0 = 1 := by
    show nOf _ (X₀.vert 0) = 1
    rw [hX0, ← one_smul (f112Gold L1 L2 S).Universal (baseA (f112Gold L1 L2 S))]
    exact f112sa_nOf_alpha hF h1 le_rfl h2 1
  have hY1 : X₀.n 1 = 2 := by
    show nOf _ (X₀.vert 1) = 2
    rw [hX1, ← one_smul (f112Gold L1 L2 S).Universal (baseB (f112Gold L1 L2 S))]
    exact f112sa_nOf_beta hF h1 le_rfl h2 1
  obtain ⟨-, hdata⟩ := sec5_S3A5_univ hc hs hodd h5
    (fun Y hY hGT => sec6_false' hH hc hn h11 Y hs hodd h5 hY hGT) X₀ hY0 hY1
  exact ⟨X₀, hX0, hX1, hdata⟩

theorem idS3A5_holds :
    IdS3A5 := by
  intro G _ _ L1 L2 S hF h1 h2
  obtain ⟨X, hX0, hX1, hd | hd⟩ := f112sa_exists_setup_treeData hF h1 h2
  · have hU := s3a5U42Hyp_of_treeU42Data hF hX0 hX1 hd
    rcases u42Data_of_s3a5ParabolicId hF h1 h2 (s3a5ParabolicId_u42 hF h1 h2 hU) hU
        (not_natSec_of_treeU42Data hF hX0 hX1 hd) with hD | hD
    · exact Or.inl (isAmalgamOfGroup_psu4_of_u42PlainData hF h1 h2 hD)
    · exact Or.inr (Or.inl (isU4ExtTwo_of_u42ExtData hF h1 h2 hD))
  · have hJ := s3a5J2Hyp_of_treeJ2Data hF hX0 hX1 hd
    rcases j2Data_of_s3a5ParabolicId hF h1 h2 (s3a5ParabolicId_j2 hF h1 h2 hJ) hJ
        (card_pCoreOf_P1'_of_treeJ2Data hF hX0 hX1 hd)
        (exists_involution_of_treeJ2Data hF hX0 hX1 hd)
        (exists_zSigma_of_treeJ2Data hF hX0 hX1 hd) with hD | hD
    · exact Or.inr (Or.inr (Or.inl (isParabolicAmalgamOfGroup_j2_of_j2LocalData hF h1 h2 hD)))
    · exact Or.inr (Or.inr (Or.inr
        (isParabolicAmalgamOfGroup_autJ2_of_autJ2LocalData hF h1 h2 hD)))

end CFSG.Quasithin.F112R.St84
