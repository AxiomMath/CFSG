module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeakNbr
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnolaLabel
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowCases
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSA
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSD
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowSE
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNMoreAbsurd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNAbsurd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNE6Cells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowNF4Cells
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallAbsurd
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZA8
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrRowZE6
public import CFSG.LocalAnalysis.StandardType.GGTCJHolds
public import CFSG.LocalAnalysis.StandardType.GGLabelRigid
public import CFSG.LocalAnalysis.StandardType.GGNbrBalanceSchreier

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem GGInnerDiagOnLabel.mono' {G : Type} [Group G] {S T : ℕ → LargeEvenLabel → Prop} {p : ℕ}
    {Bs K : Subgroup G} (hST : ∀ lab, S p lab → T p lab) (h : GGInnerDiagOnLabel S p Bs K) :
    GGInnerDiagOnLabel T p Bs K :=
  largeEvenMarking_mono (fun lab _ _ _ _ _ hP => ⟨hST lab hP.1, hP.2⟩) h

theorem GGInnerDiagOnLabel.toMarking {G : Type} [Group G] {S : ℕ → LargeEvenLabel → Prop}
    {p : ℕ} {Bs K : Subgroup G} (h : GGInnerDiagOnLabel S p Bs K) :
    LargeEvenMarking ↥K (fun lab _ _ _ _ _ => S p lab) :=
  largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) h

theorem ggSecFiveSplitNbrInput_of_ennola
    (hKn : GGTCJEnnolaKnown) (hLB : GGLBalanceInput) (hP : GGStdSubPrimeInput) :
    GGSecFiveSplitNbrInput := by
  have hRig : GGLabelRigidInput := ggLabelRigidInput_holds
  have hTCJ : GGTCJKnown := TCJ.ggTCJKnown_holds
  have hBr : GGSplitLieLabelInput := fun G _ _ p L hp hp2 hL => ggSplitLie_label hp hp2 hL
  intro G _ _ p B Bs x L D J 𝒦 hcfg hL ι M e hpres hle3 K hK
  have hKw := GGSecFiveWeakNbr.of_mem hcfg hK
  have hp : p.Prime := (ggRouteCfg_prime hcfg).1
  have hEn : ∀ {S : ℕ → LargeEvenLabel → Prop}, (∀ lab, S p lab → ggRowP_Ennola p lab) →
      GGInnerDiagOnLabel S p Bs K → False := fun hST h =>
    ggRowEnnola_absurd hRig hTCJ hKn hLB hP hBr hcfg hL hK (h.mono' hST)
  have h0 := ggNbr_rowCases hcfg hKw
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SA) h0 with h | h
  · exact ggSplitLie_of_rowSA hp h.toMarking
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SD) h with h | h
  · exact ggSplitLie_of_rowSD hp h.toMarking
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SE6) h with h | h
  · exact ggSplitLie_of_rowSE6 hp h.toMarking
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SE7) h with h | h
  · exact ggSplitLie_of_rowSE7 hp h.toMarking
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_SE8) h with h | h
  · exact ggSplitLie_of_rowSE8 hp h.toMarking
  exfalso
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ESU) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inl h)) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EOmP) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inl h))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EOmM) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inr (Or.inl h)))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ETwE6) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inl h))))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE7) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_EE8) h with h | h
  · exact hEn (fun _ h => Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))) h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NB) h with h | h
  · exact ggRowNB_absurd hcfg hpres hle3 hKw h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NF4) h with h | h
  · have h' : GGInnerDiagOnLabel (fun p lab => (ggRowP_NF4 p lab ∧ (p = 3 ∧ p ∣ 2 ^ lab.n + 1)) ∨
        (ggRowP_NF4 p lab ∧ ¬ (p = 3 ∧ p ∣ 2 ^ lab.n + 1))) p Bs K :=
      h.mono' fun lab hl => (em (p = 3 ∧ p ∣ 2 ^ lab.n + 1)).imp (fun h3 => ⟨hl, h3⟩)
        (fun h3 => ⟨hl, h3⟩)
    rcases GGInnerDiagOnLabel.elim_or h' with h | h
    · exact hEn (fun _ h => Or.inr h) h
    · exact ggRowNF4Cells_absurd hcfg hpres hle3 hKw h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NAP) h with h | h
  · exact ggRowNAP_absurd hcfg hpres hle3 hKw h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NTwAM) h with h | h
  · exact ggRowNTwAM_absurd hcfg hpres hle3 hKw h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NDOdd) h with h | h
  · exact ggRowNDOdd_absurd hcfg hpres hle3 hKw h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NTwD) h with h | h
  · exact ggRowNTwD_absurd hcfg hpres hle3 hKw h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_NE6) h with h | h
  · exact ggRowNE6_absurd hcfg hpres hle3 hKw h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_Small) h with h | h
  · exact ggRowSmall_absurd hcfg hKw h
  rcases GGInnerDiagOnLabel.elim_or (S := ggRowP_ZA8) h with h | h
  · exact ggRowZA8_absurd hcfg hKw h
  · exact ggRowZE6_absurd hcfg hKw h

end CFSG.StandardType

end
