module

public import CFSG.LocalAnalysis.StandardType.GGR4JMeetDefs
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetDecomp
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetCard

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

theorem ggR4JCard_of_meet
    (hZk : GGCentreTwoKnown) (hM : GGR4JMeet) (hN : GGR4JCardNC) :
    GGR4JCard := by
  intro G _ _ p B Bs x L D J hcfg hOp hInn hNT y K hnbr hRG hSc _ hp3 Λ _ _ C b c V _ _ ι φ' h' α'
    hD hspan hcell hAL hAK
  obtain ⟨hnum, hlab⟩ := hN G p B Bs x L D J hcfg hOp hInn hNT y K hnbr hRG hSc hp3 Λ C b c V ι φ'
    h' α' hD hspan hcell hAL hAK
  refine ⟨?_, hlab⟩
  by_cases hC : ∃ f : ℕ, GGHasLabel ⟨.C, 3, f⟩ (J ⧸ Subgroup.center J)
  · obtain ⟨f, hC3⟩ := hC
    have hE : 3 ^ 3 ≤ Nat.card (Bs ⊓ J : Subgroup G) :=
      hM G p B Bs x L D J hcfg hOp hInn hNT y K hnbr hRG hSc hp3 Λ C b c V ι φ' h' α' hD hspan
        hcell hAL hAK
    subst hp3
    have hBsEA : IsElemAbelian 3 Bs := hcfg.2.1.2.1
    have hSCs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs := hcfg.2.1.2.2.2
    have hDBs : D ≤ Bs := hcfg.2.2.1.1.trans hcfg.2.1.1
    have hDcard : Nat.card D = 3 ^ 2 := hcfg.2.2.1.2.2.1
    have hDJ : D ≤ Subgroup.centralizer (J : Set G) :=
      (le_of_eq hcfg.2.2.1.2.2.2.2.2.2).trans inf_le_right
    have hJq : CFSG.Assembly.IsQuasisimple J := (hcfg.2.2.1.2.2.2.2.2.1).2.2
    have hJperf : commutator ↥J = ⊤ := hJq.1
    have hZ := ggR4J_center_coprime hZk hJperf hC3
    have hcardΛ : Fintype.card Λ = 4 := by
      obtain ⟨e, -, -⟩ := hcell
      simpa using Fintype.card_congr e.symm
    have hBs : Nat.card Bs ≤ 3 ^ 5 := (ggR4J_card_Bs hD hspan hcardΛ).le
    have hInnJ := ggR4J_inn_of_meet hBsEA hDBs hDcard hDJ hZ hBs hE
    exact ggR4J_card_ge_c3 hBsEA hSCs hJperf hZ hInnJ hC3
  · exact hnum (fun f hf => hC ⟨f, hf⟩)

end CFSG.StandardType

end
