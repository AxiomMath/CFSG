module

public import CFSG.LocalAnalysis.StandardType.GGQTwoAssemble
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs
public import CFSG.LocalAnalysis.StandardType.GGOneFiveInputs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylKnownDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSecFiveTypeA
public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms
public import CFSG.LocalAnalysis.StandardType.GGNbrCenterPCyclic
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseNoBL5Aut
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.StandardType.GGNbrReflGenTwE6Three
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyWeylNS
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaCard
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {G : Type} [Group G] [Finite G]

theorem not_exists_ggTypeASplitConfig_of_qTwo (hRig : GGLabelRigidInput) {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J)
    (hL : GGInnerDiagOnLabel GGLabQTwo p Bs L) :
    ¬ ∃ n f : ℕ, GGTypeASplitConfig p B Bs x L D J n f := by
  rintro ⟨n, f, hM, hpf, hn3, -⟩
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨lab, hlab, hhas, -, -, -, -, -, hq2, -⟩ := largeEvenMarking_exists_hasLabel hL
  have hiso := hRig lab ⟨.A, n, f⟩ _ hlab (largeEvenInLambda2_typeA hM) hhas (ggHasLabel_typeA hM)
  have hf : lab.n = f := by
    obtain ⟨ta, ra, na⟩ := lab
    change na = f
    unfold GGLabelIso at hiso
    rcases hiso with h | h | h | h | h | h | h | h
    · exact congrArg LargeEvenLabel.n h
    · obtain ⟨-, h2, -⟩ := h
      rcases h2 with h2 | h2 <;> exact absurd h2 (by simp)
    · obtain ⟨-, h2⟩ := h
      have hfn : f = na := congrArg LargeEvenLabel.n h2
      omega
    · obtain ⟨-, h2⟩ := h
      exact absurd (congrArg LargeEvenLabel.tag h2) (by simp)
    · obtain ⟨-, h2⟩ := h
      exact absurd (congrArg LargeEvenLabel.tag h2) (by simp)
    · obtain ⟨-, h2⟩ := h
      exact absurd (congrArg LargeEvenLabel.tag h2) (by simp)
    · obtain ⟨-, h2⟩ := h
      have hn : n = 1 := congrArg LargeEvenLabel.rank h2
      omega
    · obtain ⟨h1, -⟩ := h
      exact absurd (congrArg LargeEvenLabel.tag h1) (by simp)
  have hf1 : 1 ≤ f := (largeEvenInLambda2_typeA hM).1
  have hf' : f = 1 := by simp only [GGLabQTwo] at hq2; omega
  subst hf'
  exact hp.one_lt.ne' (Nat.dvd_one.mp (by simpa using hpf))

theorem ggQ2_secFiveRestHyp_of_label (hdLab : GGCoxeterLabelInput) (hRig : GGLabelRigidInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) : GGSecFiveRestHyp p B Bs x L D J :=
  ⟨hS.1.1, hS.1.2.1, hS.1.2.2.1, hS.1.2.2.2.1,
    fun y K hK hRG hSW =>
      hdLab G p B Bs x L D J hS.1.1 hS.1.2.1 hS.1.2.2.1 hS.1.2.2.2.1 y K hK hRG hSW,
    not_exists_ggTypeASplitConfig_of_qTwo hRig hS.1.1 hS.2.1⟩

theorem ggQ2_nbrReflGen_of_label
    (hdLab : GGCoxeterLabelInput) (hNRG : GGNbrReflGenNonSplitInput)
    (hRk : GGTwE6ThreeNbrRankInput) (hW : GGTwE6ThreeNbrWeylInput) (hTB : GGNbrTableBWeylInput)
    (hRig : GGLabelRigidInput) (hCP : GGLabelCenterPCyclicInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting p B Bs x L D J) {y : G} {K : Subgroup G} (hK : GGNbr p B x D J y K) :
    GGReflGenerated p (ggAutomizer K Bs) := by
  by_contra hnr
  have hZ := ggNbrBstarCenterInput_of_centerPCyclic hCP
  have h7 := (ggNbr_exc_of_not_reflGen (ggNbrReflGenNonSplitFull_of_rank hNRG hRk hW hRig hZ)
    hTB hRig hZ hraw hiso (ggQ2_secFiveRestHyp_of_label hdLab hRig hS) hK hnr).1
  have h3 := ggQ2_pThree hS
  omega

theorem ggQTwoModelInput_of_label
    (hdLab : GGCoxeterLabelInput) (hNRG : GGNbrReflGenNonSplitInput)
    (hRk : GGTwE6ThreeNbrRankInput) (hW : GGTwE6ThreeNbrWeylInput) (hTB : GGNbrTableBWeylInput)
    (hRig : GGLabelRigidInput) (hCP : GGLabelCenterPCyclicInput) (hraw : GGRawInnFieldInput)
    (hiso : GGRawInndiagIsoInput) : GGQTwoModelInput := by
  intro G _ _ p B Bs x L D J hS _ _ y K hK
  have hRG := ggQ2_nbrReflGen_of_label hdLab hNRG hRk hW hTB hRig hCP hraw hiso hS hK
  have hH := hS.1
  exact Or.inr (Or.inr (Or.inr
    ⟨hdLab G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hK hRG
      (Or.inl (ggScalarsPmOne_of_prime_three hH.1 (ggQ2_pThree hS))), hRG⟩))

end CFSG.StandardType

end
