module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortGlueSix
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQFourTBSmall
import CFSG.LocalAnalysis.StandardType.GGFrameRouteJoin
import CFSG.LocalAnalysis.StandardType.GGFrameRouteLower
import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP5TwE6
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitMarking
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase

public section

namespace CFSG.StandardType.FrameRoute

open CFSG.Assembly CFSG.Open CFSG.StandardType

private theorem glueFSPointAux_eq_twE6 {lab : LargeEvenLabel}
    (h : GGLabelIso ⟨.twE6, 0, 1⟩ lab) : lab = ⟨.twE6, 0, 1⟩ := by
  obtain ⟨t, r, n⟩ := lab
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h <;> simp_all

theorem ggFSyNonFSPointJoinInput_of_glue
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) (hb1 : GGFrameTBNumerologyInput)
    (hb1' : GGFrameTBVacuousInput) (hrig : GGLabelRigidInput) (hPU : GGPumpupInput)
    (hO : GGOuterThreeRankInput) (hTCJ : GGTCJKnown) : GGFSyNonFSPointJoinInput := by
  intro G _ _ B Bs x L D J hR hW hq
  refine ⟨fun hJ hm => ?_, fun hJ hm =>
    fsPoint_unitaryNine hTBF hWI hb1 hb1' hrig hPU hO hTCJ hR hW hq hJ hm⟩
  have hm' : LargeEvenMarking L (fun lab _ _ _ _ _ =>
      (lab.tag = .twA ∧ lab.rank = 6 ∧ lab.n = 1) ∨
        (lab.tag = .twE6 ∧ lab.rank = 0 ∧ lab.n = 1)) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ h => by tauto) hm
  rcases largeEvenMarking_or hm' with h6 | hE6
  · exact fsPoint_unitarySeven hTBF hWI hb1 hb1' hrig hPU hO hTCJ hR hW hq hJ h6
  obtain ⟨𝒦, h𝒦, hne, hM⟩ := id hJ
  have hcard : Nat.card Bs = 3 ^ 7 :=
    card_bstar_of_weylAtJoin (Fintype.card_fin 7) exists_elemAbelian_two_coxeterE7 hTBF hWI hR
      hW h𝒦 hne hM
  have hL : GGInnerDiagOnLabel (fun _ lab => lab = ⟨.twE6, 0, 1⟩) 3 Bs L := by
    obtain ⟨lab₂, hΛ₂, hhas₂, -, _, -, -, -, hP₂⟩ := largeEvenMarking_exists_hasLabel hE6
    have h₂ : lab₂ = ⟨.twE6, 0, 1⟩ := by
      obtain ⟨t, r, n⟩ := lab₂
      obtain ⟨rfl, rfl, rfl⟩ := hP₂
      rfl
    subst h₂
    exact GGInnerDiagOnLabel.mono_label_of_hasLabel (fun lab hΛ hhas _ =>
      glueFSPointAux_eq_twE6 (hrig _ lab _ hΛ₂ hΛ hhas₂ hhas)) hq
  exact fsPoint_twE6 hTBF hWI hb1 hb1' hrig hPU hO hTCJ hR hW hq hJ hE6
    (TwE6Model.exists_p5Out_of_twE6 hR.1.1 hR.1.2.1
      (GGDichotomy.le_normalizer_of_innerDiagOn hR.2.2.1.1) hR.1.bstar_inf_centralizer_L hcard hL)

end CFSG.StandardType.FrameRoute

end
