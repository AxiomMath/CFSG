module

public import CFSG.Timmesfeld.Bridge.OddLocalDefs
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.Timmesfeld.Bridge.Asc72Triangle
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

theorem conj_mem_commSet (hN : IsNormalSet D) (g : G) {z x : G} (hx : x ∈ commSet D z) :
    g * x * g⁻¹ ∈ commSet D (g * z * g⁻¹) := by
  refine ⟨hN g x hx.1, (Commute.conj_iff g).2 hx.2.1, fun h => hx.2.2 ?_⟩
  simpa using h

theorem conj_mem_commSet_of_commute (hN : IsNormalSet D) {x g z : G} (hg : Commute g x)
    (hz : z ∈ commSet D x) : g * z * g⁻¹ ∈ commSet D x := by
  refine ⟨hN g z hz.1, ?_, fun h => hz.2.2 ?_⟩
  · have h1 := hz.2.1.conj g
    rwa [hg.eq, mul_inv_cancel_right] at h1
  · have h2 : g * z * g⁻¹ = g * x * g⁻¹ := by rw [h, hg.eq, mul_inv_cancel_right]
    simpa using h2

end CFSG.OddTranspositions.PartThree
