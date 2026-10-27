module

public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem s16h_e3_CycTwoP7M6A_fstar_eq_pCoreOf {Ω : Type} [Group Ω] [Finite Ω] {p : ℕ}
    [Fact p.Prime] {H : Subgroup Ω}
    (h : Subgroup.centralizer (pCoreOf p H : Set Ω) ⊓ H ≤ pCoreOf p H) :
    UC22.Fstar H = pCoreOf p H := by
  have hchar : CFSG.IsCharacteristicP p ↥H := by
    change Subgroup.centralizer (CFSG.pCore p ↥H : Set ↥H) ≤ CFSG.pCore p ↥H
    intro x hx
    have hx' : (x : Ω) ∈ Subgroup.centralizer (pCoreOf p H : Set Ω) ⊓ H := by
      refine ⟨?_, x.2⟩
      intro y hy
      rw [pCoreOf] at hy
      obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
      have hcomm : z * x = x * z := hx z hz
      rw [← hzy]
      exact congrArg Subtype.val hcomm
    have hmem : (x : Ω) ∈ pCoreOf p H := h hx'
    rw [pCoreOf] at hmem
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hmem
    have hzx' : z = x := Subtype.ext hzx
    rw [hzx'] at hz
    exact hz
  have hgf : CFSG.generalizedFitting ↥H = CFSG.pCore p ↥H :=
    (CFSG.isCharacteristicP_iff_generalizedFitting_eq_pCore ↥H p).1 hchar
  unfold UC22.Fstar pCoreOf
  rw [CFSG.Adapters.genFittingFStar_eq_foundations, hgf]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
