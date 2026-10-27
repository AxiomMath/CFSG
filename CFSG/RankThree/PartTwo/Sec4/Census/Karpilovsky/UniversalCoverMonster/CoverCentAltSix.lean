module

public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.KFacts.KP4Data
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Item417Res7ProofTitsCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster

open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

noncomputable def centralizerSingletonEquivOfConj {S : Type} [Group S] {s₀ s : S} (g : S)
    (hs : s = g * s₀ * g⁻¹) :
    ↥(Subgroup.centralizer ({s} : Set S)) ≃* ↥(Subgroup.centralizer ({s₀} : Set S)) :=
  ((MulAut.conj g⁻¹).subgroupMap (Subgroup.centralizer ({s} : Set S))).trans
    (MulEquiv.subgroupCongr (by
      ext y
      simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx' : x * s = s * x := hx
        change g⁻¹ * x * g⁻¹⁻¹ * s₀ = s₀ * (g⁻¹ * x * g⁻¹⁻¹)
        rw [hs] at hx'
        calc g⁻¹ * x * g⁻¹⁻¹ * s₀ = g⁻¹ * (x * (g * s₀ * g⁻¹)) * g := by group
          _ = g⁻¹ * ((g * s₀ * g⁻¹) * x) * g := by rw [hx']
          _ = s₀ * (g⁻¹ * x * g⁻¹⁻¹) := by group
      · intro hy
        refine ⟨g * y * g⁻¹, ?_, ?_⟩
        · rw [hs]
          have hy' : y * s₀ = s₀ * y := hy
          calc g * y * g⁻¹ * (g * s₀ * g⁻¹) = g * (y * s₀) * g⁻¹ := by group
            _ = g * (s₀ * y) * g⁻¹ := by rw [hy']
            _ = g * s₀ * g⁻¹ * (g * y * g⁻¹) := by group
        · change g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y
          group))

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster
