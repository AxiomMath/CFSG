module

public import CFSG.LocalAnalysis.WeakClosure81.SixFour
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsSetting
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem w172_centralizer_le_conj {D : Data G} {V₀ V : Subgroup G} (hs : WeakClosureSetting D V₀ V)
    (hV₀ : V₀ ≠ ⊥) {g w : G} (hw : w ∈ conjSubgroup V₀ g) (hw1 : w ≠ 1) :
    Subgroup.centralizer ({w} : Set G) ≤ conjSubgroup D.M g := by
  intro y hy
  rw [mem_conjSubgroup_iff]
  have hw' : g * w * g⁻¹ ∈ V₀ := mem_conjSubgroup_iff.mp hw
  have hw1' : g * w * g⁻¹ ≠ 1 := fun h => hw1 (by simpa using h)
  have hc : g * y * g⁻¹ ∈ Subgroup.centralizer ({g * w * g⁻¹} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    calc g * y * g⁻¹ * (g * w * g⁻¹) = g * (y * w) * g⁻¹ := by group
      _ = g * (w * y) * g⁻¹ := by rw [hy]
      _ = g * w * g⁻¹ * (g * y * g⁻¹) := by group
  exact centralizer_le_M_of_mem_V₀ (hs.ti₀ hV₀).1 (hs.normalizer₀ hV₀) hw' hw1' hc

end CFSG.LocalAnalysis.WeakClosure81

end
