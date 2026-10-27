module

public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.MatrixSeedIdentification
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.SteinbergBQDeletedSelfNormalizing
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.SteinbergCCOddNilpotentDerived

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

namespace Lem7NQ

variable {G : Type} [Group G]

theorem le_normalizer_map {Y : Subgroup G} (X' : Subgroup ↥Y) [hn : X'.Normal] :
    Y ≤ Subgroup.normalizer ((X'.map Y.subtype : Subgroup G) : Set G) := by
  intro y hy
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨⟨y, hy⟩ * x' * ⟨y, hy⟩⁻¹, hn.conj_mem x' hx' _, rfl⟩
  · rintro ⟨x'', hx'', hxh⟩
    refine ⟨⟨y, hy⟩⁻¹ * x'' * ⟨y, hy⟩, ?_, ?_⟩
    · have := hn.conj_mem x'' hx'' ⟨y, hy⟩⁻¹
      rwa [inv_inv] at this
    · have hxh' : (x'' : G) = y * h * y⁻¹ := hxh
      show y⁻¹ * (x'' : G) * y = h
      rw [hxh']
      group

end Lem7NQ

open Lem7NQ

end CFSG.Quasithin.H13
