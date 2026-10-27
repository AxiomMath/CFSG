module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs
import CFSG.LocalAnalysis.StandardType.GGHLAutomizer
import CFSG.LocalAnalysis.StandardType.GGRCLinRefl

public section

namespace CFSG.StandardType.HdRo7C

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem c2_lfixgen_holds : C2LFixGenLeaf := by
  intro G _ _ p B Bs x L D J y K hH _ hDL V _ _ ι hx
  obtain ⟨Λ, _, _, M, C, V', _, _, ι', φ, h, α, hM, hC, hlin, hrefl, hpair, ⟨f, hf⟩, hgen⟩ := hDL
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hH.1.tableB_facts.2.2.2.1
  constructor
  · intro a ha
    obtain ⟨φ₀, hφ₀, ha⟩ := Subgroup.mem_map.mp ha
    rw [← ha, ggLin_apply_ofMul, ggHLA_fixes_x hLx hx φ₀ hφ₀]
  · have hmap : (ggAutomizer L Bs).map (ggLin (p := p) ι) =
        Subgroup.closure (Set.range fun i : Λ => ggLin (p := p) ι (φ i)) := by
      rw [hgen, MonoidHom.map_closure, ← Set.range_comp]
      rfl
    refine le_antisymm ?_ ?_
    · rw [hmap]
      apply Subgroup.closure_mono
      rintro r ⟨i, rfl⟩
      exact ⟨Subgroup.subset_closure (Set.mem_range_self i),
        (ggRC_isReflection_iff_linRefl ι (φ i)).mp (hrefl i)⟩
    · apply (Subgroup.closure_le _).mpr
      rintro r ⟨hr, -⟩
      exact hr

end CFSG.StandardType.HdRo7C
