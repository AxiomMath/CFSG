module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Cover
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenResultsB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R16_47z (D : Data G) : Prop :=
  ∀ (V₀ V L : Subgroup G) (hV : IsElemAbelian 2 V), Sect16 D V₀ V L hV →
    Case167_1 D V₀ V hV L → L ∈ calC D.M → IsU4 (Bar2 L) 1 →
      ∃ x : IntMod V hV, Setup1645 D V hV x ∧ Concl1647 V x.val ∧ Concl1647a D V₀ V x.val

theorem sixteen_forty_z (D : Data G) (hSimple : RSimple153) (h127 : R127 D) (h119 : F11.R119 D)
    (h1217 : R1217 D) (hSchur : RSchurOm6) (h46 : R16_46 D) (h47z : R16_47z D)
    (hcl : R16_47_close D) : R16_40 D := by
  intro V₀ V L hV hS h1
  obtain ⟨K, hK, -, hSK, h1K, hU⟩ := exists_calC_cover D hSimple h127 h119 h1217 hSchur hS h1
  obtain ⟨x, hx, hc47, hc47a⟩ := h47z V₀ V K hV hSK h1K hK hU
  have hc46 := h46 V₀ V K hV hSK h1K hK hU x hx
  have hc47c := hcl V₀ V K hV hSK h1K hK hU x hx hc47 hc47a
  exact absurd (hc46.2.1 5 (by norm_num) (by norm_num)) (not_le.2 hc47c.2)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
