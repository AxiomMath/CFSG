module

public import CFSG.LocalAnalysis.WeakClosure81.W18Ctx
public import CFSG.LocalAnalysis.WeakClosure81.W18ASSeven

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem ctx188_two_AS (h162 : W3Thm162Gt2 G) (h5_11 : Asch5_11AS)
    (h5_13 : Asch5_13AS) (c : MinCex183 D V₀ V H i) (h1 : ¬ Concl181 D V₀ V H) :
    Ctx188 D V₀ V H i 2 := by
  have hmb := (c.hyp.setting.pair.mBarGT_iff_lt_mBar 2).1 c.mBarGT_two
  have hi := c.hyp.i_le
  exact ⟨c.hyp, h162, c.mBarGT_two, by norm_num, by omega,
    fun A hAH hAab => c.not_inCalA_two_AS h5_11 h5_13 h1 hAH hAab⟩

theorem ctx188_three_AS (h162 : W3Thm162Gt2 G) (h5_11 : Asch5_11AS) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) : Ctx188 D V₀ V H i 3 := by
  have hmb := (c.hyp.setting.pair.mBarGT_iff_lt_mBar (i + 2)).1
    (not_concl182_iff.mp h2).2.1
  exact ⟨c.hyp, h162, c.mBarGT_two, by norm_num, by omega,
    fun A hAH hAab => c.not_inCalA_three_AS h5_11 h2 hAH hAab⟩

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
