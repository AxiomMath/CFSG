module

public import CFSG.LocalAnalysis.WeakClosure81.W172Defs
public import CFSG.LocalAnalysis.WeakClosure81.W18ASSeven
public import CFSG.LocalAnalysis.WeakClosure81.W18Ctx
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5ASMaster

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

theorem calNIn_eq (c : MinCex172 D V₀ V H) : calNIn H D.T = {H ⊓ D.M} := by
  have hTH : D.T ≤ H := c.hyp.hyp171.2.1
  have hTM : D.T ≤ D.M := (CFSG.ABGLocalTools.isSylowOf_iff.1 D.sylowM).1
  have hlt : H ⊓ D.M < H :=
    lt_of_le_of_ne inf_le_left fun h => c.hyp.notLe (inf_eq_left.1 h)
  ext X
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hTX, hXH, hmax⟩
    have hXM : X ≤ D.M := c.le_M_of_lt hTX hXH
    refine eq_of_le_of_not_lt (le_inf hXH.le hXM) fun hXlt => ?_
    exact hlt.ne (hmax _ hXlt inf_le_left)
  · rintro rfl
    refine ⟨le_inf hTH hTM, hlt, fun Y hY hYH => ?_⟩
    by_contra hYne
    have hYM : Y ≤ D.M := c.le_M_of_lt ((le_inf hTH hTM).trans hY.le) (lt_of_le_of_ne hYH hYne)
    exact hY.not_ge (le_inf hYH hYM)

theorem inFSqAS_one (c : MinCex172 D V₀ V H) : InFSqAS 1 H :=
  inFSqAS_of_isSolvable c.hyp.isSylowIn_T c.calNIn_eq c.solv

theorem ctx188 (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) : Ctx188 D V₀ V H 1 2 where
  hyp := c.hyp
  h162 := h162
  mbar := c.mbar
  two_le := le_rfl
  bound := by
    have := (c.hyp.setting.pair.mBarGT_iff_lt_mBar 2).1 c.mbar
    omega
  not_inCalA := fun _ hAH hAab =>
    c.hyp.not_inCalA_of_inFSqAS (by norm_num : 1 < 2) c.inFSqAS_one hAH hAab

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
