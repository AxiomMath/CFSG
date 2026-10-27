module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD0
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMGlue

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin

set_option maxRecDepth 100000

theorem t_gens : ([u1, v1, u2, v2] ++ bGens 0).map code = tGenC := by decide

theorem t_build : tLit = Core.buildCodes cid tGenC tTree := by decide +kernel

theorem t_tbl : Core.tblCheckC cid tGenC tLit tTbl = true := by decide +kernel

theorem t_nodup : tLit.Nodup := by decide +kernel

theorem t_length : tLit.length = 128 := by decide +kernel

theorem t_desc : LDesc (TB 0) tLit := ldesc_of_closure t_gens t_build t_tbl

theorem g_norm : GNormChk (([a1, b1, a2, b2] ++ bGens 0).map code) = true := by decide +kernel

theorem t_perm : TPermChk (([u1, v1, u2, v2] ++ bGens 0).map code) = true := by decide +kernel

theorem t0_chk : T0Chk tLit dGenC dLit = true := by decide +kernel

theorem d_gen : ∀ c ∈ dGenC, c ∈ dLit := by decide +kernel

theorem d_desc' : LDesc (closureC dGenC) dLit := by
  rw [← d_gens, closureC_map_code]
  exact d_desc

theorem t0_data : T0Data tLit dGenC dLit := ⟨d_desc', d_gen, t0_chk⟩

theorem t_card : Nat.card (TB 0) = 2 ^ 7 := by
  rw [t_desc.card t_nodup, t_length]
  norm_num

theorem t_sylow : IsSylowIn 2 (Tb 0) ⊤ := sylow_T 0 g_norm t_card

theorem pair_chk : PairChk tLit pairW = true := by decide +kernel

theorem close_inv : CloseInvChk tLit [k0.qLit, k1.qLit] closeW = true := by decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M0
