module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBMD3

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M3

open CFSG.QuasithinUnique.A6Facts Subgroup CFSG.Quasithin

set_option maxRecDepth 100000

theorem t_gens : ([u1, v1, u2, v2] ++ bGens 3).map code = tGenC := by decide

theorem t_build : tLit = Core.buildCodes cid tGenC tTree := by decide +kernel

theorem t_tbl : Core.tblCheckC cid tGenC tLit tTbl = true := by decide +kernel

theorem t_nodup : tLit.Nodup := by decide +kernel

theorem t_length : tLit.length = 512 := by decide +kernel

theorem t_desc : LDesc (TB 3) tLit := ldesc_of_closure t_gens t_build t_tbl

theorem g_norm : GNormChk (([a1, b1, a2, b2] ++ bGens 3).map code) = true := by decide +kernel

theorem t_perm : TPermChk (([u1, v1, u2, v2] ++ bGens 3).map code) = true := by decide +kernel

theorem t0_gen_T : ∀ c ∈ t0Gen, c ∈ tLit := by decide +kernel

theorem t0_build : t0Lit = Core.buildCodes cid t0Gen t0Tree := by decide +kernel

theorem t0_tbl : Core.tblCheckC cid t0Gen t0Lit t0Tbl = true := by decide +kernel

theorem t0_gen : ∀ c ∈ t0Gen, c ∈ t0Lit := by decide +kernel

theorem t0_chk : T0Chk tLit t0Gen t0Lit = true := by decide +kernel

theorem t0_desc : LDesc (closureC t0Gen) t0Lit := by
  have h := t0_tbl
  rw [t0_build] at h ⊢
  exact ldesc_closureC (fun c hc => by
    obtain ⟨σ, -, e⟩ := t_desc.surj c (t0_gen_T c hc)
    exact ⟨σ, e⟩) h

theorem t0_data : T0Data tLit t0Gen t0Lit := ⟨t0_desc, t0_gen, t0_chk⟩

theorem t_card : Nat.card (TB 3) = 2 ^ 9 := by
  rw [t_desc.card t_nodup, t_length]
  norm_num

theorem t_sylow : IsSylowIn 2 (Tb 3) ⊤ := sylow_T 3 g_norm t_card

theorem pair_chk : PairChk tLit pairW = true := by decide +kernel

theorem close_inv : CloseInvChk tLit [zLit] closeW = true := by decide +kernel

theorem z_chk : ZChk tLit zLit = true := by decide +kernel

theorem z_five : FiveChk tLit t0Lit zLit zFive.1 zFive.2.1 zFive.2.2.1 zFive.2.2.2.1 zFive.2.2.2.2 =
    true := by
  decide +kernel

end CFSG.LocalAnalysis.WeakClosure81.NGM.MF.M3
