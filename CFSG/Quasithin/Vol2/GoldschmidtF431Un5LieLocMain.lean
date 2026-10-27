module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLieLocMap
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieBrA
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieLocF
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieAutC
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieClsC
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylF
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5LieSylP

public noncomputable section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Quasithin.H13.F431.Un.L5

section Hyp

variable {K : Type} [Field K] (h : UnitaryFieldData 2 2 K)

theorem unStdLoc_u5Y :
    UnStdLoc (hypPSU h 2 1) (hypProjUnitriangular h 2 1) (z5Y h) (t5Y h) (vY h) (ucY h) (rY h)
      (kY h) := by
  have := h.charP
  have hf : 2 ≤ 2 := le_rfl
  exact
    { comm := comm_zt
      sylow_t := syl_isSylowTwoOf h (fun x hx => syl_cent_decomp h hx)
        (fun x hU hx => syl_uni_decomp h hU hx)
      V_le := vY_le_Ct
      V_aut := fun φ hφ v hv => aut_vY h φ hφ v hv
      V_ab := fun a ha b hb => vY_ab ha hb
      V_sq := fun a ha => vY_sq ha
      z_V := z5Y_mem_vY
      U_le := ucY_le_vY
      U_aut := fun φ hφ u hu => aut_ucY h φ hφ u hu
      t_U := t5Y_mem_ucY
      K_le := kY_le_Ct
      K_perf := kY_perfect hf
      V_K := vY_le_kY
      K_cent := fun k hk u hu => kY_cent_ucY hk hu
      coset := coset_Y h hf
      nonsolv := nonsolv_Y hf
      R_le := rY_le_vY
      R_two := R_two_Y h hf
      R_cls := R_cls_Y h
      R_U := R_U_Y h
      z_cent := fun y hy => z5Y_cent hy
      P_U := fun y hy u hu => P_U_Y hy hu }

end Hyp

section Datum

variable {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ 2) ^ 2)
  (ζ : traceZero (unitaryInvolution F 2 2)) [Fact ((ζ : F) ≠ 0)]

theorem un5StdLoc_datum :
    ∃ V Uc R K : Subgroup (SU (unitaryInvolution F 2 2) 5 ⧸
        Subgroup.center (SU (unitaryInvolution F 2 2) 5)),
      UnStdLoc _ (un5System hF ζ).U (un5Eps hF ζ (z5Y (un5FD hF)))
        (un5Eps hF ζ (t5Y (un5FD hF))) V Uc R K := by
  have := LL.UnStdLoc.map (un5Eps hF ζ) (unStdLoc_u5Y (un5FD hF))
  rw [un5Eps_map_U] at this
  exact ⟨_, _, _, _, this⟩

end Datum

end CFSG.Quasithin.H13.F431.Un
