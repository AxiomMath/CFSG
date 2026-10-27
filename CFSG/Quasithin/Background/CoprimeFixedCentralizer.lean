module

public import CFSG.Quasithin.Background.A1cModuleCoprime

public section

namespace CFSG.Quasithin

open scoped Pointwise

theorem modFix_eq_bot_of_odd_of_modComm_eq_top
    {G V : Type*} [Group G] [CommGroup V] [MulDistribMulAction G V]
    {H C : Subgroup G} [Finite C]
    (hV : ∀ v : V, v ^ 2 = 1) (hC : Odd (Nat.card C))
    (hHC : H ≤ Subgroup.normalizer (C : Set G))
    (hcomm : modComm H (⊤ : Subgroup V) = ⊤)
    (hfixed : modFix C (⊤ : Subgroup V) ≤ modFix H (⊤ : Subgroup V)) :
    modFix C (⊤ : Subgroup V) = ⊥ := by
  classical
  let F := modFix C (⊤ : Subgroup V)
  let D := modComm C (⊤ : Subgroup V)
  have hcompl : IsCompl F D := XMod.isCompl_fixed_commOf_of_odd (A := ↥C) hC hV
  have hDinv : XMod.IsInv ↥H D := by
    intro h l hl
    have hsmul : (h : G) • D = D := by
      dsimp only [D]
      rw [smul_modComm (hHC h.2) (⊤ : Subgroup V), smul_top_eq_top]
    exact hsmul ▸ Subgroup.smul_mem_pointwise_smul l (h : G) D hl
  have hsup : D ⊔ F = ⊤ := by
    rw [sup_comm]
    exact hcompl.sup_eq_top
  have hcommD : modComm H D = ⊤ := by
    have h := XMod.commOf_sup_eq_of_le_fixed (A := ↥H) (L := D) (C := F) hfixed
    rw [hsup] at h
    rw [show modComm H D = XMod.commOf ↥H D from rfl, ← h,
      show XMod.commOf ↥H ⊤ = modComm H ⊤ from rfl, hcomm]
  have hDtop : D = ⊤ := by
    have hle : (⊤ : Subgroup V) ≤ D := by
      rw [← hcommD]
      exact XMod.commOf_le_of_isInv hDinv
    exact top_le_iff.mp hle
  have hFbot : F = ⊥ := by
    have h := hcompl.inf_eq_bot
    rwa [hDtop, inf_top_eq] at h
  exact hFbot

end CFSG.Quasithin
