module

public import CFSG.Quasithin.AppendixH.H9.GLBasics
public import CFSG.Quasithin.AppendixH.H9.PairStabilizer.StabilizerSubgroups

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.PairStab

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH.AutPair

variable {m : ℕ}

private theorem relIndex_inf_Lg_eq_two {H : Subgroup (MulAut (PairN (m + 1)))}
    (hH : H ≤ Mg (m + 1)) {t : MulAut (PairN (m + 1))} (ht : t ∈ H)
    (htL : t ∉ Lg (m + 1)) : (H ⊓ Lg (m + 1)).relIndex H = 2 := by
  have hcomm : (H ⊓ Lg (m + 1)).relIndex H = (Lg (m + 1)).relIndex H := by
    rw [inf_comm, Subgroup.inf_relIndex_right]
  rw [hcomm]
  have hLgM : (Lg (m + 1)).relIndex (Mg (m + 1)) ≠ 0 := by
    rw [relIndex_Lg_Mg (by omega)]
    norm_num
  have hle : (Lg (m + 1)).relIndex H ≤ 2 := by
    have h := Subgroup.relIndex_le_of_le_right (H := Lg (m + 1)) (K := H)
      (L := Mg (m + 1)) hH hLgM
    rw [relIndex_Lg_Mg (by omega)] at h
    exact h
  have hne1 : (Lg (m + 1)).relIndex H ≠ 1 := by
    intro h1
    exact htL (((Subgroup.relIndex_eq_one).1 h1) ht)
  have hne0 : (Lg (m + 1)).relIndex H ≠ 0 := by
    intro h0
    have hcard := Subgroup.relIndex_mul_card (H := Lg (m + 1)) (K := H)
    rw [h0, zero_mul] at hcard
    exact (Nat.card_pos (α := ↥H)).ne' hcard.symm
  omega

theorem relIndex_range_Mv : (leviAct m).range.relIndex
    (Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) = 2 := by
  have hHinf : (Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) ⊓ Lg (m + 1)
      = (leviAct m).range := by
    have hEq : (Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) ⊓ Lg (m + 1)
        = Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m))) := by
      ext x
      simp only [Subgroup.mem_inf]
      constructor
      · rintro ⟨⟨_, hxC⟩, hxL⟩; exact ⟨hxL, hxC⟩
      · rintro ⟨hxL, hxC⟩; exact ⟨⟨Lg_le_Mg (n := m + 1) hxL, hxC⟩, hxL⟩
    rw [hEq, Lg_inf_centSub_eq_range]
  have h := relIndex_inf_Lg_eq_two
    (H := Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) inf_le_left
    tInv_mem_Mv (tInv_not_mem_Lg (m := m))
  rw [hHinf] at h
  exact h

theorem relIndex_Pv_Sv : (Pv m).relIndex (Sv m) = 2 := by
  have h := relIndex_inf_Lg_eq_two (H := Sv m) (Sv_le_Mv.trans inf_le_left)
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers (tInv m))) (tInv_not_mem_Lg (m := m))
  rw [Sv_inf_Lg] at h
  exact h

theorem isPGroup_Pv : IsPGroup 2 (Pv m) := by
  refine IsPGroup.of_card (n := m * (m - 1) / 2) ?_
  rw [Pv, Subgroup.card_map_of_injective leviAct_injective, card_utriGL]

theorem isPGroup_Sv : IsPGroup 2 (Sv m) := by
  have hPvle : Pv m ≤ Sv m := le_sup_left
  have hcard := Subgroup.relIndex_mul_card (H := Pv m) (K := Sv m)
  rw [relIndex_Pv_Sv, inf_eq_left.mpr hPvle] at hcard
  have hPvcard : Nat.card (Pv m) = 2 ^ (m * (m - 1) / 2) := by
    rw [Pv, Subgroup.card_map_of_injective leviAct_injective, card_utriGL]
  refine IsPGroup.of_card (n := 1 + m * (m - 1) / 2) ?_
  rw [← hcard, hPvcard, pow_add]
  norm_num

theorem isSylowIn_Pv_range : IsSylowIn 2 (Pv m) (leviAct m).range := by
  refine ⟨Pv_le_range, isPGroup_Pv, ?_⟩
  have hri : (Pv m).relIndex (leviAct m).range = (utriGL m).relIndex ⊤ := by
    rw [Pv, MonoidHom.range_eq_map]
    exact Subgroup.relIndex_map_map_of_injective (utriGL m) ⊤ leviAct_injective
  rw [hri]
  exact (isSylowIn_utriGL m).not_dvd_relIndex

theorem isSylowIn_Sv_Mv :
    IsSylowIn 2 (Sv m) (Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) := by
  refine ⟨Sv_le_Mv, isPGroup_Sv, ?_⟩
  have h1 := Subgroup.relIndex_mul_relIndex (H := Pv m) (K := Sv m)
    (L := Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) le_sup_left Sv_le_Mv
  have h2 := Subgroup.relIndex_mul_relIndex (H := Pv m) (K := (leviAct m).range)
    (L := Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) Pv_le_range range_le_Mv
  rw [relIndex_Pv_Sv] at h1
  rw [relIndex_range_Mv] at h2
  have hcancel : (Sv m).relIndex
      (Mg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) (ez m)))) =
      (Pv m).relIndex (leviAct m).range := by
    omega
  rw [hcancel]
  exact (isSylowIn_Pv_range (m := m)).not_dvd_relIndex

theorem twoResidual_range (hm : 3 ≤ m) :
    twoResidual (leviAct m).range = (leviAct m).range := by
  haveI : Group.IsPerfect (GL (Fin m) (ZMod 2)) := isPerfect_GL_two hm
  exact twoResidual_eq_self_of_isPerfect (Group.IsPerfect.range (leviAct m))

end CFSG.ASVolI.ChH.PairStab
