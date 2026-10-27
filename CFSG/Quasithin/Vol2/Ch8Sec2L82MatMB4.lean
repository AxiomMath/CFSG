module

public import CFSG.Quasithin.Vol2.Ch8Sec2L828TMB4
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB4S
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB4D
public import CFSG.Quasithin.Vol2.Ch8Sec2L82MatMB4T

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.LU CFSG.Quasithin.H.LU24
  CFSG.Quasithin.E3 CFSG.Quasithin.H13.Mat

theorem mb4_828_proved :
    MB4_828 := by
  intro V _ _ H X hXN hXe hall
  obtain ⟨h, hX, hfX⟩ := hall
  obtain ⟨e, hH, hU⟩ := row3_classify hXN hXe h hX hfX
  have hS := card_stab_US_le
  have hnorm : Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut W11)) :
      Set (MulAut W11)) = (rhoC11 AutPerm le_rfl).range :=
    (congrArg (fun K : Subgroup (MulAut W11) => Subgroup.normalizer (K : Set (MulAut W11))) hH).trans
      normalizer_rhoC11_autPerm
  have hXs : X.map (congrHom e) ≤ (rhoC11 AutPerm le_rfl).range :=
    (map_le_normalizer_congrHom e hXN).trans hnorm.le
  have hXN' : X.map (congrHom e) ≤
      Subgroup.normalizer (((rhoC11 AutPerm le_rfl).range : Subgroup (MulAut W11)) :
        Set (MulAut W11)) := hXs.trans Subgroup.le_normalizer
  refine ⟨?_, ?_⟩
  ·
    intro g hg
    have h1 : congrHom e g ∈ Subgroup.normalizer
        ((H.map (congrHom e) : Subgroup (MulAut W11)) : Set (MulAut W11)) :=
      map_le_normalizer_congrHom e (le_refl _) (Subgroup.mem_map_of_mem _ hg)
    have h2 : congrHom e g ∈ (rhoC11 AutPerm le_rfl).range := hnorm.le h1
    have h3 : congrHom e g ∈ H.map (congrHom e) := hH.symm.le h2
    exact (Subgroup.mem_map_iff_mem (congrHom_injective e)).1 h3
  · have hXc : Nat.card ↥X = 2 ^ 6 := hX ▸ card_eq_of_isElemAbelian2 hXe
    have hXc' : Nat.card ↥(X.map (congrHom e)) = 2 ^ 6 := by
      rw [Subgroup.card_map_of_injective (congrHom_injective e)]; exact hXc
    have hX2 : IsPGroup 2 ↥(X.map (congrHom e)) := hXe.isPGroup.map _
    have hB : s828BPrime (rhoC11 AutPerm le_rfl).range (X.map (congrHom e)) =
        maskSub 11 mb3L10 := row3_std_B hS _ hXN' hU
    have hPS' : perfectCore ((rhoC11 AutPerm le_rfl).range ⊓ stabSub US) = imgCd sxP0 :=
      (lu_code_std hS).1
    obtain ⟨g, hg, hconj⟩ := mb4_conj_into_KS
    have hc := mb4_std_c_of ⟨mb4T, g, mb4T_mem, hg, mb4T_sq, mb4T_stab, mb4T_inv_sxZ, hconj⟩
      centH_le_P0 (X.map (congrHom e)) hXs hX2 hXc' hU
    have hb := mb4_std_b_of mb4_comm_sxZ_sxG1 mb4_b4
    have hbc : MB4bc (rhoC11 AutPerm le_rfl).range (X.map (congrHom e)) :=
      MB4bc.of_std hU hPS' hB hb hc
    exact mb4bc_of_map' e H X _ _ hH rfl hbc

end CFSG.Quasithin.H13
