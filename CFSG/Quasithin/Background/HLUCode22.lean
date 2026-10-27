module

public import CFSG.Quasithin.Background.HLUBase
public import CFSG.Quasithin.Background.HParabCode22

public section

namespace CFSG.Quasithin.H.Code22

open CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.ModChk
  CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.Coc CFSG.Quasithin.H.Parab CFSG.Quasithin.H.LU CFSG.QuasithinUnique.A5.Delta5

@[expose] noncomputable def rhoA : MulAut W10 := rhoC10 mog22 mog22_le_mog22plus ⟨hbA, hbA_mem⟩

@[expose] noncomputable def rhoB : MulAut W10 := rhoC10 mog22 mog22_le_mog22plus ⟨hbB, hbB_mem⟩

theorem rhoA_mem : rhoA ∈ imgC hbQ := ⟨⟨hbA, hbA_mem⟩, Subgroup.mem_subgroupOf.2 hbA_mem_Q, rfl⟩

theorem rhoB_mem : rhoB ∈ imgC hbQ := ⟨⟨hbB, hbB_mem⟩, Subgroup.mem_subgroupOf.2 hbB_mem_Q, rfl⟩

theorem actsBy_rhoA : ActsBy rhoA hbACols := actsBy_rho_arr hbA_mem hasArr_hbA hbCols_eq.1

theorem actsBy_rhoB : ActsBy rhoB hbBCols := actsBy_rho_arr hbB_mem hasArr_hbB hbCols_eq.2.1

theorem imgC_hbQ_le_stab : imgC hbQ ≤ stabSub UC := imgC_hbQ_le.trans inf_le_right

theorem card_autSub_hbQ_le :
    Nat.card ↥(autSub (imgC hbQ) UC) ≤ 60 := by
  have : Finite (MulAut W10) := finite_mulAut_z (V := W10)
  have h : Nat.card ↥(autSub (imgC hbQ) UC) * Nat.card ↥(imgC hbQ ⊓ centSub UC) = 960 :=
    (card_autSub_mul imgC_hbQ_le_stab).trans card_imgC_hbQ
  have hle : imgC Q16P ≤ imgC hbQ ⊓ centSub UC :=
    le_inf (imgC_mono Q16P_le_hbQ) fun φ hφ => (imgC_Q16P_le_cent hφ).2
  have h16 : 16 ≤ Nat.card ↥(imgC hbQ ⊓ centSub UC) :=
    card_imgC_Q16P ▸ Subgroup.card_le_of_le hle
  have h1 : Nat.card ↥(autSub (imgC hbQ) UC) * 16 ≤ 960 := h ▸ Nat.mul_le_mul_left _ h16
  omega

@[expose] def bcM22 : List ℕ := [0, 0, 0, 0, 30, 0, 0, 5, 18, 3]

theorem luM22_data : ∀ m ∈ combos hbU0Basis,
    (actM bcM22 m < 2 ^ 5 ∧ (actM bcM22 m = 0 → m = 0) ∧ ∑ i : Fin 5, bvec 5 (actM bcM22 m) i = 0) ∧
    actM hbACols (actM hbBCols m) ∈ combos hbU0Basis ∧
    actM hbACols (actM hbACols m) ∈ combos hbU0Basis ∧
    ∀ i : Fin 5, bvec 5 (actM bcM22 (actM hbACols (actM hbBCols m))) i =
        bvec 5 (actM bcM22 m) (a0⁻¹ i) ∧
      bvec 5 (actM bcM22 (actM hbACols (actM hbACols m))) i = bvec 5 (actM bcM22 m) (b0⁻¹ i) := by
  decide +kernel

theorem card_UC : Nat.card ↥UC = 16 := by
  rw [card_maskSub hbU0Basis_lt (by decide +kernel)]
  rfl

@[expose] noncomputable def luBeta : ↥UC ≃* ↥(G6.coreMod 5) :=
  maskEquiv 10 5 hbU0Basis (G6.coreMod 5) bcM22 hbU0Basis_lt
    (fun m hm => G6.mem_coreMod.2 (luM22_data m hm).1.2.2)
    (fun m hm => ⟨(luM22_data m hm).1.1, (luM22_data m hm).1.2.1⟩)
    (by rw [card_coreMod_five, card_UC])

theorem luBeta_toW (s : ↥UC) {m : ℕ} (hm : m ∈ combos hbU0Basis) (hs : (s : W10) = toW 10 m) :
    ((luBeta s : ↥(G6.coreMod 5)) : G6.PermMod 5) = toW 5 (actM bcM22 m) :=
  maskEquiv_apply s hm hs

@[expose] noncomputable def luX : MulAut ↥UC :=
  resHom UC ⟨rhoA * rhoB, imgC_hbQ_le_stab ((imgC hbQ).mul_mem rhoA_mem rhoB_mem)⟩

@[expose] noncomputable def luY : MulAut ↥UC :=
  resHom UC ⟨rhoA * rhoA, imgC_hbQ_le_stab ((imgC hbQ).mul_mem rhoA_mem rhoA_mem)⟩

theorem luX_mem : luX ∈ autSub (imgC hbQ) UC :=
  mem_autSub.2 ⟨_, (imgC hbQ).mul_mem rhoA_mem rhoB_mem, rfl⟩

theorem luY_mem : luY ∈ autSub (imgC hbQ) UC :=
  mem_autSub.2 ⟨_, (imgC hbQ).mul_mem rhoA_mem rhoA_mem, rfl⟩

theorem luBeta_X (s : ↥UC) :
    ((luBeta (luX s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 a0 (luBeta s) := by
  obtain ⟨m, hm, hms⟩ := s.2
  have hx : ((luX s : ↥UC) : W10) = toW 10 (actM hbACols (actM hbBCols m)) := by
    show (rhoA * rhoB) (s : W10) = _
    rw [← hms, MulAut.mul_apply, actsBy_rhoB, actsBy_rhoA]
  rw [luBeta_toW _ (luM22_data m hm).2.1 hx, luBeta_toW s hm hms.symm]
  exact permAct_toW_eq fun i => ((luM22_data m hm).2.2.2 i).1

theorem luBeta_Y (s : ↥UC) :
    ((luBeta (luY s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 b0 (luBeta s) := by
  obtain ⟨m, hm, hms⟩ := s.2
  have hy : ((luY s : ↥UC) : W10) = toW 10 (actM hbACols (actM hbACols m)) := by
    show (rhoA * rhoA) (s : W10) = _
    rw [← hms, MulAut.mul_apply, actsBy_rhoA, actsBy_rhoA]
  rw [luBeta_toW _ (luM22_data m hm).2.2.1 hy, luBeta_toW s hm hms.symm]
  exact permAct_toW_eq fun i => ((luM22_data m hm).2.2.2 i).2

end CFSG.Quasithin.H.Code22
