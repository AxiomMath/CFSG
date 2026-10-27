module

public import CFSG.Quasithin.Background.HLUBase
public import CFSG.Quasithin.Background.HParabL34

public section

namespace CFSG.Quasithin.H.L34Z

open CFSG.Open CFSG.Fischer Matrix CFSG.Monster.Code CFSG.Quasithin.H.Mathieu
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.ZTrans CFSG.Quasithin.H.L3W9
  CFSG.Quasithin.H13.Ch9.Herm9 CFSG.Quasithin.H13.Ch9.L34M CFSG.Quasithin.H.Coc
  CFSG.Quasithin.H.Parab CFSG.Quasithin.H.LU CFSG.QuasithinUnique.A5.Delta5

theorem QW9_le_cent : QW9 ≤ P2 ⊓ centSub U0 := by
  intro φ hφ
  obtain ⟨t, ht, rfl⟩ := mem_QW9.1 hφ
  refine ⟨S1_le_P2 (mem_S1.2 ⟨4 * t, by omega, (rho9_vG_eq t).symm⟩), fun u hu => ?_⟩
  rw [← fixV_QW9] at hu
  exact hu _ (rho9_vG_mem ht)

theorem qw9_orbit4 : ((List.range 16).map fun t => actM (colsS1.getD (4 * t) []) 4).Nodup ∧
    ∀ t < 16, actM (colsS1.getD (4 * t) []) 4 < 2 ^ 9 := by
  decide +kernel

theorem le_card_cent_U0 : 16 ≤ Nat.card ↥(P2 ⊓ centSub U0) := by
  have : Finite (MulAut W9) := finite_mulAut_z (V := W9)
  have h := le_card_of_keys (K := P2 ⊓ centSub U0)
    (fun φ : MulAut W9 => Parab.maskOf 9 (φ (toW 9 4))) qw9_orbit4.1 (by
      intro k hk
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hk
      have ht' := List.mem_range.1 ht
      refine ⟨rho9 (vG t), QW9_le_cent (rho9_vG_mem ht'), ?_⟩
      show Parab.maskOf 9 (rho9 (vG t) (toW 9 4)) = _
      rw [rho9_toW_cols (vG t) (cols_vG ht') (by norm_num), Parab.maskOf_toW (qw9_orbit4.2 t ht')])
  simpa using h

theorem P2_le_stab : P2 ≤ stabSub U0 := P2_le.trans inf_le_right

theorem card_autSub_P2_le : Nat.card ↥(autSub P2 U0) ≤ 60 := by
  have h : Nat.card ↥(autSub P2 U0) * Nat.card ↥(P2 ⊓ centSub U0) = 960 :=
    (card_autSub_mul P2_le_stab).trans card_P2
  have h1 : Nat.card ↥(autSub P2 U0) * 16 ≤ 960 := h ▸ Nat.mul_le_mul_left _ le_card_cent_U0
  omega

@[expose] def bcL34 : List ℕ := [23, 27, 0, 18, 17, 0, 0, 0, 0]

theorem luL34_data : ∀ m ∈ combos U0Basis,
    (actM bcL34 m < 2 ^ 5 ∧ (actM bcL34 m = 0 → m = 0) ∧ ∑ i : Fin 5, bvec 5 (actM bcL34 m) i = 0) ∧
    actM colsY2 m ∈ combos U0Basis ∧
    actM colsX2 (actM colsY2 (actM colsX2 (actM colsY2 m))) ∈ combos U0Basis ∧
    ∀ i : Fin 5, bvec 5 (actM bcL34 (actM colsY2 m)) i = bvec 5 (actM bcL34 m) (a0⁻¹ i) ∧
      bvec 5 (actM bcL34 (actM colsX2 (actM colsY2 (actM colsX2 (actM colsY2 m))))) i =
        bvec 5 (actM bcL34 m) (b0⁻¹ i) := by
  decide +kernel

theorem card_U0 : Nat.card ↥U0 = 16 := by
  rw [card_maskSub U0Basis_lt (by decide +kernel)]
  rfl

@[expose] noncomputable def luBeta : ↥U0 ≃* ↥(G6.coreMod 5) :=
  maskEquiv 9 5 U0Basis (G6.coreMod 5) bcL34 U0Basis_lt
    (fun m hm => G6.mem_coreMod.2 (luL34_data m hm).1.2.2)
    (fun m hm => ⟨(luL34_data m hm).1.1, (luL34_data m hm).1.2.1⟩)
    (by rw [card_coreMod_five, card_U0])

theorem luBeta_toW (s : ↥U0) {m : ℕ} (hm : m ∈ combos U0Basis) (hs : (s : W9) = toW 9 m) :
    ((luBeta s : ↥(G6.coreMod 5)) : G6.PermMod 5) = toW 5 (actM bcL34 m) :=
  maskEquiv_apply s hm hs

@[expose] noncomputable def luX : MulAut ↥U0 := resHom U0 ⟨rho9 y2G, P2_le_stab y2_mem_P2⟩

@[expose] noncomputable def luY : MulAut ↥U0 :=
  resHom U0 ⟨rho9 x2G * rho9 y2G * rho9 x2G * rho9 y2G,
    P2_le_stab (P2.mul_mem (P2.mul_mem (P2.mul_mem x2_mem_P2 y2_mem_P2) x2_mem_P2) y2_mem_P2)⟩

theorem luX_mem : luX ∈ autSub P2 U0 := mem_autSub.2 ⟨_, y2_mem_P2, rfl⟩

theorem luY_mem : luY ∈ autSub P2 U0 :=
  mem_autSub.2 ⟨_, P2.mul_mem (P2.mul_mem (P2.mul_mem x2_mem_P2 y2_mem_P2) x2_mem_P2) y2_mem_P2,
    rfl⟩

theorem luBeta_X (s : ↥U0) :
    ((luBeta (luX s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 a0 (luBeta s) := by
  obtain ⟨m, hm, hms⟩ := s.2
  have hx : ((luX s : ↥U0) : W9) = toW 9 (actM colsY2 m) := by
    show rho9 y2G (s : W9) = _
    rw [← hms]
    exact actsBy_rho9_y2 m
  rw [luBeta_toW _ (luL34_data m hm).2.1 hx, luBeta_toW s hm hms.symm]
  exact permAct_toW_eq fun i => ((luL34_data m hm).2.2.2 i).1

theorem luBeta_Y (s : ↥U0) :
    ((luBeta (luY s) : ↥(G6.coreMod 5)) : G6.PermMod 5) = G6.permAct 5 b0 (luBeta s) := by
  obtain ⟨m, hm, hms⟩ := s.2
  have hy : ((luY s : ↥U0) : W9) =
      toW 9 (actM colsX2 (actM colsY2 (actM colsX2 (actM colsY2 m)))) := by
    show (rho9 x2G * rho9 y2G * rho9 x2G * rho9 y2G) (s : W9) = _
    rw [← hms, MulAut.mul_apply, MulAut.mul_apply, MulAut.mul_apply, actsBy_rho9_y2 m,
      actsBy_rho9_x2, actsBy_rho9_y2, actsBy_rho9_x2]
    rfl
  rw [luBeta_toW _ (luL34_data m hm).2.2.1 hy, luBeta_toW s hm hms.symm]
  exact permAct_toW_eq fun i => ((luL34_data m hm).2.2.2 i).2

end CFSG.Quasithin.H.L34Z
