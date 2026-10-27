module

public import CFSG.Quasithin.Vol2.Ch8Sec3Statements
public import CFSG.Quasithin.Vol2.Ch3Sec2Wreath
public import CFSG.Quasithin.Vol2.Ch7Lem734L3Wr
public import CFSG.Quasithin.Vol2.Ch1A3Proved
public import CFSG.Quasithin.Vol2.Ch3Sec2Lem322Eight
public import CFSG.Quasithin.Vol2.Ch7E61
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin

namespace H

namespace L3Wr

open CFSG.Open Matrix CFSG.Quasithin.H13

theorem zero_ne_one_fin3 : (0 : Fin 3) ≠ 1 := by decide

@[expose] noncomputable def sTr : MulAut WMod := rho (tr 0 1 zero_ne_one_fin3, 1)

theorem sTr_mem_img : sTr ∈ img := rho_mem_img _

theorem sTr_apply_of_row_eq_zero {X : WMod} (hX : ∀ k, Multiplicative.toAdd X 1 k = 0) :
    sTr X = X := by
  apply Multiplicative.toAdd.injective
  rw [sTr, toAdd_rho, mat_tr, mat_one, Matrix.transpose_one, Matrix.mul_one, Matrix.transvection,
    Matrix.add_mul, Matrix.one_mul, add_eq_left]
  ext i k
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [Matrix.single_apply]
  split_ifs with h
  · rw [← h.2, hX, mul_zero]
  · rw [zero_mul]

theorem toAdd_sTr (X : WMod) :
    Multiplicative.toAdd (sTr X) =
      Matrix.transvection 0 1 (1 : ZMod 2) * Multiplicative.toAdd X := by
  rw [sTr, toAdd_rho, mat_tr, mat_one, Matrix.transpose_one, Matrix.mul_one]

theorem sTr_mul_self : sTr * sTr = 1 := by
  refine MulEquiv.ext fun X => ?_
  rw [MulAut.mul_apply, MulAut.one_apply]
  apply Multiplicative.toAdd.injective
  rw [toAdd_sTr, toAdd_sTr, ← Matrix.mul_assoc,
    Matrix.transvection_mul_transvection_same (0 : Fin 3) 1 zero_ne_one_fin3]
  have : (1 : ZMod 2) + 1 = 0 := by decide
  rw [this, Matrix.transvection_zero, Matrix.one_mul]

theorem sTr_ne_one : sTr ≠ 1 := by
  intro h
  have h1 := congrArg (fun φ : MulAut WMod =>
    Multiplicative.toAdd (φ (Multiplicative.ofAdd (Matrix.single (1 : Fin 3) (0 : Fin 3)
      (1 : ZMod 2))))) h
  simp only [toAdd_sTr, MulAut.one_apply, toAdd_ofAdd] at h1
  have h2 := congrFun (congrFun h1 0) 0
  rw [Matrix.transvection, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply,
    Matrix.single_mul_single_same] at h2
  simp at h2

theorem orderOf_sTr : orderOf sTr = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine orderOf_eq_prime ?_ sTr_ne_one
  rw [sq, sTr_mul_self]

theorem card_fixV_sTr_ge : 64 ≤ Nat.card ↥(fixV (Subgroup.zpowers sTr)) := by
  classical
  let f : (Fin 2 → Fin 3 → ZMod 2) → Matrix (Fin 3) (Fin 3) (ZMod 2) := fun r =>
    Matrix.of fun i k => Fin.insertNth (α := fun _ : Fin 3 => Fin 3 → ZMod 2) (1 : Fin 3) 0 r i k
  have hf1 : ∀ r k, f r 1 k = 0 := fun r k => by
    simp only [f, Matrix.of_apply, Fin.insertNth_apply_same, Pi.zero_apply]
  have hf2 : ∀ r j k, f r ((1 : Fin 3).succAbove j) k = r j k := fun r j k => by
    simp only [f, Matrix.of_apply, Fin.insertNth_apply_succAbove]
  let ψ : (Fin 2 → Fin 3 → ZMod 2) → ↥(fixV (Subgroup.zpowers sTr)) := fun r =>
    ⟨Multiplicative.ofAdd (f r), by
      rw [mem_fixV_zpowers]
      exact sTr_apply_of_row_eq_zero (hf1 r)⟩
  have hψ : Function.Injective ψ := by
    intro r r' h
    have h1 : f r = f r' := congrArg (fun w : ↥(fixV (Subgroup.zpowers sTr)) =>
      Multiplicative.toAdd (w : WMod)) h
    funext j k
    rw [← hf2 r j k, ← hf2 r' j k, h1]
  have h1 := Nat.card_le_card_of_injective ψ hψ
  have h2 : Nat.card (Fin 2 → Fin 3 → ZMod 2) = 64 := by
    simp [Nat.card_eq_fintype_card]
  rwa [h2] at h1

theorem rkIdx_fixV_sTr_le : rkIdx (fixV (Subgroup.zpowers sTr)) ≤ 3 := by
  have h1 := Subgroup.index_mul_card (fixV (Subgroup.zpowers sTr))
  rw [card_WMod] at h1
  have hpos : 0 < (fixV (Subgroup.zpowers sTr)).index :=
    Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h2 : (fixV (Subgroup.zpowers sTr)).index ≤ 8 := by
    by_contra h
    push Not at h
    have := Nat.mul_lt_mul_of_lt_of_le h card_fixV_sTr_ge (by norm_num)
    omega
  unfold rkIdx
  calc padicValNat 2 (fixV (Subgroup.zpowers sTr)).index
      ≤ Nat.log 2 (fixV (Subgroup.zpowers sTr)).index := padicValNat_le_nat_log _
    _ ≤ Nat.log 2 (2 ^ 3) := Nat.log_mono_right (by norm_num; exact h2)
    _ = 3 := Nat.log_pow (by norm_num) 3

theorem mParam_le_three {X : Subgroup (MulAut WMod)} (hX : img ≤ X) : E3.mParam X ≤ 3 := by
  have hsX : sTr ∈ X := hX sTr_mem_img
  have hev : Even (Nat.card X) := by
    have h := orderOf_dvd_natCard (⟨sTr, hsX⟩ : ↥X)
    rw [Subgroup.orderOf_mk, orderOf_sTr] at h
    exact even_iff_two_dvd.2 h
  unfold E3.mParam
  split_ifs with h
  · have hmem : rkIdx (fixV (Subgroup.zpowers sTr)) ∈ {n : ℕ | ∃ t ∈ X, orderOf t = 2 ∧
        n = rkIdx (fixV (Subgroup.zpowers t))} := ⟨sTr, hsX, orderOf_sTr, rfl⟩
    exact (Nat.sInf_le hmem).trans rkIdx_fixV_sTr_le
  · exact absurd hev h

theorem H44_L3Wreath_mParam_le {V : Type*} [CommGroup V] {H M : Subgroup (MulAut V)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H) (hHM : H ≤ M) : E3.mParam M ≤ 3 := by
  obtain ⟨e, he⟩ := exists_model hreal
  rw [← mParam_map_congrHom e M]
  exact mParam_le_three (he ▸ Subgroup.map_mono hHM)

end L3Wr

end H

namespace H13

open CFSG.Open CFSG.Quasithin.E3
open scoped IsMulCommutative

theorem stmt8_3_2_of
    (h63 : ASInputs.AS_E_6_3) : Stmt8_3_2 := by
  intro G _ _ T L I hyp _ _ hrow hV
  have h3228 : Stmt3_2_2_eight := stmt3_2_2_eight_proved
  have hmod : StmtFSUModule := stmtFSUModule_of_eight h3228
  obtain ⟨-, hN⟩ := hmod G T L I hyp.fsu
  have hNM := normalizer_fsuV_le_fsuM a37ForSQTK_proved a38ForSQTK_proved a39ForSQTK_proved
    hyp.fsu hV hN
  obtain ⟨-, hTI⟩ := isTISetUnder_fsuV_of_row711L3Wreath hyp.fsu hrow
  have hm3 : 3 ≤ mParam (autI hV ⊤) := stmt7_2_1_m_L3Wreath G T L I hyp hV hN hNM _ hrow
  have hm3' : mParam (autI hV ⊤) ≤ 3 := by
    obtain ⟨-, hreal⟩ := hrow
    have hL : (tensorPairModel H.L3Wr.SL32 H.L3Wr.SL32).RealizesMod (V := IntMod (fsuV T I) hV)
        (autI hV (fsuL0 T L)) := hreal
    exact H.L3Wr.H44_L3Wreath_mParam_le hL (autI_fsuL0_le hV)
  have hm : mParam (autI hV ⊤) = 3 := le_antisymm hm3' hm3
  have hr : (mParam (autI hV ⊤) : ℕ∞) ≤ rParam (fsuV T I) :=
    mParam_le_rParam_of_ti a37ForSQTK_proved a38ForSQTK_proved a39ForSQTK_proved hmod h3228 h63
      hyp hTI hV (by omega)
  unfold sParam
  rw [min_eq_right hr, hm]
  rfl

end H13

end CFSG.Quasithin
