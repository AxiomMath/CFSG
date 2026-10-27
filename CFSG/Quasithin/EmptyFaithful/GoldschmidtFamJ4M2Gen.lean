module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Abs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Lat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Om
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Q

public section

namespace CFSG.Quasithin.J4M2

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4Loc
open CFSG.Sporadic.J4.QT2 (z0_mem_Zl)

theorem sigPerm_val {n : ℕ} (hn : n < 32) (i : Fin 77) :
    ((sigPerm n) i : ℕ) = (sigData[n]!)[i.val]! := by
  have h := chkSig_true
  unfold chkSig at h
  simp only [List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have h1 := h n hn i.val i.2
  have h2 : Fin.ofNat 77 i.val = i := Fin.ext (by simp)
  simp only [h2] at h1
  rw [h1]
  simp [List.getD_eq_getElem?_getD, List.getElem!_eq_getElem?_getD]
  rfl

theorem sigData_q : ∀ n < 12, ∀ i < 77, (sigData[n]!)[i]! = i := by decide +kernel

theorem sigPerm_q {n : ℕ} (hn : n < 12) : sigPerm n = 1 := by
  refine Equiv.ext fun i => Fin.ext ?_
  rw [sigPerm_val (by omega) i, sigData_q n hn i.val i.2]
  rfl

theorem rho_gE_perm
    (hF : J4Facts) {n : ℕ} (hn : n < 32) :
    rho hF ⟨gE n, gE_mem_M2 hF.mat hn⟩ = sigPerm n :=
  Equiv.ext fun i => Fin.ext (by rw [rho_gE hF n hn i, sigPerm_val hn i])

theorem sigPerm_mem_range
    (hF : J4Facts) {n : ℕ} (hn : n < 32) :
    sigPerm n ∈ (rho hF).range :=
  ⟨⟨gE n, gE_mem_M2 hF.mat hn⟩, rho_gE_perm hF hn⟩

theorem mem_range_of_eq
    (hF : J4Facts) {x : Equiv.Perm (Fin 77)} {n : ℕ}
    (hn : n < 32) (h : x = sigPerm n) : x ∈ (rho hF).range := by
  rw [h]
  exact sigPerm_mem_range hF hn

theorem Mbar_le_range
    (hF : J4Facts) : Mbar ≤ (rho hF).range := by
  rw [Mbar, Subgroup.closure_le]
  intro x hx
  simp only [oddPerms, tPerms, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    Set.mem_ofPred_eq, or_assoc] at hx
  rcases hx with h | h | h | h | h | h | h | h | h
  · exact mem_range_of_eq hF (n := 12) (by norm_num) h
  · exact mem_range_of_eq hF (n := 13) (by norm_num) h
  · exact mem_range_of_eq hF (n := 14) (by norm_num) h
  · exact mem_range_of_eq hF (n := 15) (by norm_num) h
  · exact mem_range_of_eq hF (n := 16) (by norm_num) h
  · exact mem_range_of_eq hF (n := 28) (by norm_num) h
  · exact mem_range_of_eq hF (n := 29) (by norm_num) h
  · exact mem_range_of_eq hF (n := 30) (by norm_num) h
  · exact mem_range_of_eq hF (n := 17) (by norm_num) h

theorem le_card_Mbar :
    887040 ≤ Nat.card ↥Mbar := by
  have h1 : Nat.card ↥MbarP ∣ Nat.card ↥Mbar := Subgroup.card_dvd_of_le MbarP_le_Mbar
  rw [card_MbarP] at h1
  obtain ⟨k, hk⟩ := h1
  have hpos : 0 < Nat.card ↥Mbar := Nat.card_pos
  have hk0 : k ≠ 0 := by
    rintro rfl
    omega
  have hk1 : k ≠ 1 := by
    rintro rfl
    apply Tbar_not_le_MbarP
    have : MbarP = Mbar :=
      Subgroup.eq_of_le_of_card_ge MbarP_le_Mbar (by rw [card_MbarP]; omega)
    rw [this]
    exact Tbar_le_Mbar
  omega

@[expose] noncomputable def Kker
    (hF : J4Facts) : Subgroup J := (rho hF).ker.map M2.subtype

@[expose] noncomputable def Kgrp : Subgroup J := Qgrp ⊔ Subgroup.zpowers cE

theorem Kgrp_le_Kker
    (hF : J4Facts) : Kgrp ≤ Kker hF := by
  refine sup_le ?_ ?_
  · rw [Qgrp, Subgroup.closure_le]
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨gE k, gE_mem_M2 hF.mat (by omega)⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, rho_gE_perm hF (by omega)]
    exact sigPerm_q hk
  · rw [Subgroup.zpowers_le]
    exact ⟨⟨cE, cE_mem_M2 hF.mat⟩, rho_cE hF, rfl⟩

theorem three_mul_dvd_card_Kgrp
    (hF : J4Facts) : 3 * 2 ^ 13 ∣ Nat.card ↥Kgrp := by
  have hQ : 2 ^ 13 ∣ Nat.card ↥Kgrp := by
    rw [← card_Qgrp hF.mat]
    exact Subgroup.card_dvd_of_le le_sup_left
  have h3 : 3 ∣ Nat.card ↥Kgrp := by
    have := Subgroup.orderOf_dvd_natCard Kgrp
      (show cE ∈ Kgrp from Subgroup.mem_sup_right (Subgroup.mem_zpowers cE))
    rwa [orderOf_cE hF.mat] at this
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 hQ

theorem card_Kker
    (hF : J4Facts) : Nat.card ↥(Kker hF) = Nat.card ↥(rho hF).ker :=
  Subgroup.card_map_of_injective M2.subtype_injective

theorem card_M2
    (hF : J4Facts) :
    Nat.card ↥M2 = 887040 * 24576 := by
  have h : Nat.card ↥M2 = 21799895040 :=
    CFSG.Sporadic.J4.QT2.card_centralizer_of_mem_Zl hF z0_mem_Zl
  rw [h]

theorem card_range_ker_rho
    (hF : J4Facts) : Nat.card (rho hF).range = 887040 ∧ Nat.card (rho hF).ker = 24576 := by
  refine card_eq_of_bounds (rho hF) ?_ ?_ (card_M2 hF)
  · exact le_card_Mbar.trans (Subgroup.card_le_of_le (Mbar_le_range hF))
  · have h1 := Nat.le_of_dvd Nat.card_pos (three_mul_dvd_card_Kgrp hF)
    have h2 := Subgroup.card_le_of_le (Kgrp_le_Kker hF)
    rw [card_Kker hF] at h2
    omega

theorem range_rho_eq
    (hF : J4Facts) : (rho hF).range = Mbar :=
  (Subgroup.eq_of_le_of_card_ge (Mbar_le_range hF)
    (by rw [(card_range_ker_rho hF).1]; exact le_card_Mbar)).symm

theorem card_Mbar
    (hF : J4Facts) : Nat.card ↥Mbar = 887040 := by
  rw [← range_rho_eq hF]
  exact (card_range_ker_rho hF).1

theorem Kgrp_eq_Kker
    (hF : J4Facts) : Kgrp = Kker hF := by
  refine Subgroup.eq_of_le_of_card_ge (Kgrp_le_Kker hF) ?_
  have h2 := Nat.le_of_dvd Nat.card_pos (three_mul_dvd_card_Kgrp hF)
  rw [card_Kker hF, (card_range_ker_rho hF).2]
  omega

theorem card_Kgrp
    (hF : J4Facts) : Nat.card ↥Kgrp = 3 * 2 ^ 13 := by
  rw [Kgrp_eq_Kker hF, card_Kker hF, (card_range_ker_rho hF).2]
  norm_num

theorem mem_Kgrp_iff
    (hF : J4Facts) (m : ↥M2) : (m : J) ∈ Kgrp ↔ rho hF m = 1 := by
  rw [Kgrp_eq_Kker hF, Kker]
  exact (Subgroup.mem_map_iff_mem M2.subtype_injective).trans (MonoidHom.mem_ker)

theorem rho_eq_one_iff
    (hF : J4Facts) (m : ↥M2) : rho hF m = 1 ↔ (m : J) ∈ Kgrp :=
  (mem_Kgrp_iff hF m).symm

end CFSG.Quasithin.J4M2
