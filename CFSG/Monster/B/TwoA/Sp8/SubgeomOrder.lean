
module

public import CFSG.Monster.B.TwoA.Sp8.SubgeomOrderBase

public import CFSG.Monster.B.TwoA.Sp8.SubgeomCard
public import CFSG.Monster.B.TwoA.Sp8.SubgeomVec

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

theorem natCard_isoSub_b0 {i : ℕ} (hi : i ≤ 4) :
    (Nat.card (IsoSub i) : ℚ) = isoGaussian 4 i 2 := by
  have h := natCard_isoSub b0_isAlt b0_nondegenerate finrank_V8 hi
  rwa [Nat.card_zmod] at h

theorem natCard_isoSub_values :
    Nat.card (IsoSub 1) = 255 ∧ Nat.card (IsoSub 2) = 5355 ∧
    Nat.card (IsoSub 3) = 11475 ∧ Nat.card (IsoSub 4) = 2295 := by
  obtain ⟨h1, h2, h3, h4⟩ := isoGaussian_four_two
  have e1 := natCard_isoSub_b0 (i := 1) (by norm_num)
  have e2 := natCard_isoSub_b0 (i := 2) (by norm_num)
  have e3 := natCard_isoSub_b0 (i := 3) (by norm_num)
  have e4 := natCard_isoSub_b0 (i := 4) (by norm_num)
  rw [h1] at e1
  rw [h2] at e2
  rw [h3] at e3
  rw [h4] at e4
  exact ⟨by exact_mod_cast e1, by exact_mod_cast e2, by exact_mod_cast e3, by exact_mod_cast e4⟩

@[expose] def conjOrbitEquiv
    (i : ℕ) (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    {F : Subgroup Dfull | ∃ k ∈ Xgrp, F = conjSub k (Echain i)} ≃ IsoSub i where
  toFun F := ⟨a8Vec F.1, by
    obtain ⟨k, hk, e⟩ := F.2
    rw [e]
    exact isotropic_a8Vec_conjSub ⟨k, hk⟩ h1 h4⟩
  invFun W := ⟨a8Grp W.1, by
    obtain ⟨x, hx⟩ := exists_conj_eq_a8Grp W.2.1 h1 h4 W.2.2
    exact ⟨x, x.2, hx.symm⟩⟩
  left_inv F := by
    apply Subtype.ext
    obtain ⟨k, hk, e⟩ := F.2
    show a8Grp (a8Vec F.1) = F.1
    rw [a8Grp_a8Vec]
    rw [e]
    exact conjSub_le_A8 hk (Echain_le_A8 h1 h4)
  right_inv W := Subtype.ext (a8Vec_a8Grp W.1)

theorem index_Kchain_subgroupOf_X
    (i : ℕ) (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    ((Kchain i).subgroupOf Xgrp).index = Nat.card (IsoSub i) := by
  rw [← ncard_conjSub_orbit Xgrp (Echain i), ← Nat.card_coe_set_eq,
    Nat.card_congr (conjOrbitEquiv i h1 h4)]

theorem natCard_X_inf_Kchain_mul
    (i : ℕ) (h1 : 1 ≤ i) (h4 : i ≤ 4) :
    Nat.card ↥(Xgrp ⊓ Kchain i) * Nat.card (IsoSub i) = 1589728887019929600 := by
  rw [natCard_inf_eq_subgroupOf, ← index_Kchain_subgroupOf_X i h1 h4, Subgroup.card_mul_index,
    natCard_Xgrp]

theorem natCard_X_inf_Kchain_two :
    Nat.card ↥(Xgrp ⊓ Kchain 2) = 2 ^ 41 * 135 := by
  have h := natCard_X_inf_Kchain_mul 2 (by norm_num) (by norm_num)
  rw [natCard_isoSub_values.2.1] at h
  generalize Nat.card ↥(Xgrp ⊓ Kchain 2) = n at h ⊢
  norm_num
  omega

theorem natCard_X_inf_Kchain_three :
    Nat.card ↥(Xgrp ⊓ Kchain 3) = 138538465099776 := by
  have h := natCard_X_inf_Kchain_mul 3 (by norm_num) (by norm_num)
  rw [natCard_isoSub_values.2.2.1] at h
  generalize Nat.card ↥(Xgrp ⊓ Kchain 3) = n at h ⊢
  omega

theorem Xgrp_inf_Kchain_one :
    Xgrp ⊓ Kchain 1 = H1 := by
  rw [Kchain_one, ← centralizer_xhat]
  exact Xgrp_inf_centralizer_xhat

theorem natCard_Kchain_values :
    Nat.card (Kchain 1) = 2 ^ 41 * 161382375 ∧
    Nat.card (Kchain 2) = 2 ^ 41 * 10395 ∧ Nat.card (Kchain 3) = 2 ^ 41 * 315 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Kchain_one, natCard_Jhat]
  · rw [Kchain_two, natCard_Ntwo]
    norm_num
  · show Nat.card K3 = _
    rw [natCard_K3]
    norm_num

theorem exists_sylow_X_inf_Kchain
    (i : ℕ) (h1 : 1 ≤ i) (h3 : i ≤ 3) :
    ∃ P : Sylow 2 (Kchain i), ∀ g ∈ (P : Subgroup (Kchain i)), (g : Dfull) ∈ Xgrp := by
  obtain ⟨k1, k2, k3⟩ := natCard_Kchain_values
  have hsub : ∀ {H : Subgroup Dfull}, (∃ P : Sylow 2 (Kchain i), ∀ g ∈ (P : Subgroup (Kchain i)),
      (g : Dfull) ∈ H) → H ≤ Xgrp →
      ∃ P : Sylow 2 (Kchain i), ∀ g ∈ (P : Subgroup (Kchain i)), (g : Dfull) ∈ Xgrp :=
    fun ⟨P, hP⟩ hH => ⟨P, fun g hg => hH (hP g hg)⟩
  refine hsub ?_ (inf_le_left : Xgrp ⊓ Kchain i ≤ Xgrp)
  interval_cases i
  · refine exists_sylow_le_of_card (inf_le_right : Xgrp ⊓ Kchain 1 ≤ Kchain 1) (a := 2835) ?_ k1
      (by norm_num)
    rw [Xgrp_inf_Kchain_one, natCard_H1]
    norm_num
  · exact exists_sylow_le_of_card inf_le_right natCard_X_inf_Kchain_two k2 (by norm_num)
  · refine exists_sylow_le_of_card inf_le_right (a := 63) ?_ k3 (by norm_num)
    rw [natCard_X_inf_Kchain_three]
    norm_num

end CFSG.Monster.B.TwoA.Sp8
