module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListM22

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
open CFSG.QuasithinUnique.Vol2Native.A312L.PermLat
open CFSG.QuasithinUnique.Unc25K1.Six
open Equiv

set_option maxRecDepth 200000 in
private lemma wt1 : cert.lat[1][0] = evalW cert.mGens
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] := by decide
set_option maxRecDepth 200000 in
private lemma wt2 : cert.lat[1][1] = evalW cert.mGens
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0] := by decide
set_option maxRecDepth 200000 in
private lemma wt3 : cert.lat[1][2] = evalW cert.mGens
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] := by decide
set_option maxRecDepth 200000 in
private lemma wx1 : cert.lat[1][3] = evalW cert.mGens
    [0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0] := by decide
set_option maxRecDepth 200000 in
private lemma wx2 : cert.lat[2][3] = evalW cert.mGens
    [0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0] := by decide
set_option maxRecDepth 200000 in
private lemma wt1' : cert.lat[2][0] = evalW cert.mGens
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] := by decide
set_option maxRecDepth 200000 in
private lemma wt2' : cert.lat[2][1] = evalW cert.mGens
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0] := by decide
set_option maxRecDepth 200000 in
private lemma wt3' : cert.lat[2][2] = evalW cert.mGens
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] := by decide
set_option maxRecDepth 200000 in
private lemma wt1t : cert.tGens[0] = evalW cert.mGens
    [1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1] := by decide
set_option maxRecDepth 200000 in
private lemma wt2t : cert.tGens[1] = evalW cert.mGens
    [0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0] := by decide
set_option maxRecDepth 200000 in
private lemma wt3t : cert.tGens[2] = evalW cert.mGens
    [1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1] := by decide
set_option maxRecDepth 200000 in
private lemma word0 : cert.lat[0][3] = evalW cert.lat[1] [0, 2, 1, 3, 0, 2, 3, 0, 3] := by decide
set_option maxRecDepth 200000 in
private lemma word5 : cert.lat[4][3] = evalW cert.lat[2] [1, 3, 1, 2, 1, 2, 3, 1, 2, 1, 3, 2] := by decide
set_option maxRecDepth 200000 in
private lemma wordj0 : cert.lat[3][0] = evalW (cert.lat[1] ++ cert.lat[2]) [0] := by decide
set_option maxRecDepth 200000 in
private lemma wordj1 : cert.lat[3][1] = evalW (cert.lat[1] ++ cert.lat[2]) [1] := by decide
set_option maxRecDepth 200000 in
private lemma wordj2 : cert.lat[3][2] = evalW (cert.lat[1] ++ cert.lat[2]) [2] := by decide
set_option maxRecDepth 200000 in
private lemma wordj3 : cert.lat[3][3] = evalW (cert.lat[1] ++ cert.lat[2]) [7, 3] := by decide

private lemma lat1_le_Mgrp : Subgroup.closure {g | g ∈ cert.lat[1]} ≤ Mgrp := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk4 : k < 4 := by rw [show cert.lat[1].length = 4 from rfl] at hk; exact hk
  interval_cases k
  · rw [wt1]; exact evalW_mem_closure _ _
  · rw [wt2]; exact evalW_mem_closure _ _
  · rw [wt3]; exact evalW_mem_closure _ _
  · rw [wx1]; exact evalW_mem_closure _ _

private lemma lat2_le_Mgrp : Subgroup.closure {g | g ∈ cert.lat[2]} ≤ Mgrp := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk4 : k < 4 := by rw [show cert.lat[2].length = 4 from rfl] at hk; exact hk
  interval_cases k
  · rw [wt1']; exact evalW_mem_closure _ _
  · rw [wt2']; exact evalW_mem_closure _ _
  · rw [wt3']; exact evalW_mem_closure _ _
  · rw [wx2]; exact evalW_mem_closure _ _

private lemma tGens_le_Mgrp : Subgroup.closure {g | g ∈ cert.tGens} ≤ Mgrp := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk3 : k < 3 := by rw [show cert.tGens.length = 3 from rfl] at hk; exact hk
  interval_cases k
  · rw [wt1t]; exact evalW_mem_closure _ _
  · rw [wt2t]; exact evalW_mem_closure _ _
  · rw [wt3t]; exact evalW_mem_closure _ _

private lemma tGens_le_lat1 : Subgroup.closure {g | g ∈ cert.tGens} ≤
    Subgroup.closure {g | g ∈ cert.lat[1]} := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk3 : k < 3 := by rw [show cert.tGens.length = 3 from rfl] at hk; exact hk
  interval_cases k <;> exact Subgroup.subset_closure (by simp [cert, tGens, lat])

private lemma tGens_le_lat2 : Subgroup.closure {g | g ∈ cert.tGens} ≤
    Subgroup.closure {g | g ∈ cert.lat[2]} := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk3 : k < 3 := by rw [show cert.tGens.length = 3 from rfl] at hk; exact hk
  interval_cases k <;> exact Subgroup.subset_closure (by simp [cert, tGens, lat])

private lemma closure_append_eq_sup {G : Type*} [Group G] (A B : List G) :
    Subgroup.closure {g | g ∈ A ++ B} =
      Subgroup.closure {g | g ∈ A} ⊔ Subgroup.closure {g | g ∈ B} := by
  rw [show {g : G | g ∈ A ++ B} = {g | g ∈ A} ∪ {g | g ∈ B} by ext g; simp,
    Subgroup.closure_union]

private lemma lat0_le_lat1 : Subgroup.closure {g | g ∈ cert.lat[0]} ≤
    Subgroup.closure {g | g ∈ cert.lat[1]} := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk4 : k < 4 := by rw [show cert.lat[0].length = 4 from rfl] at hk; exact hk
  interval_cases k
  · exact Subgroup.subset_closure (by simp [cert, lat])
  · exact Subgroup.subset_closure (by simp [cert, lat])
  · exact Subgroup.subset_closure (by simp [cert, lat])
  · rw [word0]; exact evalW_mem_closure _ _

private lemma lat4_le_lat2 : Subgroup.closure {g | g ∈ cert.lat[4]} ≤
    Subgroup.closure {g | g ∈ cert.lat[2]} := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk4 : k < 4 := by rw [show cert.lat[4].length = 4 from rfl] at hk; exact hk
  interval_cases k
  · exact Subgroup.subset_closure (by simp [cert, lat])
  · exact Subgroup.subset_closure (by simp [cert, lat])
  · exact Subgroup.subset_closure (by simp [cert, lat])
  · rw [word5]; exact evalW_mem_closure _ _

private lemma lat3_le_sup : Subgroup.closure {g | g ∈ cert.lat[3]} ≤
    Subgroup.closure {g | g ∈ cert.lat[1]} ⊔ Subgroup.closure {g | g ∈ cert.lat[2]} := by
  rw [Subgroup.closure_le]
  intro g hg
  simp only [Set.mem_ofPred_eq] at hg
  rw [List.mem_iff_getElem] at hg
  obtain ⟨k, hk, rfl⟩ := hg
  have hk4 : k < 4 := by rw [show cert.lat[3].length = 4 from rfl] at hk; exact hk
  have hU := closure_append_eq_sup (G := Perm (Fin 22)) cert.lat[1] cert.lat[2]
  interval_cases k
  · rw [wordj0]; exact hU ▸ evalW_mem_closure _ _
  · rw [wordj1]; exact hU ▸ evalW_mem_closure _ _
  · rw [wordj2]; exact hU ▸ evalW_mem_closure _ _
  · rw [wordj3]; exact hU ▸ evalW_mem_closure _ _

private lemma le_of_subgroupOf_le {G : Type*} [Group G] {M H K : Subgroup G}
    (hH : H ≤ M) (hK : K ≤ M) (h : H.subgroupOf M ≤ K.subgroupOf M) : H ≤ K := by
  have h' := Subgroup.map_mono (f := M.subtype) h
  rwa [Subgroup.map_subgroupOf_eq_of_le hH, Subgroup.map_subgroupOf_eq_of_le hK] at h'

private lemma cons_lat_0 : (cert.tGens :: cert.lat)[0] = cert.tGens := by simp
private lemma cons_lat_1 : (cert.tGens :: cert.lat)[1] = cert.lat[0] := by simp
private lemma cons_lat_2 : (cert.tGens :: cert.lat)[2] = cert.lat[1] := by simp
private lemma cons_lat_3 : (cert.tGens :: cert.lat)[3] = cert.lat[2] := by simp
private lemma cons_lat_4 : (cert.tGens :: cert.lat)[4] = cert.lat[3] := by simp
private lemma cons_lat_5 : (cert.tGens :: cert.lat)[5] = cert.lat[4] := by simp

private lemma sizes_getD_eq_1920 {j : ℕ} (hj : j < 6)
    (h : cert.sizes.getD j 0 = 1920) : j = 2 := by
  rw [show cert.sizes = [128, 384, 1920, 5760, 443520, 384] from rfl] at h
  interval_cases j <;> simp_all

private lemma sizes_getD_eq_5760 {j : ℕ} (hj : j < 6)
    (h : cert.sizes.getD j 0 = 5760) : j = 3 := by
  rw [show cert.sizes = [128, 384, 1920, 5760, 443520, 384] from rfl] at h
  interval_cases j <;> simp_all

theorem card_Ugrp : Nat.card Ugrp = 128 := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  change Nat.card ((Subgroup.closure {g | g ∈ cert.tGens}).subgroupOf Mgrp) = 128
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe tGens_le_Mgrp).toEquiv,
    cert.card_t (rawIsEnc 22) hcl hsz]
  rfl

theorem mgrp_overgroups :
    ∃ A B : Subgroup ↥Mgrp, Ugrp ≤ A ∧ Ugrp ≤ B ∧ Nat.card A = 1920 ∧ Nat.card B = 5760 ∧
      (∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y → Y = ⊤ ∨ Y ≤ A ∨ Y ≤ B) ∧ ¬ A ≤ B ∧
      (∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y → Nat.card Y = 1920 → Y = A) ∧
      (∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y → Nat.card Y = 5760 → Y = B) := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  have hsz := LatCert.sizesOK_of_check hck
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  have hMcard : Nat.card ↥Mgrp = 443520 := cert.card_m (rawIsEnc 22) hcl hsz
  have hcard_lat0 : Nat.card (Subgroup.closure {g | g ∈ cert.lat[0]}) = 384 := by
    rw [← cons_lat_1,
      cert.card_member_idx (rawIsEnc 22) hcl hsz 1 (by rw [hlen]; norm_num)]; rfl
  have hcard_lat1 : Nat.card (Subgroup.closure {g | g ∈ cert.lat[1]}) = 1920 := by
    rw [← cons_lat_2,
      cert.card_member_idx (rawIsEnc 22) hcl hsz 2 (by rw [hlen]; norm_num)]; rfl
  have hcard_lat2 : Nat.card (Subgroup.closure {g | g ∈ cert.lat[2]}) = 5760 := by
    rw [← cons_lat_3,
      cert.card_member_idx (rawIsEnc 22) hcl hsz 3 (by rw [hlen]; norm_num)]; rfl
  have hcard_lat3 : Nat.card (Subgroup.closure {g | g ∈ cert.lat[3]}) = 443520 := by
    rw [← cons_lat_4,
      cert.card_member_idx (rawIsEnc 22) hcl hsz 4 (by rw [hlen]; norm_num)]; rfl
  have hcard_lat4 : Nat.card (Subgroup.closure {g | g ∈ cert.lat[4]}) = 384 := by
    rw [← cons_lat_5,
      cert.card_member_idx (rawIsEnc 22) hcl hsz 5 (by rw [hlen]; norm_num)]; rfl
  let A : Subgroup ↥Mgrp := (Subgroup.closure {g | g ∈ cert.lat[1]}).subgroupOf Mgrp
  let B : Subgroup ↥Mgrp := (Subgroup.closure {g | g ∈ cert.lat[2]}).subgroupOf Mgrp
  have hAcard : Nat.card A = 1920 := by
    change Nat.card ((Subgroup.closure {g | g ∈ cert.lat[1]}).subgroupOf Mgrp) = 1920
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe lat1_le_Mgrp).toEquiv, hcard_lat1]
  have hBcard : Nat.card B = 5760 := by
    change Nat.card ((Subgroup.closure {g | g ∈ cert.lat[2]}).subgroupOf Mgrp) = 5760
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe lat2_le_Mgrp).toEquiv, hcard_lat2]
  have hTrust : Ugrp = (Subgroup.closure {g | g ∈ cert.tGens}).subgroupOf Mgrp := rfl
  have hUA : Ugrp ≤ A := by
    rw [hTrust]
    intro x hx; rw [Subgroup.mem_subgroupOf] at hx ⊢; exact tGens_le_lat1 hx
  have hUB : Ugrp ≤ B := by
    rw [hTrust]
    intro x hx; rw [Subgroup.mem_subgroupOf] at hx ⊢; exact tGens_le_lat2 hx
  have hclass : ∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y →
      ∃ j, ∃ _hj : j < (cert.tGens :: cert.lat).length,
        Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[j]} ≤ Mgrp ∧
        Y = (Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[j]}).subgroupOf Mgrp ∧
        Nat.card Y = cert.sizes.getD j 0 := by
    intro Y hY
    obtain ⟨j, hj, hLM, hYeq, hcardj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) hck Y hY
    have hYcard : Nat.card Y = cert.sizes.getD j 0 := by
      rw [hYeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj]
    exact ⟨j, hj, hLM, hYeq, hYcard⟩
  have hunion : ∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y → Y = ⊤ ∨ Y ≤ A ∨ Y ≤ B := by
    intro Y hY
    obtain ⟨j, hj, hLM, hYeq, hYcard⟩ := hclass Y hY
    have hj6 : j < 6 := by rwa [hlen] at hj
    interval_cases j
    · refine Or.inr (Or.inl ?_)
      rw [hYeq, cons_lat_0]; exact hUA
    · refine Or.inr (Or.inl ?_)
      rw [hYeq, cons_lat_1]
      exact fun x hx => by rw [Subgroup.mem_subgroupOf] at hx ⊢; exact lat0_le_lat1 hx
    · refine Or.inr (Or.inl ?_)
      rw [hYeq, cons_lat_2]
    · refine Or.inr (Or.inr ?_)
      rw [hYeq, cons_lat_3]
    · refine Or.inl ?_
      apply Subgroup.eq_top_of_card_eq
      rw [hYeq, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv,
        cert.card_member_idx (rawIsEnc 22) hcl hsz 4 (by rw [hlen]; norm_num),
        show cert.sizes.getD 4 0 = 443520 from rfl, hMcard]
    · refine Or.inr (Or.inr ?_)
      rw [hYeq, cons_lat_5]
      exact fun x hx => by rw [Subgroup.mem_subgroupOf] at hx ⊢; exact lat4_le_lat2 hx
  have hnotAB : ¬ A ≤ B := by
    intro h
    have hL1L2 : Subgroup.closure {g | g ∈ cert.lat[1]} ≤ Subgroup.closure {g | g ∈ cert.lat[2]} :=
      le_of_subgroupOf_le lat1_le_Mgrp lat2_le_Mgrp h
    have hL3L2 : Subgroup.closure {g | g ∈ cert.lat[3]} ≤ Subgroup.closure {g | g ∈ cert.lat[2]} :=
      lat3_le_sup.trans (sup_le hL1L2 le_rfl)
    have := Nat.card_le_card_of_injective (Subgroup.inclusion hL3L2)
      (Subgroup.inclusion_injective hL3L2)
    rw [hcard_lat3, hcard_lat2] at this; omega
  have huniq1920 : ∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y → Nat.card Y = 1920 → Y = A := by
    intro Y hY hYc
    obtain ⟨j, hj, -, hYeq, hYcard⟩ := hclass Y hY
    have hj6 : j < 6 := by rwa [hlen] at hj
    have hj2 : j = 2 := sizes_getD_eq_1920 hj6 (by rw [← hYcard]; exact hYc)
    subst hj2
    rw [hYeq, cons_lat_2]
  have huniq5760 : ∀ Y : Subgroup ↥Mgrp, Ugrp ≤ Y → Nat.card Y = 5760 → Y = B := by
    intro Y hY hYc
    obtain ⟨j, hj, -, hYeq, hYcard⟩ := hclass Y hY
    have hj6 : j < 6 := by rwa [hlen] at hj
    have hj3 : j = 3 := sizes_getD_eq_5760 hj6 (by rw [← hYcard]; exact hYc)
    subst hj3
    rw [hYeq, cons_lat_3]
  exact ⟨A, B, hUA, hUB, hAcard, hBcard, hunion, hnotAB, huniq1920, huniq5760⟩

end CFSG.Quasithin.AppendixH.H12
