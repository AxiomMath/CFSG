module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Perf

public section

namespace CFSG.Quasithin.J4M2

open scoped commutatorElement

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.QT CFSG.Sporadic.J4.QT2A
  CFSG.Quasithin.J4Loc CFSG.Quasithin

theorem Kgrp_le_M2
    (hF : J4Facts) : Kgrp ≤ M2 :=
  (Kgrp_le_Kker hF).trans (by rintro _ ⟨y, -, rfl⟩; exact y.2)

theorem Qgrp_le_Kgrp : Qgrp ≤ Kgrp := le_sup_left

theorem Kgrp_normalizes_Qgrp
    (hF : J4Facts) :
    ∀ k ∈ Kgrp, ∀ x ∈ Qgrp, k * x * k⁻¹ ∈ Qgrp :=
  normalizes_of_mem_sup_zpowers Qgrp cE (cE_normalizes_Qgrp hF.mat)

theorem Kgrp_conj_mem
    (hF : J4Facts) : ∀ m ∈ M2, ∀ k ∈ Kgrp, m * k * m⁻¹ ∈ Kgrp := by
  intro m hm k hk
  have hkM : k ∈ M2 := Kgrp_le_M2 hF hk
  have hk1 : rho hF ⟨k, hkM⟩ = 1 := (mem_Kgrp_iff hF ⟨k, hkM⟩).1 hk
  refine (mem_Kgrp_iff hF ⟨m * k * m⁻¹, M2.mul_mem (M2.mul_mem hm hkM) (M2.inv_mem hm)⟩).2 ?_
  have e : (⟨m * k * m⁻¹, M2.mul_mem (M2.mul_mem hm hkM) (M2.inv_mem hm)⟩ : ↥M2) =
      ⟨m, hm⟩ * ⟨k, hkM⟩ * ⟨m, hm⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, hk1, mul_one, map_inv, mul_inv_cancel]

theorem Qgrp_conj_mem
    (hF : J4Facts) : ∀ m ∈ M2, ∀ x ∈ Qgrp, m * x * m⁻¹ ∈ Qgrp :=
  conj_mem_of_normal_two_sylow M2 Kgrp Qgrp (Kgrp_conj_mem hF) le_sup_left
    (Kgrp_normalizes_Qgrp hF) (card_Kgrp hF) (card_Qgrp hF.mat)

theorem isSolvable_Kgrp
    (hF : J4Facts) : Group.IsSolvable ↥Kgrp :=
  isSolvable_of_normal_two_group Kgrp Qgrp le_sup_left (Kgrp_normalizes_Qgrp hF) (card_Kgrp hF)
    (card_Qgrp hF.mat)

theorem P0_le_M2
    (hF : J4Facts) : P0 ≤ M2 :=
  P0_le_Dgrp.trans (Dgrp_le_M2 hF.mat)

theorem card_M2_two_part
    (hF : J4Facts) :
    Nat.card ↥M2 = 2 ^ 21 * 10395 := by
  rw [card_M2 hF]
  norm_num

theorem Qgrp_le_P0
    (hF : J4Facts) : Qgrp ≤ P0 :=
  le_of_normal_two_group M2 Qgrp P0 (P0_le_M2 hF) (card_P0 hF.mat hF) (m := 10395)
    (card_M2_two_part hF) (by norm_num) (Qgrp_le_M2 hF.mat) (Qgrp_conj_mem hF)
    (isPGroup_Qgrp hF.mat)

theorem B0grp_le_M2
    (hF : J4Facts) : B0grp ≤ M2 := by
  rw [B0grp, Subgroup.closure_le]
  rintro _ ⟨n, hn, rfl⟩
  exact gE_mem_M2 hF.mat (by omega)

theorem Kgrp_le_B0grp : Kgrp ≤ B0grp :=
  sup_le Qgrp_le_B0 (Subgroup.zpowers_le.2 cE_mem_B0)

theorem sigPerm_mem_MbarP {k : ℕ} (hk : k < 5) : sigPerm (12 + k) ∈ MbarP := by
  refine Subgroup.subset_closure ?_
  show sigPerm (12 + k) ∈ oddPerms
  simp only [oddPerms, List.mem_cons, List.not_mem_nil, or_false]
  interval_cases k
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))

theorem map_B0grp_eq
    (hF : J4Facts) :
    (B0grp.subgroupOf M2).map (rho hF) = MbarP := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    have hS : B0grp ≤ (MbarP.comap (rho hF)).map M2.subtype := by
      rw [B0grp, Subgroup.closure_le]
      rintro _ ⟨n, hn, rfl⟩
      refine ⟨⟨gE n, gE_mem_M2 hF.mat (by omega)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, rho_gE_perm hF (by omega)]
      by_cases h : n < 12
      · rw [sigPerm_q h]
        exact MbarP.one_mem
      · have h12 : n = 12 + (n - 12) := by omega
        rw [h12]
        exact sigPerm_mem_MbarP (by omega)
    intro m hm
    obtain ⟨y, hy, hym⟩ := hS (Subgroup.mem_subgroupOf.1 hm)
    have : y = m := Subtype.ext hym
    rw [← this]
    exact hy
  · rw [MbarP, Subgroup.closure_le]
    intro x hx
    simp only [oddPerms, List.mem_cons, List.not_mem_nil, or_false, Set.mem_ofPred_eq] at hx
    have key : ∀ n, 12 ≤ n → n < 17 → x = sigPerm n →
        x ∈ (B0grp.subgroupOf M2).map (rho hF) := fun n h1 h2 h => by
      refine ⟨⟨gE n, gE_mem_M2 hF.mat (by omega)⟩, Subgroup.mem_subgroupOf.2 ?_, ?_⟩
      · exact gE_mem_B0 h2
      · rw [rho_gE_perm hF (by omega)]
        exact h.symm
    rcases hx with h | h | h | h | h
    · exact key 12 (by norm_num) (by norm_num) h
    · exact key 13 (by norm_num) (by norm_num) h
    · exact key 14 (by norm_num) (by norm_num) h
    · exact key 15 (by norm_num) (by norm_num) h
    · exact key 16 (by norm_num) (by norm_num) h

theorem commutator_MbarP :
    ⁅MbarP, MbarP⁆ = MbarP := by
  have hs := isSimpleGroup_MbarP
  obtain ⟨a, b, hab⟩ := MbarP_nonabelian
  have htop : commutator ↥MbarP = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator ↥MbarP) with h | h
    · exfalso
      apply hab
      have hmem : ⁅a, b⁆ ∈ commutator ↥MbarP := by
        rw [commutator_def]
        exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
      exact hmem
    · exact h
  have h2 : (commutator ↥MbarP).map MbarP.subtype = ⁅MbarP, MbarP⁆ := by
    rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
  exact h2.symm

theorem B0grp_perfect
    (hF : J4Facts) : ⁅B0grp, B0grp⁆ = B0grp :=
  commutator_eq_of_ker_le M2 B0grp Kgrp (rho hF) (B0grp_le_M2 hF) (rho_eq_one_iff hF)
    (sup_le (Qgrp_le_commutator_B0 hF.mat) (Subgroup.zpowers_le.2 cE_mem_commutator_B0))
    (by rw [map_B0grp_eq hF]; exact commutator_MbarP)

theorem shape_of_mem_cComp_M2
    (hF : J4Facts) : ∀ B ∈ cComp M2, J4Fam.J4Shape ↥B := by
  intro B hB
  have hS' : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  let e : ↥MbarP ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22 := phiEquiv.symm
  have hnab : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M22, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := MbarP_nonabelian
    refine ⟨e a, e b, fun h => hab ?_⟩
    have h' : e (a * b) = e (b * a) := by rw [map_mul, map_mul]; exact h
    exact e.injective h'
  have hAle : MbarP ≤ (rho hF).range := by
    rw [range_rho_eq hF]
    exact MbarP_le_Mbar
  have hidx : Nat.card (rho hF).range = 2 * Nat.card ↥MbarP := by
    rw [(card_range_ker_rho hF).1, card_MbarP]
  exact (j4Shape_of_mem_cComp M2 (rho hF) MbarP e hS' hnab hAle hidx Kgrp Qgrp B0grp
    (Kgrp_le_M2 hF) (rho_eq_one_iff hF) (isSolvable_Kgrp hF) (card_Kgrp hF) le_sup_left
    (card_Qgrp hF.mat) (isExtraspecial_Qgrp hF.mat) (Qgrp_conj_mem hF) (B0grp_le_M2 hF)
    Kgrp_le_B0grp
    (mem_iff_of_map_eq M2 B0grp Kgrp (rho hF) MbarP (rho_eq_one_iff hF) Kgrp_le_B0grp
      (map_B0grp_eq hF))
    (B0grp_perfect hF) B hB).2

end CFSG.Quasithin.J4M2
