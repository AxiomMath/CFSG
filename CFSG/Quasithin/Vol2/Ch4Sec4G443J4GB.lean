module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Str

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4.JM

open CFSG.Open CFSG.Quasithin CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.J4M2
  CFSG.Quasithin.J4Loc


noncomputable def psiB0 (hF : J4Facts) : ↥B0grp →* ↥MbarP :=
  ((rho hF).comp (Subgroup.inclusion (B0grp_le_M2 hF))).codRestrict MbarP fun b =>
    (mem_iff_of_map_eq M2 B0grp Kgrp (rho hF) MbarP (rho_eq_one_iff hF) Kgrp_le_B0grp
      (map_B0grp_eq hF) ⟨b, B0grp_le_M2 hF b.2⟩).1 b.2

theorem psiB0_surjective (hF : J4Facts) : Function.Surjective (psiB0 hF) := by
  intro a
  have ha : (a : Equiv.Perm (Fin 77)) ∈ (B0grp.subgroupOf M2).map (rho hF) := by
    rw [map_B0grp_eq hF]
    exact a.2
  obtain ⟨m, hm, hma⟩ := ha
  exact ⟨⟨(m : J), hm⟩, Subtype.ext hma⟩

theorem psiB0_eq_one_iff (hF : J4Facts) (b : ↥B0grp) : psiB0 hF b = 1 ↔ (b : J) ∈ Kgrp :=
  Iff.trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    (rho_eq_one_iff hF ⟨b, B0grp_le_M2 hF b.2⟩)

theorem card_ker_psiB0 (hF : J4Facts) : Nat.card ↥(psiB0 hF).ker = 3 * 2 ^ 13 := by
  rw [← card_Kgrp hF]
  exact Nat.card_congr ((Equiv.subtypeEquiv (Equiv.refl _) fun b =>
    MonoidHom.mem_ker.trans ((psiB0_eq_one_iff hF b).trans Subgroup.mem_subgroupOf.symm)).trans
    (Subgroup.subgroupOfEquivOfLe Kgrp_le_B0grp).toEquiv)

theorem card_B0grp (hF : J4Facts) : Nat.card ↥B0grp = 443520 * 24576 := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (psiB0 hF).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ (psiB0_surjective hF)).toEquiv,
    card_MbarP, card_ker_psiB0 hF] at h1
  rw [h1]
  norm_num

theorem perfectCore_M2 (hF : J4Facts) : perfectCore M2 = B0grp := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have hcard : Nat.card ↥M2 = 2 * Nat.card ↥B0grp := by
    rw [card_M2 hF, card_B0grp hF]
  refine le_antisymm ?_ (le_perfectCore_of_perfect (B0grp_le_M2 hF) (B0grp_perfect hF))
  refine (perfectCore_le_derivedSeriesOf M2 1).trans ?_
  show ⁅M2, M2⁆ ≤ B0grp
  exact Subgroup.commutator_le.mpr (commutatorElement_mem_of_card_eq_two_mul (B0grp_le_M2 hF) hcard)

theorem normal_Qgrp (hF : J4Facts) : (Qgrp.subgroupOf B0grp).Normal := ⟨fun x hx b => by
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact Qgrp_conj_mem hF b (B0grp_le_M2 hF b.2) x hx⟩

theorem isHat_quot_Qgrp (hF : J4Facts) [(Qgrp.subgroupOf B0grp).Normal] :
    IsHat (↥B0grp ⧸ Qgrp.subgroupOf B0grp) (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have hS' : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
    (CFSG.Sporadic.Mathieu.fam_m22_simplicity).2.2
  let e : ↥MbarP ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22 := phiEquiv.symm
  have hnab : ∃ a b : CFSG.Blueprint.NativeSporadic.Carrier .M22, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := MbarP_nonabelian
    refine ⟨e a, e b, fun h => hab ?_⟩
    have h' : e (a * b) = e (b * a) := by rw [map_mul, map_mul]; exact h
    exact e.injective h'
  have hVψ : Qgrp.subgroupOf B0grp ≤ (psiB0 hF).ker := fun b hb => by
    rw [MonoidHom.mem_ker, psiB0_eq_one_iff hF]
    exact Qgrp_le_Kgrp (Subgroup.mem_subgroupOf.mp hb)
  have hcard : Nat.card ↥(psiB0 hF).ker = 3 * Nat.card ↥(Qgrp.subgroupOf B0grp) := by
    rw [card_ker_psiB0 hF, Nat.card_congr (Subgroup.subgroupOfEquivOfLe Qgrp_le_B0).toEquiv,
      card_Qgrp hF.mat]
  exact isHat_quotient_of_surjective (psiB0 hF) (psiB0_surjective hF) (Qgrp.subgroupOf B0grp) hVψ
    (commutator_eq_top_of_commutator_eq_self (B0grp_perfect hF)) hcard e hS' hnab

theorem pCore_B0grp (hF : J4Facts) : CFSG.pCore 2 ↥B0grp = Qgrp.subgroupOf B0grp := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite J := Nat.finite_of_card_ne_zero (by rw [card_J hF]; norm_num)
  have hQn := normal_Qgrp hF
  have hhat := isHat_quot_Qgrp hF
  have hQ2 : IsPGroup 2 ↥(Qgrp.subgroupOf B0grp) := IsPGroup.of_card (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Qgrp_le_B0).toEquiv, card_Qgrp hF.mat])
  refine le_antisymm ?_ (J4Fam.le_pCore_two hQ2)
  have hbot := J4Fam.pCore_eq_bot_of_isHat hhat.1 hhat.2.1
  intro x hx
  have hmap : (CFSG.pCore 2 ↥B0grp).map (QuotientGroup.mk' (Qgrp.subgroupOf B0grp)) ≤
      CFSG.pCore 2 (↥B0grp ⧸ Qgrp.subgroupOf B0grp) := by
    have : ((CFSG.pCore 2 ↥B0grp).map (QuotientGroup.mk' (Qgrp.subgroupOf B0grp))).Normal :=
      Subgroup.Normal.map CFSG.pCore_normal _ (QuotientGroup.mk'_surjective _)
    exact J4Fam.le_pCore_two ((CFSG.pCore_isPGroup (p := 2) (G := ↥B0grp)).map _)
  rw [hbot] at hmap
  have h1 := hmap (Subgroup.mem_map_of_mem _ hx)
  rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem isHat_B0grp (hF : J4Facts) :
    IsHat (↥B0grp ⧸ CFSG.pCore 2 ↥B0grp) (CFSG.Blueprint.NativeSporadic.Carrier .M22) := by
  have := normal_Qgrp hF
  exact IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq (pCore_B0grp hF)).symm
    (isHat_quot_Qgrp hF)

theorem not_dvd_card_M2 (hF : J4Facts) : ¬ 23 ∣ Nat.card ↥M2 := by
  rw [card_M2 hF]
  norm_num

theorem not_B0grp_le_Hj (hF : J4Facts) : ¬ B0grp ≤ Hj := by
  intro h
  have hle : B0grp ≤ Subgroup.centralizer ({z0} : Set J) ⊓ Hj := le_inf (B0grp_le_M2 hF) h
  have hc : Nat.card ↥(Subgroup.centralizer ({z0} : Set J) ⊓ Hj) = 283115520 :=
    J4Rad.card_inf_Hj_of_mem_Zl hF CFSG.Sporadic.J4.QT2.z0_mem_Zl
  have h1 := Subgroup.card_dvd_of_le hle
  rw [card_B0grp hF, hc] at h1
  norm_num at h1

theorem sup_B0grp_eq_top (hF : J4Facts) : Hj ⊔ B0grp = ⊤ :=
  (isCoatom_Hj hF).2 _ (lt_of_le_of_ne le_sup_left fun h =>
    not_B0grp_le_Hj hF (h ▸ le_sup_right))

end CFSG.Quasithin.H13.Ch4.G443J4.JM
