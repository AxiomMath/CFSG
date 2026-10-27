module

public import CFSG.Quasithin.Vol2.Ch12Sec6L12CentJ4Gen
public import CFSG.Sporadic.Schreier.J4SNoCompCover
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Gen

public section

namespace CFSG.Quasithin.H13.K1262Two

open CFSG.Open CFSG.Blueprint CFSG.Sporadic.J4

section Facts


theorem card_centralizer_η14 :
    Nat.card (Subgroup.centralizer ({CFSG.Sporadic.J4Schreier.η 14} : Set J)) = 1816657920 := by
  have h1 := CFSG.Sporadic.J4Schreier.card_H_inf_centralizer
    (CFSG.Sporadic.J4Schreier.η_mem_N 14)
    CFSG.Sporadic.J4Schreier.QT_unique_J4_local_normal_module_irreducible.2.2.2.2.1
  rw [inf_eq_right.mpr CFSG.Sporadic.J4Schreier.NoComp.centralizer_η14_le_H,
    CFSG.Sporadic.J4Schreier.card_H] at h1
  exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 276) (h1.trans (by norm_num))

theorem orderOf_z0_J4 : orderOf CFSG.Quasithin.J4Loc.z0 = 2 :=
  orderOf_eq_prime (by
    rw [sq]
    exact CFSG.Sporadic.J4.QT.eta_sq (CFSG.Sporadic.J4.QT.elem_uJ j4Facts.mat) 1131)
    (CFSG.Quasithin.J4M2.z0_ne_one j4Facts.mat)

theorem isConj_z0_of_dvd : CentJ4.J1Prop J CFSG.Quasithin.J4Loc.z0 := by
  intro x hx h
  have hC0 : Nat.card (Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J)) =
      21799895040 := by
    have := CFSG.Quasithin.J4M2.card_M2 j4Facts
    rw [this]
  obtain ⟨-, g, hg | hg⟩ :=
    CFSG.Sporadic.J4Schreier.CTU_J4_every_inner_involution_conjugate_into_local_binary_subgroup
      x hx
  · obtain ⟨-, g', hg' | hg'⟩ :=
      CFSG.Sporadic.J4Schreier.CTU_J4_every_inner_involution_conjugate_into_local_binary_subgroup
        _ orderOf_z0_J4
    · exact CentJ4.isConj_of_conj_eq hg hg'
    · exfalso
      have h1 := CentJ4.card_centralizer_conj g' CFSG.Quasithin.J4Loc.z0
      rw [hg', card_centralizer_η14, hC0] at h1
      norm_num at h1
  · exfalso
    have h1 := CentJ4.card_centralizer_conj g x
    rw [hg, card_centralizer_η14] at h1
    rw [← h1] at h
    norm_num at h

theorem noA6_le_centralizer_z0 :
    ∀ Y : Subgroup J, Y ≤ Subgroup.centralizer ({CFSG.Quasithin.J4Loc.z0} : Set J) →
      quasithinO2QuotientIso Y ↥(alternatingGroup (Fin 6)) → False := by
  intro Y hYM hY
  have hF := j4Facts
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card ↥CFSG.Quasithin.J4M2.M2 = 21799895040 := by
    rw [CFSG.Quasithin.J4M2.card_M2 hF]
  have h27 : ∀ T : Sylow 3 ↥CFSG.Quasithin.J4M2.M2, Nat.card T = 27 := fun T => by
    have := CentJ4.card_sylow_eq (k := 3) T (by rw [hcard]; norm_num) (by rw [hcard]; norm_num)
    rw [this]; norm_num
  have hYclM : CFSG.Sporadic.J4.QT2A.Ycl ≤ CFSG.Quasithin.J4M2.M2 :=
    CFSG.Sporadic.J4.QT2A.Ycl_le_Cz hF.mat
  have hT₁ : IsPGroup 3 ↥(CFSG.Sporadic.J4.QT2A.Ycl.subgroupOf CFSG.Quasithin.J4M2.M2) :=
    IsPGroup.of_card (n := 3) (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYclM).toEquiv,
        CFSG.Sporadic.J4.QT2A.card_Ycl hF.mat]
      norm_num)
  have haY := hYclM CFSG.Sporadic.J4.QT2A.aY_mem
  have hbY := hYclM CFSG.Sporadic.J4.QT2A.bY_mem
  have hcY : CFSG.Sporadic.J4.QT2A.cY ≠ 1 := by
    intro h1
    have := CFSG.Sporadic.J4.QT2A.yJ_inj hF.mat (n := 1) (m := 0) (by norm_num) (by norm_num)
      (by rw [CFSG.Sporadic.J4.QT2A.yJ_zero]; simp [CFSG.Sporadic.J4.QT2A.yJ, h1])
    omega
  have hab := CentJ4.mk_mul_ne haY hbY
    (CentJ4.mul_ne_of_commutator_ne_one (CFSG.Sporadic.J4.QT2A.cY_eq) hcY)
  have hKM : CFSG.Quasithin.J4M2.Kgrp ≤ CFSG.Quasithin.J4M2.M2 := by
    rw [CFSG.Quasithin.J4M2.Kgrp_eq_Kker hF, CFSG.Quasithin.J4M2.Kker]
    exact Subgroup.map_subtype_le _
  have hNk : CFSG.Quasithin.J4M2.Kgrp.subgroupOf CFSG.Quasithin.J4M2.M2 =
      (CFSG.Quasithin.J4M2.rho hF).ker := by
    ext m
    rw [Subgroup.mem_subgroupOf, CFSG.Quasithin.J4M2.mem_Kgrp_iff hF m, MonoidHom.mem_ker]
  have hN : (CFSG.Quasithin.J4M2.Kgrp.subgroupOf CFSG.Quasithin.J4M2.M2).Normal := by
    rw [hNk]; exact (CFSG.Quasithin.J4M2.rho hF).normal_ker
  have h5 : ¬ 5 ∣ Nat.card ↥(CFSG.Quasithin.J4M2.Kgrp.subgroupOf CFSG.Quasithin.J4M2.M2) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv,
      CFSG.Quasithin.J4M2.card_Kgrp hF]
    norm_num
  have hcK : CFSG.Quasithin.J4M2.cE ∈ CFSG.Quasithin.J4M2.Kgrp :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  have hcE := CFSG.Quasithin.J4M2.cE_mem_M2 hF.mat
  refine CentJ4.false_of_a6Type h27 hT₁ (a := ⟨_, haY⟩) (b := ⟨_, hbY⟩)
    (Subgroup.mem_subgroupOf.mpr CFSG.Sporadic.J4.QT2A.aY_mem)
    (Subgroup.mem_subgroupOf.mpr CFSG.Sporadic.J4.QT2A.bY_mem) hab (hN := hN) h5
    (n := ⟨_, hcE⟩) (Subgroup.mem_subgroupOf.mpr hcK)
    (by rw [Subgroup.orderOf_mk]; exact CFSG.Quasithin.J4M2.orderOf_cE hF.mat)
    (Y := Y.subgroupOf CFSG.Quasithin.J4M2.M2)
    (CentJ4.quasithinO2QuotientIso_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hYM).symm hY)

end Facts

theorem a6CentJ4_holds :
    A6CentJ4 := by
  intro X _ _ hX Y P u hY hP hPN
  obtain ⟨eX⟩ := hX
  have eJ : X ≃* J := eX.trans (seedEquiv j4Facts.mat)
  exact @CentJ4.card_lt_of_mulEquiv X J _ _ (Subgroup.toGroup J) eJ CFSG.Quasithin.J4Loc.z0
    isConj_z0_of_dvd noA6_le_centralizer_z0 Y P u hY hP hPN

end CFSG.Quasithin.H13.K1262Two

end
