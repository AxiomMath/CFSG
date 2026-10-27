module

public import CFSG.RankThree.GF2n.Stroth80.Sec108Phi

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement
open Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}

private theorem sup_root_Q_le_CN (D : Sec108Data hc t Y) : Y ⊔ Q ≤ hc.CN t := by
  refine sup_le (fun y hy => ?_) (Ctx.Q_le_CN hc D.good.1.mem_LB)
  refine Ctx.Rt_inf_le_CN hc D.sit (Good103.Vt_eq D.good D.sit) ⟨?_, ?_, ?_⟩
  · exact le_Rt (LB M Q B) D.good.1.mem_LB (D.root_le_LB hy)
  · exact IsZConjugate.le_QB_self hc.hyp D.sit.conj hy
  · exact ((smith_1_12 D.sit).1.trans inf_le_left) hy

private theorem phiMat_eq_zero_of_mem_root (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {y : G} (hy : y ∈ Y) :
    D.phiMat AM ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ = 0 := by
  have hV : ∀ e ∈ AM.Vsp hc t,
      AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ e = e :=
    fun e he => D.root_fix_range_nu AM hy (D.Vsp_le_range_nu AM he)
  have ht : ∀ e, AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩
        (AM.φ ⟨t, D.t_mem_H0⟩ e) =
      AM.φ ⟨t, D.t_mem_H0⟩ (AM.φ ⟨y, hc.LB_le_H0 (D.root_le_LB hy)⟩ e) := by
    intro e
    refine Sec108Data.phi_comm_of_comm_mem AM ?_ e
    rw [← commutatorElement_inv]
    exact Q.inv_mem (D.comm_Rt_root_mem t
      (le_Rt (LB M Q B) D.good.1.mem_LB D.good.1.mem_LB) y hy)
  exact (D.phiMat_eq_zero_iff AM hV ht).mpr fun u hu => D.root_fix_range_nu AM hy hu

private theorem phiMat_eq_zero_of_mem_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) {q : G} (hq : q ∈ Q) :
    D.phiMat AM ⟨q, hc.Q_le_H0 hq⟩ = 0 := by
  have hφ : AM.φ ⟨q, hc.Q_le_H0 hq⟩ = 1 := (AM.φ_ker _).mpr hq
  refine (D.phiMat_eq_zero_iff AM (m := ⟨q, hc.Q_le_H0 hq⟩) ?_ ?_).mpr fun u _ => ?_
  · intro e _
    rw [hφ]
    rfl
  · intro e
    rw [hφ]
    rfl
  · rw [hφ]
    rfl

private theorem sup_root_Q_le_ker (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    (Y ⊔ Q).subgroupOf (hc.CN t) ≤ (D.phiHom AM).ker := by
  rw [Subgroup.subgroupOf_sup
    (show Y ≤ hc.CN t from fun y hy => sup_root_Q_le_CN D (Subgroup.mem_sup_left hy))
    (Ctx.Q_le_CN hc D.good.1.mem_LB)]
  refine sup_le ?_ ?_
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hy : (x : G) ∈ Y := hx
    have h2 : (D.phiHom AM x).toAdd = 0 := by
      rw [D.phiHom_apply]
      exact phiMat_eq_zero_of_mem_root D AM hy
    exact toAdd_eq_zero.mp h2
  · intro x hx
    rw [MonoidHom.mem_ker]
    have hq : (x : G) ∈ Q := hx
    have h2 : (D.phiHom AM x).toAdd = 0 := by
      rw [D.phiHom_apply]
      exact phiMat_eq_zero_of_mem_Q D AM hq
    exact toAdd_eq_zero.mp h2

private theorem ker_inf_LB_eq_sup_root_Q (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    (D.phiHom AM).ker ⊓ (LB M Q B).subgroupOf (hc.CN t) =
      (Y ⊔ Q).subgroupOf (hc.CN t) := by
  refine le_antisymm ?_ ?_
  · intro x hx
    have hphi : D.phiMat AM ⟨x, D.CN_le_H0 x.2⟩ = 0 := by
      have h1 : D.phiHom AM x = 1 := MonoidHom.mem_ker.mp hx.1
      have h2 : (D.phiHom AM x).toAdd = 0 := by
        rw [h1]
        exact toAdd_one
      rwa [D.phiHom_apply] at h2
    have hLB : (x : G) ∈ LB M Q B := hx.2
    have hfix : ∀ u ∈ LinearMap.range (D.nu AM),
        AM.φ ⟨(x : G), hc.LB_le_H0 hLB⟩ u = u :=
      (D.phiMat_eq_zero_iff AM
        (fun e he => D.fix_Vsp_of_mem_CN AM (n := (x : G)) x.2 he)
        (fun e => D.comm_t_of_mem_CN AM (n := (x : G)) x.2 e)).mp hphi
    obtain ⟨y, hy, hyx⟩ := (D.fix_range_nu_iff AM ⟨(x : G), hLB⟩).mp hfix
    show (x : G) ∈ Y ⊔ Q
    have hxeq : (x : G) = y * (y⁻¹ * (x : G)) := by group
    rw [hxeq]
    exact Subgroup.mul_mem_sup hy hyx
  · intro x hx
    have hx' : (x : G) ∈ Y ⊔ Q := hx
    exact ⟨sup_root_Q_le_ker D AM hx, sup_le D.root_le_LB sec39_Q_le_LB hx'⟩

private theorem card_subgroupOf_LB (D : Sec108Data hc t Y) :
    Nat.card ((LB M Q B).subgroupOf (hc.CN t)) = Nat.card Z ^ 3 * Nat.card Q := by
  rw [← Subgroup.inf_subgroupOf_right (LB M Q B) (hc.CN t)]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (show LB M Q B ⊓ hc.CN t ≤ hc.CN t from inf_le_right)).toEquiv).trans D.card_LB_inf_CN

private theorem card_sup_root_Q (D : Sec108Data hc t Y) :
    Nat.card ↥(Y ⊔ Q) = Nat.card Z * Nat.card Q := by
  have hYcard : Nat.card Y = Nat.card Z := by
    obtain ⟨g, hg⟩ := D.sit.conj
    rw [hg, card_conjSubgroup]
  have hYN : Y ≤ Subgroup.normalizer (Q : Set G) :=
    ((smith_1_12 D.sit).1.trans inf_le_left).trans hc.hyp.Q_normal.2
  have hprod := card_sup_mul_card_inf_of_normalizer (A := Q) (C := Y) hYN
  have hbot : Q ⊓ Y = ⊥ := by
    rw [inf_comm]
    exact (smith_1_12 D.sit).2
  rw [hbot, hYcard, Subgroup.card_bot, mul_one] at hprod
  rw [sup_comm, hprod, Nat.mul_comm]

private theorem card_subgroupOf_sup_root_Q (D : Sec108Data hc t Y) :
    Nat.card ((Y ⊔ Q).subgroupOf (hc.CN t)) = Nat.card Z * Nat.card Q :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (sup_root_Q_le_CN D)).toEquiv).trans
    (card_sup_root_Q D)

theorem Sec108Data.card_range_phiHom_le (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Nat.card (D.phiHom AM).range ≤ Nat.card Z ^ 3 := by
  haveI := hc.normal_Q_in_M
  have hNcard : Nat.card ↥(hc.CN t) = Nat.card Z ^ 4 * Nat.card Q := by
    have h := bar_card_mul_card_of_le (M := M) (S := hc.CN t)
      (Ctx.Q_le_CN hc D.good.1.mem_LB)
      (fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1)
    rw [D.card_bar_CN] at h
    exact h.symm
  have hYQ := card_subgroupOf_sup_root_Q D
  have hle := sup_root_Q_le_ker D AM
  have hmul := Subgroup.card_ker_mul_card_range (D.phiHom AM)
  have hmain : Nat.card (D.phiHom AM).range *
        Nat.card ((Y ⊔ Q).subgroupOf (hc.CN t)) ≤
      Nat.card Z ^ 3 * Nat.card ((Y ⊔ Q).subgroupOf (hc.CN t)) := by
    calc Nat.card (D.phiHom AM).range * Nat.card ((Y ⊔ Q).subgroupOf (hc.CN t))
        = Nat.card ((Y ⊔ Q).subgroupOf (hc.CN t)) * Nat.card (D.phiHom AM).range :=
          Nat.mul_comm _ _
      _ ≤ Nat.card (D.phiHom AM).ker * Nat.card (D.phiHom AM).range :=
          Nat.mul_le_mul_right _ (Subgroup.card_le_of_le hle)
      _ = Nat.card ↥(hc.CN t) := hmul
      _ = Nat.card Z ^ 4 * Nat.card Q := hNcard
      _ = Nat.card Z ^ 3 * (Nat.card Z * Nat.card Q) := by ring
      _ = Nat.card Z ^ 3 * Nat.card ((Y ⊔ Q).subgroupOf (hc.CN t)) := by rw [hYQ]
  exact Nat.le_of_mul_le_mul_right hmain Nat.card_pos

theorem Sec108Data.card_map_phiHom_LB (D : Sec108Data hc t Y)
    (AM : Smith81.Smith23E1.ActionModel M Q Z) :
    Nat.card (((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)) = Nat.card Z ^ 2 := by
  have hker := ker_inf_LB_eq_sup_root_Q D AM
  have hK := card_subgroupOf_LB D
  have hYQ := card_subgroupOf_sup_root_Q D
  have hmul := Subgroup.relIndex_mul_card (H := (D.phiHom AM).ker)
    (K := (LB M Q B).subgroupOf (hc.CN t))
  rw [Subgroup.relIndex_ker (K := (LB M Q B).subgroupOf (hc.CN t)) (D.phiHom AM),
    hker, hYQ, hK] at hmul
  have hq : Nat.card (((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)) *
      Nat.card Z = Nat.card Z ^ 3 := by
    refine Nat.eq_of_mul_eq_mul_right (m := Nat.card Q) Nat.card_pos ?_
    rw [Nat.mul_assoc]
    exact hmul
  have hsq : Nat.card (((LB M Q B).subgroupOf (hc.CN t)).map (D.phiHom AM)) =
      Nat.card Z ^ 2 := by
    refine Nat.eq_of_mul_eq_mul_right (m := Nat.card Z) Nat.card_pos ?_
    rw [hq]
    ring
  exact hsq

end CFSG.RankThree.GF2n.Stroth80
