
module

public import CFSG.Monster.B.TwoA.Amalgam.CosetStepBase

public import CFSG.Monster.B.TwoA.Amalgam.Kernels
public import CFSG.Monster.B.TwoA.Base.ResGenBase
public import CFSG.Monster.B.TwoA.Sp8.Orth8

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Sp8
open scoped Pointwise

theorem Eam_inf_conj
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    Eam ⊓ Eam.map (MulAut.conj a⁻¹).toMonoidHom = P1 := by
  apply le_antisymm
  · rintro y ⟨hyE, hya'⟩
    have hya := mem_conj_iff.1 hya'
    have hy1 : y * cQ = cQ * y := Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer hyE)
    have hy2 : a * y * a⁻¹ * cQ = cQ * (a * y * a⁻¹) :=
      Subgroup.mem_centralizer_singleton_iff.1 (Eam_le_centralizer hya)
    have hy3 : y * (cQ * xhat) = cQ * xhat * y := by
      rw [← conj_cQ_of_not_mem ha hn]
      calc y * (a⁻¹ * cQ * a) = a⁻¹ * (a * y * a⁻¹ * cQ) * a := by group
        _ = a⁻¹ * (cQ * (a * y * a⁻¹)) * a := by rw [hy2]
        _ = a⁻¹ * cQ * a * y := by group
    have hyx : y * xhat = xhat * y := by
      have : cQ * (y * xhat) = cQ * (xhat * y) := by
        rw [← mul_assoc, ← hy1, mul_assoc, hy3, mul_assoc]
      exact mul_left_cancel this
    refine ⟨?_, Eam_le_centralizer hyE⟩
    rw [← centralizer_xhat]
    exact Subgroup.mem_centralizer_singleton_iff.2 hyx
  · intro p hp
    refine ⟨Pc_le_Eam 0 hp, ?_⟩
    rw [← map_conj_P1 ha hn] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    exact ⟨q, Pc_le_Eam 0 hq, rfl⟩

theorem Ehat_not_mem_P4
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) : a ∉ P4 :=
  fun h => hn ⟨ha, h.2⟩

theorem exists_mem_Ehat_not_mem_N1 :
    ∃ a ∈ Ehat, a ∉ N1 := by
  by_contra h
  have hle := Subgroup.card_le_of_le (show Ehat ≤ N1 from fun a ha => by
    by_contra hn
    exact h ⟨a, ha, hn⟩)
  rw [natCard_Ehat, natCard_N1] at hle
  norm_num at hle

theorem closure_P4_eq
    {a : Dfull} (haX : a ∈ Xgrp) (haP : a ∉ P4) :
    Subgroup.closure (insert a (P4 : Set Dfull)) = Xgrp := by
  set H := Subgroup.closure (insert a (P4 : Set Dfull))
  have hP : P4 ≤ H := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have haH : a ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact haX
    · exact P4_le_Xgrp hx
  · intro x hx
    have hc : cQ ∈ cOrbit := ⟨1, Xgrp.one_mem, by rw [one_mul, inv_one, mul_one]⟩
    have hz : a * cQ * a⁻¹ ∈ cOrbit := ⟨a, haX, rfl⟩
    have hy : x * cQ * x⁻¹ ∈ cOrbit := ⟨x, hx, rfl⟩
    have hza : a * cQ * a⁻¹ ≠ cQ := fun h => haP ⟨haX,
      Subgroup.mem_centralizer_singleton_iff.2 (by
        calc a * cQ = a * cQ * a⁻¹ * a := by group
          _ = cQ * a := by rw [h])⟩
    by_cases hxy : x * cQ * x⁻¹ = cQ
    · exact hP ⟨hx, Subgroup.mem_centralizer_singleton_iff.2 (by
        calc x * cQ = x * cQ * x⁻¹ * x := by group
          _ = cQ * x := by rw [hxy])⟩
    · obtain ⟨g, hg, hg1, hg2⟩ := cOrbit_two_transitive hc hz hc hy (Ne.symm hza) (Ne.symm hxy)
      have hgP : g ∈ P4 := ⟨hg, Subgroup.mem_centralizer_singleton_iff.2 (by
        calc g * cQ = g * cQ * g⁻¹ * g := by group
          _ = cQ * g := by rw [hg1])⟩
      have hk : (g * a)⁻¹ * x ∈ P4 := by
        refine ⟨Xgrp.mul_mem (Xgrp.inv_mem (Xgrp.mul_mem hg haX)) hx,
          Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
        have e : (g * a) * cQ * (g * a)⁻¹ = x * cQ * x⁻¹ := by
          rw [← hg2]
          group
        calc (g * a)⁻¹ * x * cQ = (g * a)⁻¹ * (x * cQ * x⁻¹) * x := by group
          _ = (g * a)⁻¹ * ((g * a) * cQ * (g * a)⁻¹) * x := by rw [e]
          _ = cQ * ((g * a)⁻¹ * x) := by group
      have : x = (g * a) * ((g * a)⁻¹ * x) := by group
      rw [this]
      exact H.mul_mem (H.mul_mem (hP hgP) haH) (hP hk)

theorem isCoatom_Usig :
    IsCoatom Unitary.Usig := by
  have h : IsCoatom (MulAction.stabilizer CFSG.Monster.B.Co2.Pgrp (0 : CFSG.Monster.B.Co2.Ω)) :=
    (MulAction.isCoatom_stabilizer_iff_preprimitive (G := CFSG.Monster.B.Co2.Pgrp)
      (a := (0 : CFSG.Monster.B.Co2.Ω))).2 inferInstance
  rw [← Unitary.map_Usig] at h
  exact (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup Unitary.kvEquivP) Unitary.Usig).1 h

theorem Cr_not_le_Usig :
    ¬ Co2Inv.Cr ≤ Unitary.Usig := by
  intro h
  have hd := Subgroup.card_dvd_of_le h
  rw [Co2Inv.natCard_Cr, Unitary.natCard_Usig] at hd
  norm_num at hd

theorem P1_sup_H1 :
    P1 ⊔ H1 = Jhat := by
  apply le_antisymm (sup_le P1_le_Jhat H1_le_Jhat)
  set M := (P1 ⊔ H1).subgroupOf Jhat
  have hker : jhatToKv0.ker ≤ M := by
    rw [ker_jhatToKv0]
    intro e he
    have he' : (e : Dfull) ∈ Ehat := Subgroup.mem_subgroupOf.1 he
    show (e : Dfull) ∈ P1 ⊔ H1
    exact (le_sup_right : H1 ≤ P1 ⊔ H1) (Ehat_le_H1 he')
  have hU : Unitary.Usig ≤ M.map jhatToKv0 := by
    rw [← map_P1]
    exact Subgroup.map_mono fun x hx => by
      have hx' : (x : Dfull) ∈ P1 := Subgroup.mem_subgroupOf.1 hx
      show (x : Dfull) ∈ P1 ⊔ H1
      exact (le_sup_left : P1 ≤ P1 ⊔ H1) hx'
  have hC : Co2Inv.Cr ≤ M.map jhatToKv0 := by
    intro k hk
    obtain ⟨g, rfl⟩ := jhatToKv0_surjective k
    refine ⟨g, ?_, rfl⟩
    show (g : Dfull) ∈ P1 ⊔ H1
    exact (le_sup_right : H1 ≤ P1 ⊔ H1) ⟨g, hk, rfl⟩
  have htop : M.map jhatToKv0 = ⊤ :=
    isCoatom_Usig.2 _ (lt_of_le_of_ne hU fun h => Cr_not_le_Usig (h ▸ hC))
  intro g hg
  have hg' : (⟨g, hg⟩ : Jhat) ∈ M := by
    have h1 : (⟨g, hg⟩ : Jhat) ∈ (M.map jhatToKv0).comap jhatToKv0 := by
      rw [htop]
      exact Subgroup.mem_top _
    rwa [Subgroup.comap_map_eq, sup_eq_left.2 hker] at h1
  exact hg'

theorem closure_Eam_eq
    {a : Dfull} (ha : a ∈ Ehat) (hn : a ∉ N1) :
    Subgroup.closure (insert a (Eam : Set Dfull)) = Shat := by
  set H := Subgroup.closure (insert a (Eam : Set Dfull))
  have hE : Eam ≤ H := fun x hx => Subgroup.subset_closure (Set.mem_insert_of_mem _ hx)
  have haH : a ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (rfl | hx)
    · exact Ehat_le_Shat ha
    · exact Eam_le_Shat hx
  · have hX : Xgrp ≤ H := by
      rw [← closure_P4_eq (Ehat_le_Xgrp ha) (Ehat_not_mem_P4 ha hn), Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact haH
      · exact hE (Pc_le_Eam 3 hx)
    have hJ : Jhat ≤ H := by
      rw [← P1_sup_H1]
      exact sup_le ((Pc_le_Eam 0).trans hE) (H1_le_Xgrp.trans hX)
    have hN : Ntwo ≤ H := by
      rw [Ntwo_eq_closure, Subgroup.closure_le]
      rintro x (rfl | hx)
      · exact hE (Pc_le_Eam 1 tauhat_mem_P2)
      · exact hJ hx.1
    rw [Shat_eq_sup]
    exact sup_le hJ hN

theorem short_F4_coset_step_and_generation :
    (∃ a ∈ Ehat, a ∉ Nc 0) ∧
    ∀ a ∈ Ehat, a ∉ Nc 0 →
      a⁻¹ * cQ * a = cQ * xhat ∧ a * a ∈ Subgroup.zpowers xhat ∧
      Subgroup.zpowers xhat ≤ Pc 0 ∧
      (Pc 0).map (MulAut.conj a⁻¹).toMonoidHom = Pc 0 ∧
      Eam ⊓ Eam.map (MulAut.conj a⁻¹).toMonoidHom = Pc 0 ∧
      a ∈ Xgrp ∧ a ∉ Pc 3 ∧
      Subgroup.closure (insert a (Pc 3 : Set Dfull)) = Xgrp ∧
      Subgroup.closure (insert a (Eam : Set Dfull)) = Shat ∧
      (∀ a' ∈ Ehat, a' ∉ Nc 0 →
        DoubleCoset.doubleCoset a' (Eam : Set Dfull) Eam =
          DoubleCoset.doubleCoset a Eam Eam) ∧
      (DoubleCoset.doubleCoset a (Eam : Set Dfull) Eam)⁻¹ = DoubleCoset.doubleCoset a Eam Eam := by
  have h0 : Nc 0 = N1 := Nc_zero
  rw [h0]
  refine ⟨exists_mem_Ehat_not_mem_N1, fun a ha hn => ⟨conj_cQ_of_not_mem ha hn,
    mul_self_mem_zpowers_xhat ha, zpowers_xhat_le_P1, map_conj_P1 ha hn, Eam_inf_conj ha hn,
    Ehat_le_Xgrp ha, Ehat_not_mem_P4 ha hn,
    closure_P4_eq (Ehat_le_Xgrp ha) (Ehat_not_mem_P4 ha hn), closure_Eam_eq ha hn,
    fun a' ha' hn' => doubleCoset_eq ha hn ha' hn', doubleCoset_inv ha⟩⟩

end CFSG.Monster.B.TwoA.Amalgam
