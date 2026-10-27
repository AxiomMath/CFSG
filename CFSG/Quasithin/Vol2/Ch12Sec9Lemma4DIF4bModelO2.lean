module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF4bModelO

public section

namespace CFSG.Quasithin.H13.C1294.Model

open CFSG.Quasithin

@[expose] def HM : Subgroup (VM ≃ₗ[ZMod 2] VM) := stabM Sm ⊓ GM

theorem mem_HM_iff (h : VM ≃ₗ[ZMod 2] VM) : h ∈ HM ↔ (∀ v, v ∈ Sm ↔ h v ∈ Sm) ∧ h ∈ GM :=
  Subgroup.mem_inf

theorem HM_mem_Sm (h : ↥HM) {s : VM} (hs : s ∈ Sm) : (h : VM ≃ₗ[ZMod 2] VM) s ∈ Sm :=
  (((mem_HM_iff _).1 h.2).1 s).1 hs

theorem HM_ne_zero (h : ↥HM) {s : VM} (hs : s ≠ 0) : (h : VM ≃ₗ[ZMod 2] VM) s ≠ 0 := fun h0 =>
  hs ((h : VM ≃ₗ[ZMod 2] VM).map_eq_zero_iff.1 h0)

@[expose] def TSm : Type := {s : VM // s ∈ Sm ∧ s ≠ 0}

instance : MulAction ↥HM TSm where
  smul h s := ⟨(h : VM ≃ₗ[ZMod 2] VM) s.1, HM_mem_Sm h s.2.1, HM_ne_zero h s.2.2⟩
  one_smul s := Subtype.ext rfl
  mul_smul h k s := Subtype.ext rfl

theorem smul_TSm_val (h : ↥HM) (s : TSm) : (h • s).1 = (h : VM ≃ₗ[ZMod 2] VM) s.1 := rfl

theorem eq_mkV_zero_of_Sm {s : VM} (hs : s ∈ Sm) : mkV (xp s) 0 = s := by
  have hyv : yp s = 0 := (mem_Sm_iff_yp s).1 hs
  have e : mkV (xp s) (yp s) = s := mkV_xp_yp s
  rw [hyv] at e
  exact e

theorem mkV_zero_zero : mkV (0 : Fin 3 → ZMod 2) 0 = 0 := by
  funext k
  cases k <;> rfl

theorem xp_ne_zero_of_TSm (s : TSm) : xp s.1 ≠ 0 := by
  intro h0
  apply s.2.2
  rw [← eq_mkV_zero_of_Sm s.2.1, h0, mkV_zero_zero]

instance : Finite TSm := Subtype.finite

theorem card_TSm : Nat.card TSm = 7 := by
  have e : TSm ≃ {x : Fin 3 → ZMod 2 // x ≠ 0} :=
    { toFun := fun s => ⟨xp s.1, xp_ne_zero_of_TSm s⟩
      invFun := fun x => ⟨mkV x.1 0, mem_Sm_mkV_zero x.1, fun h0 => x.2 (by
        have := congrArg xp h0
        simpa using this)⟩
      left_inv := fun s => Subtype.ext (eq_mkV_zero_of_Sm s.2.1)
      right_inv := fun x => Subtype.ext (xp_mkV x.1 0) }
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

theorem GL3_trans_e0 : ∀ x : Fin 3 → ZMod 2, x ≠ 0 →
    ∃ A : Matrix (Fin 3) (Fin 3) (ZMod 2), A.det ≠ 0 ∧ Matrix.mulVec A (ex 0) = x := by
  decide +kernel

@[expose] def baseTSm : TSm := ⟨mkV (ex 0) 0, mem_Sm_mkV_zero _, fun h0 => by
  have := congrArg xp h0
  simp [ex] at this⟩

theorem HM_to_base (t : TSm) : ∃ h : ↥HM, h • baseTSm = t := by
  obtain ⟨A, hdet, hAx⟩ := GL3_trans_e0 (xp t.1) (xp_ne_zero_of_TSm t)
  have hAunit : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hdet)
  let u : GL3 := hAunit.unit
  have hu : (u : Matrix (Fin 3) (Fin 3) (ZMod 2)) = A := hAunit.unit_spec
  have hmem : LA u ∈ HM := Subgroup.mem_inf.2 ⟨LA_stab u, LA_mem_GM u⟩
  refine ⟨⟨LA u, hmem⟩, Subtype.ext ?_⟩
  rw [smul_TSm_val]
  show LA u (mkV (ex 0) 0) = t.1
  rw [LA_mkV_zero, hu, hAx, eq_mkV_zero_of_Sm t.2.1]

theorem HM_trans (s t : TSm) : ∃ h : ↥HM, h • s = t := by
  obtain ⟨hs, hs_eq⟩ := HM_to_base s
  obtain ⟨ht, ht_eq⟩ := HM_to_base t
  refine ⟨ht * hs⁻¹, ?_⟩
  rw [mul_smul, ← hs_eq, inv_smul_smul, ht_eq]

theorem normal_two_fixes {N : Subgroup ↥HM} [N.Normal] (hN : IsPGroup 2 N) (s : TSm) :
    ∀ n : ↥N, (n : ↥HM) • s = s := by
  have hcard := hN.card_modEq_card_fixedPoints TSm
  rw [card_TSm] at hcard
  have hodd : Nat.card (MulAction.fixedPoints ↥N TSm) ≠ 0 := by
    intro h0
    rw [h0] at hcard
    norm_num [Nat.ModEq] at hcard
  obtain ⟨⟨s0, hs0⟩⟩ := (Nat.card_ne_zero.1 hodd).1
  have hfix0 : ∀ g : ↥N, (g : ↥HM) • s0 = s0 := fun g => MulAction.mem_fixedPoints.1 hs0 g
  intro n
  obtain ⟨h, hh⟩ := HM_trans s0 s
  have hk : h⁻¹ * (n : ↥HM) * h ∈ N := by
    have := Subgroup.Normal.conj_mem inferInstance (n : ↥HM) n.2 h⁻¹
    simpa using this
  have hkfix : (h⁻¹ * (n : ↥HM) * h) • s0 = s0 := hfix0 ⟨_, hk⟩
  rw [← hh]
  calc (n : ↥HM) • h • s0 = ((n : ↥HM) * h) • s0 := (mul_smul _ _ _).symm
    _ = (h * (h⁻¹ * (n : ↥HM) * h)) • s0 := by group
    _ = h • ((h⁻¹ * (n : ↥HM) * h) • s0) := mul_smul _ _ _
    _ = h • s0 := by rw [hkfix]

theorem fix_Sm_of_TSm (h : ↥HM) (hfix : ∀ s : TSm, h • s = s) (v : VM) (hv : v ∈ Sm) :
    (h : VM ≃ₗ[ZMod 2] VM) v = v := by
  by_cases h0 : v = 0
  · rw [h0, map_zero]
  · have := congrArg Subtype.val (hfix ⟨v, hv, h0⟩)
    exact this

theorem K0_yp (g : VM ≃ₗ[ZMod 2] VM) (hg : g ∈ K0) (v : VM) : yp (g v) = yp v := by
  obtain ⟨B, _, hB⟩ := GM_fix_Sm hg.1 (fun x => hg.2 (mkV x 0) (mem_Sm_mkV_zero x))
  rw [hB, gA_apply, gfun]
  simp

theorem K0_le_HM : K0 ≤ HM := by
  intro g hg
  refine Subgroup.mem_inf.2 ⟨fun v => ?_, hg.1⟩
  rw [mem_Sm_iff_yp, mem_Sm_iff_yp, K0_yp g hg]

theorem card_K0_subgroupOf : Nat.card (K0.subgroupOf HM) = 8 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe K0_le_HM).toEquiv, card_K0]

theorem K0_conj_HM (g : ↥HM) {k : VM ≃ₗ[ZMod 2] VM} (hk : k ∈ K0) :
    (g : VM ≃ₗ[ZMod 2] VM) * k * (g : VM ≃ₗ[ZMod 2] VM)⁻¹ ∈ K0 := by
  have hg := Subgroup.mem_inf.1 g.2
  refine ⟨mul_mem (mul_mem hg.2 hk.1) (inv_mem hg.2), fun v hv => ?_⟩
  have hmem : (g : VM ≃ₗ[ZMod 2] VM)⁻¹ v ∈ Sm := by
    have hstab := (mem_stabM_iff Sm _).1 hg.1 ((g : VM ≃ₗ[ZMod 2] VM)⁻¹ v)
    refine hstab.2 ?_
    have e : (g : VM ≃ₗ[ZMod 2] VM) (((g : VM ≃ₗ[ZMod 2] VM)⁻¹) v) = v :=
      LinearEquiv.apply_symm_apply _ v
    rw [e]
    exact hv
  show (g : VM ≃ₗ[ZMod 2] VM) (k ((g : VM ≃ₗ[ZMod 2] VM)⁻¹ v)) = v
  rw [hk.2 _ hmem]
  exact LinearEquiv.apply_symm_apply _ v

theorem K0_subgroupOf_normal : (K0.subgroupOf HM).Normal := by
  constructor
  intro n hn g
  exact Subgroup.mem_subgroupOf.2 (K0_conj_HM g (Subgroup.mem_subgroupOf.1 hn))

theorem K0_subgroupOf_isPGroup : IsPGroup 2 (K0.subgroupOf HM) :=
  IsPGroup.of_card (n := 3) (by rw [card_K0_subgroupOf]; norm_num)

theorem pCore_HM : CFSG.pCore 2 ↥HM = K0.subgroupOf HM := by
  unfold CFSG.pCore
  apply le_antisymm
  · apply sSup_le
    rintro N ⟨hNn, hNp⟩
    intro n hn
    haveI := hNn
    rw [Subgroup.mem_subgroupOf]
    exact ⟨(Subgroup.mem_inf.1 n.2).2, fun v hv =>
      fix_Sm_of_TSm n (fun s => normal_two_fixes hNp s ⟨n, hn⟩) v hv⟩
  · apply le_sSup
    exact ⟨K0_subgroupOf_normal, K0_subgroupOf_isPGroup⟩

end CFSG.Quasithin.H13.C1294.Model

end
