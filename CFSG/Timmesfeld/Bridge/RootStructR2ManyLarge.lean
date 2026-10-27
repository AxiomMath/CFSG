module

public import CFSG.Timmesfeld.Bridge.RootStructR2ManyModule
public import CFSG.Timmesfeld.Bridge.RootStructWTIL2
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyCore

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace RootMany

variable {G : Type} [Group G] {D : Set G} [Finite G] (C : ThinGateCounter G D) {a d : G}
  (ha : a ∈ D) (hd : d ∈ D) (had : Commute a d) (hadD : a * d ∈ D) (hdT : d ∉ rootSet D a)
include C ha hd had hadD hdT

omit [Finite G] in
theorem exists_conj_mul_inv_not_mem (h3 : 3 ≤ (rootLines D a).ncard) :
    ∃ x ∈ lineGroup D a d, ∃ c ∈ nCore D a, x * c * x⁻¹ * c⁻¹ ∉ rootGroup D a := by
  have hLS := lineSetting_of_counter C
  have hT : rootGroup D a ⊔ rootGroup D d ∈ rootLines D a := ⟨d, hd, had, hadD, hdT, rfl⟩
  obtain ⟨L₁, hL₁, hL₁T⟩ := hLS.exists_ne_mem_rootLines ha hT
  obtain ⟨L₂, hL₂, hL₂T, hL₂₁⟩ :=
    exists_mem_rootLines_ne_ne (L₁ := rootGroup D a ⊔ rootGroup D d) (L₂ := L₁) h3
  obtain ⟨x, hx, hxL⟩ := hLS.exists_mem_lineRadical_map_conj_eq ha hT hL₁ hL₂ hL₁T hL₂T
  have hxR := hLS.lineRadical_le_lineGroup ha hd had hadD hdT h3 hT hx
  have hxa : x * a * x⁻¹ = a := by
    rw [Subgroup.mem_centralizer_singleton_iff.1 (lineGroup_le_centralizer D a d hxR),
      mul_inv_cancel_right]
  obtain ⟨c, hc, hac, hacD, hcT, rfl⟩ := hL₁
  refine ⟨x, hxR, c, hLS.sup_rootGroup_le_nCore ha hc hac (right_mem_line hc), fun hmem => ?_⟩
  have hc'D : x * c * x⁻¹ ∈ D := C.hyp.conj_mem x hc
  have hac' : Commute a (x * c * x⁻¹) := by
    have h := hac.map (MulAut.conj x)
    rwa [MulAut.conj_apply, MulAut.conj_apply, hxa] at h
  have hc'T : x * c * x⁻¹ ∉ rootSet D a := by
    intro h
    rw [← hxa, C.hyp.rootSet_conj] at h
    obtain ⟨y, hy, hyc⟩ := h
    have : y = c := by simpa using hyc
    exact hcT (this ▸ hy)
  have hc'L₁ : x * c * x⁻¹ ∈ rootGroup D a ⊔ rootGroup D c := by
    rw [show x * c * x⁻¹ = x * c * x⁻¹ * c⁻¹ * c by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hmem) (right_mem_line hc)
  have hc'L₂ : x * c * x⁻¹ ∈ L₂ := by
    rw [← hxL]
    exact ⟨c, right_mem_line hc, rfl⟩
  obtain ⟨e, he, hae, haeD, heT, rfl⟩ := hL₂
  have h1 := hLS.sup_rootGroup_eq_of_mem_sup ha hc'D hc hac' hc'T hac hacD hcT hc'L₁
  have h2 := hLS.sup_rootGroup_eq_of_mem_sup ha hc'D he hac' hc'T hae haeD heT hc'L₂
  exact hL₂₁ (h2.symm.trans h1)

theorem le_card_nCore_of_two_le {q n : ℕ} (K : ThinGateCount G D q n 2) (hn : 2 ≤ n) :
    q ^ (2 * n + 1) ≤ Nat.card (nCore D a) := by
  classical
  have hD := C.hyp.root
  have hLS := lineSetting_of_counter C
  have hAa : a ∈ rootGroup D a := rootSet_subset_rootGroup D a (mem_rootSet_self ha)
  have hq : 2 ≤ q := by
    rw [← K.card_rootGroup a ha]
    refine (Subgroup.one_lt_card_iff_ne_bot _).mpr fun h => hD.ne_one ha ?_
    rw [← Subgroup.mem_bot, ← h]
    exact hAa
  have hqn : 4 ≤ q ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ q ^ 2 := Nat.pow_le_pow_left hq 2
      _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn
  have hlines := K.ncard_rootLines a ha
  have h3 : 3 ≤ (rootLines D a).ncard := by omega
  obtain ⟨m, -, hmcard, hMR, -, ⟨f, hf, hker⟩, -⟩ :=
    rootLinesL2Step G D hLS a ha d hd had hadD hdT h3
  have hqm : 2 ^ m = q ^ n := by omega
  have hm : 2 ≤ m := by
    by_contra hm
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hAM : rootGroup D a ≤ nCore D a :=
    le_sup_left.trans (hLS.sup_rootGroup_le_nCore ha hd had)
  have hAR : rootGroup D a ≤ lineGroup D a d := hAM.trans hMR
  have hRN := hLS.lineGroup_le_normalizer (a := a) d
  have hAn : ((rootGroup D a).subgroupOf (lineGroup D a d)).Normal := by
    refine ⟨fun y hy r => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hy ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact (Subgroup.mem_normalizer_iff.1 (hRN r.2) y).1 hy
  obtain ⟨x, hxR, c, hcM, hxc⟩ := exists_conj_mul_inv_not_mem C ha hd had hadD hdT h3
  have hmain := sq_mul_card_le_card hm (F := GaloisField 2 m) (GaloisField.card 2 m (by omega)) f
    hf (M := (nCore D a).subgroupOf (lineGroup D a d))
    (A := (rootGroup D a).subgroupOf (lineGroup D a d))
    (fun y hy => Subgroup.mem_subgroupOf.2 (hAM (Subgroup.mem_subgroupOf.1 hy))) hker
    (fun y hy z hz => by
      rw [Subgroup.mem_subgroupOf] at hy hz ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact nCoreCommutatorInRoot_of_hyp C.hyp C.closure a ha _ hy _ hz)
    (fun y hy => by
      rw [Subgroup.mem_subgroupOf] at hy ⊢
      exact mul_self_mem_rootGroup_of_mem_nCore C.hyp C.closure ha hy)
    ⟨⟨x, hxR⟩, ⟨c, hMR hcM⟩, Subgroup.mem_subgroupOf.2 hcM, fun h => hxc (by
      rw [Subgroup.mem_subgroupOf] at h
      simpa using h)⟩
  have hA : Nat.card ↥((rootGroup D a).subgroupOf (lineGroup D a d)) = q := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAR).toEquiv, K.card_rootGroup a ha]
  have hM : Nat.card ↥((nCore D a).subgroupOf (lineGroup D a d)) = Nat.card (nCore D a) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMR).toEquiv
  rw [hA, hM, hqm, ← pow_mul, mul_comm n 2, ← pow_succ] at hmain
  exact hmain

end RootMany

end CFSG.Timmesfeld.Bridge
