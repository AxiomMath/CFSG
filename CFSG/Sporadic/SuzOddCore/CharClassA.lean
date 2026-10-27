module

public import CFSG.Sporadic.SuzOddCore.ThreeLocalE

public noncomputable section

namespace CFSG.Sporadic.SuzOddCore

open CFSG.Certificates CFSG.Monster.B.Co2
open scoped Pointwise

@[expose] def suzQP : Subgroup suzP := suzQ.subgroupOf suzP

@[expose] def zP :
    suzP := ⟨suzZ, suzZ_mem_suzP⟩

theorem suzQP_eq :
    suzQP = Subgroup.zpowers zP := by
  ext x
  rw [suzQP, Subgroup.mem_subgroupOf, suzQ, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [SubgroupClass.coe_zpow]; exact hk)⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by rw [SubgroupClass.coe_zpow]; rfl⟩

abbrev autMap (α : MulAut suzP) (H : Subgroup suzP) : Subgroup suzP := H.map α.toMonoidHom

@[expose] def suzClassQ : Set (Subgroup suzP) := {H | ∃ g : suzP, autMap (MulAut.conj g) suzQP = H}

theorem smul_eq_autMap (α : MulAut suzP) (H : Subgroup suzP) : α • H = autMap α H := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
  rfl

theorem autMap_mul (α β : MulAut suzP) (H : Subgroup suzP) :
    autMap (α * β) H = autMap α (autMap β H) := by
  rw [autMap, autMap, autMap, Subgroup.map_map]
  rfl

theorem autMap_one (H : Subgroup suzP) : autMap 1 H = H := by
  rw [autMap]
  exact Subgroup.map_id H

theorem card_normalizer_subgroupOf {G : Type*} [Group G] {H K : Subgroup G} (h : H ≤ K) :
    Nat.card (Subgroup.normalizer (H.subgroupOf K : Set K)) =
      Nat.card (K ⊓ Subgroup.normalizer (H : Set G) : Subgroup G) := by
  rw [← Subgroup.subgroupOf_normalizer_eq h, ← Subgroup.card_map_of_injective K.subtype_injective,
    Subgroup.subgroupOf_map_subtype, inf_comm]

theorem card_normalizer_autMap (α : MulAut suzP) (H : Subgroup suzP) :
    Nat.card (Subgroup.normalizer (autMap α H : Set suzP)) =
      Nat.card (Subgroup.normalizer (H : Set suzP)) := by
  rw [autMap, ← Subgroup.map_equiv_normalizer_eq,
    Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective]

@[expose] def suzS3P : Subgroup suzP := suzS3.subgroupOf suzP

theorem suzLine_le_suzP
    {r : ℕ} (hr : r < 9) : suzLine r ≤ suzP := by
  rw [suzLine, Subgroup.zpowers_le]
  exact suzS3_le_suzP (centerFullPerm_mem hr)

theorem normalizer_line_lt
    {r : ℕ} (hr : r = 3 ∨ r = 4) :
    Nat.card (suzP ⊓ Subgroup.normalizer (suzLine r : Set (Equiv.Perm (Fin 22880))) :
      Subgroup (Equiv.Perm (Fin 22880))) < Nat.card suzH0 := by
  obtain ⟨-, -, -, h3, h4, -⟩ := fusionNormChecks_facts
  have hb : 39 * Nat.card (normP (centerFullPerm r)) ≤ 38 * Nat.card suzH0 := by
    rcases hr with rfl | rfl
    · have hfix : {x : Fin 22880 | centerFullPerm 3 x = x}.ncard = 38 := by
        rw [fixed_centerFull (by norm_num), h3]
      exact normalizer_bound (centerFullPerm_mem (by norm_num)) hfix rho_e3
    · have hfix : {x : Fin 22880 | centerFullPerm 4 x = x}.ncard = 38 := by
        rw [fixed_centerFull (by norm_num), h4]
      exact normalizer_bound (centerFullPerm_mem (by norm_num)) hfix rho_e4
  change Nat.card (normP (centerFullPerm r)) < Nat.card suzH0
  rw [card_suzH0] at hb ⊢
  omega

theorem central_of_map_eq
    {β : MulAut suzP} (hβ : autMap β suzS3P = suzS3P) :
    (β zP : Equiv.Perm (Fin 22880)) ∈ suzZS := by
  have hz : zP ∈ suzS3P := by
    rw [suzS3P, Subgroup.mem_subgroupOf]
    exact suzZ_mem_suzS3
  have hβz : β zP ∈ suzS3P := by
    rw [← hβ]
    exact Subgroup.mem_map_of_mem _ hz
  have hinv : autMap β⁻¹ suzS3P = suzS3P := by
    conv_lhs => rw [← hβ]
    rw [← autMap_mul, inv_mul_cancel, autMap_one]
  refine ⟨by rw [suzS3P, Subgroup.mem_subgroupOf] at hβz; exact hβz, fun y hy => ?_⟩
  have hyP : y ∈ suzP := suzS3_le_suzP hy
  set y' : suzP := ⟨y, hyP⟩
  have hy' : y' ∈ suzS3P := by rw [suzS3P, Subgroup.mem_subgroupOf]; exact hy
  have hpre : β⁻¹ y' ∈ suzS3P := by
    rw [← hinv]
    exact Subgroup.mem_map_of_mem _ hy'
  have hcomm : zP * β⁻¹ y' = β⁻¹ y' * zP := by
    apply Subtype.ext
    rw [suzS3P, Subgroup.mem_subgroupOf] at hpre
    exact suzZ_central _ hpre
  have := congrArg β hcomm
  rw [map_mul, map_mul, MulAut.apply_inv_self] at this
  exact congrArg Subtype.val this

theorem zP_ne_one :
    zP ≠ 1 := fun h => suzZ_ne_one (congrArg Subtype.val h)

theorem autMap_suzQP_map
    (β : MulAut suzP) :
    (autMap β suzQP).map suzP.subtype = Subgroup.zpowers (β zP : Equiv.Perm (Fin 22880)) := by
  rw [suzQP_eq, autMap, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
  rfl

theorem eq_of_map_subtype {H K : Subgroup suzP} (h : H.map suzP.subtype = K.map suzP.subtype) :
    H = K :=
  Subgroup.map_injective suzP.subtype_injective h

theorem suzQP_map :
    suzQP.map suzP.subtype = suzQ := by
  rw [suzQP, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (suzQ_le_suzH0.trans suzH0_le_suzP)]

theorem card_normalizer_suzQP :
    Nat.card (Subgroup.normalizer (suzQP : Set suzP)) = Nat.card suzH0 := by
  rw [suzQP, card_normalizer_subgroupOf (suzQ_le_suzH0.trans suzH0_le_suzP),
    suzP_inf_normalizer_Q]

@[expose] def fusionGP : suzP := ⟨suzFusionG, suzFusionG_mem⟩

theorem autMap_suzQP_of_fix
    {β : MulAut suzP} (hβ : autMap β suzS3P = suzS3P) :
    autMap β suzQP = suzQP ∨ autMap β suzQP = autMap (MulAut.conj fusionGP) suzQP := by
  have hc := central_of_map_eq hβ
  rw [suzS3_center_eq] at hc
  obtain ⟨r, hr⟩ := hc
  simp only at hr
  have hr0 : (r : ℕ) ≠ 0 := by
    intro h
    have e : r = ⟨0, by norm_num⟩ := Fin.ext h
    rw [e, centerFullPerm_zero] at hr
    have : β zP = 1 := Subtype.ext hr.symm
    rw [map_eq_one_iff _ β.injective] at this
    exact zP_ne_one this
  have hmap : (autMap β suzQP).map suzP.subtype = suzLine r := by
    rw [autMap_suzQP_map, ← hr]
    rfl
  have hcard : Nat.card (suzP ⊓ Subgroup.normalizer (suzLine r : Set (Equiv.Perm (Fin 22880))) :
      Subgroup (Equiv.Perm (Fin 22880))) = Nat.card suzH0 := by
    have h1 := card_normalizer_autMap β suzQP
    rw [card_normalizer_suzQP] at h1
    have h2 : autMap β suzQP = (suzLine r).subgroupOf suzP := by
      apply eq_of_map_subtype
      rw [hmap, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 (suzLine_le_suzP r.2)]
    rw [h2, card_normalizer_subgroupOf (suzLine_le_suzP r.2)] at h1
    exact h1
  rcases suzLine_of_mem r.2 hr0 with h | h | h | h
  · left
    apply eq_of_map_subtype
    rw [hmap, h, fusion_lines.1, suzQP_map]
  · exfalso
    rw [h] at hcard
    exact absurd hcard (normalizer_line_lt (Or.inl rfl)).ne
  · exfalso
    rw [h] at hcard
    exact absurd hcard (normalizer_line_lt (Or.inr rfl)).ne
  · right
    apply eq_of_map_subtype
    rw [hmap, h, ← fusion_lines.2, ← suzQP_map, autMap, Subgroup.map_map, Subgroup.map_map]
    congr 1

theorem aut_map_suzQP_mem
    (α : MulAut suzP) : autMap α suzQP ∈ suzClassQ := by
  have hcard : Nat.card (autMap α suzS3P) = 3 ^ (Nat.card suzP).factorization 3 := by
    rw [autMap, Subgroup.card_map_of_injective (f := α.toMonoidHom) α.injective, suzS3P,
      ← suzSylowThree_coe, Sylow.card_eq_multiplicity]
  let T : Sylow 3 suzP := Sylow.ofCard _ hcard
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq suzP T suzSylowThree
  have hβ : autMap (MulAut.conj g * α) suzS3P = suzS3P := by
    have h1 := congrArg (fun P : Sylow 3 suzP => (P : Subgroup suzP)) hg
    simp only [Sylow.coe_subgroup_smul, smul_eq_autMap] at h1
    rw [autMap_mul]
    exact h1
  rcases autMap_suzQP_of_fix hβ with h | h
  · refine ⟨g⁻¹, ?_⟩
    rw [autMap_mul] at h
    have h2 := congrArg (autMap (MulAut.conj g)⁻¹) h
    rw [← autMap_mul, inv_mul_cancel, autMap_one] at h2
    rw [map_inv]
    exact h2.symm
  · refine ⟨g⁻¹ * fusionGP, ?_⟩
    rw [autMap_mul] at h
    have h2 := congrArg (autMap (MulAut.conj g)⁻¹) h
    rw [← autMap_mul, inv_mul_cancel, autMap_one, ← autMap_mul] at h2
    rw [map_mul, map_inv]
    exact h2.symm

theorem aut_mul_conj (α : MulAut suzP) (g : suzP) :
    α * MulAut.conj g = MulAut.conj (α g) * α := by
  ext x
  simp [MulAut.conj_apply]

theorem aut_map_mem_classQ
    (α : MulAut suzP) {H : Subgroup suzP} (hH : H ∈ suzClassQ) :
    autMap α H ∈ suzClassQ := by
  obtain ⟨g, rfl⟩ := hH
  obtain ⟨h, hh⟩ := aut_map_suzQP_mem α
  refine ⟨α g * h, ?_⟩
  rw [← autMap_mul, aut_mul_conj, autMap_mul, ← hh, ← autMap_mul, map_mul]

end CFSG.Sporadic.SuzOddCore
