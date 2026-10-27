module

public import CFSG.Quasithin.AppendixH.H16.OctadZData
public import CFSG.Quasithin.AppendixH.H16.OctadQuad

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] def octWz : Subgroup W11 := maskSub 11 wz0Basis

@[expose] def octVz : Subgroup W11 := maskSub 11 vz0Basis

@[expose] def octZ8 : Subgroup W11 := maskSub 11 z8Basis

theorem rk_octVz : rk ↥octVz = 4 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rk, octVz, card_maskSub vz0Basis_lt vz0_nodup, padicValNat.prime_pow]
  rfl

theorem rk_octZ8 : rk ↥octZ8 = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [rk, octZ8, card_maskSub z8Basis_lt z8_nodup, padicValNat.prime_pow]
  rfl

theorem card_octVz : Nat.card ↥octVz = 16 := by
  rw [octVz, card_maskSub vz0Basis_lt vz0_nodup]
  rfl

theorem octV5_inf_octWz : octV5 ⊓ octWz = octVz := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hx5, hxw⟩ := hx
    rw [octV5, mem_maskSub] at hx5
    obtain ⟨m1, hm1, rfl⟩ := hx5
    rw [octWz, mem_maskSub] at hxw
    obtain ⟨m2, hm2, hm2eq⟩ := hxw
    have hm21 : m2 = m1 := toW_inj (combos_lt wz0Basis_lt m2 hm2) (combos_lt oct5Basis_lt m1 hm1) hm2eq
    rw [hm21] at hm2
    rw [octVz]
    exact toW_mem_maskSub ((oct5_inf_wz0 m1 (combos_lt oct5Basis_lt m1 hm1)).1 ⟨hm1, hm2⟩)
  · rw [octVz, octV5, octWz]
    refine le_inf ?_ ?_
    · rintro v ⟨m, hm, rfl⟩
      exact toW_mem_maskSub ((oct5_inf_wz0 m (combos_lt vz0Basis_lt m hm)).mpr hm).1
    · rintro v ⟨m, hm, rfl⟩
      exact toW_mem_maskSub ((oct5_inf_wz0 m (combos_lt vz0Basis_lt m hm)).mpr hm).2

theorem octVz_le_octV5 : octVz ≤ octV5 := by
  rw [← octV5_inf_octWz]
  exact inf_le_left

theorem octVz_le_octWz : octVz ≤ octWz := by
  rw [← octV5_inf_octWz]
  exact inf_le_right

theorem octWz_sup_octV5 : octWz ⊔ octV5 = octZ8 := by
  refine le_antisymm ?_ ?_
  · rw [octWz, octV5, octZ8]
    refine sup_le ?_ ?_
    · rintro v ⟨m, hm, rfl⟩
      exact toW_mem_maskSub (wz0_sub_z8 m hm)
    · rintro v ⟨m, hm, rfl⟩
      exact toW_mem_maskSub (oct5_sub_z8 m hm)
  · intro x hx
    rw [octZ8, mem_maskSub] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    obtain ⟨a, ha, b, hb, rfl⟩ := z8_sub_sum m hm
    rw [toW_xor]
    refine Subgroup.mul_mem_sup ?_ ?_
    · rw [octWz]; exact toW_mem_maskSub ha
    · rw [octV5]; exact toW_mem_maskSub hb

theorem toW_three_mem_octVz : toW 11 3 ∈ octVz := by
  rw [octVz]
  exact toW_mem_maskSub (mem_combos_of_mem (by simp [vz0Basis]))

theorem mem_octV5_split {x : W11} (hx : x ∈ octV5) : x ∈ octVz ∨ x * toW 11 1024 ∈ octVz := by
  rw [octV5, mem_maskSub] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  rcases oct5_split_vz m hm with h | h
  · left; rw [octVz]; exact toW_mem_maskSub h
  · right
    rw [octVz, ← toW_xor]
    exact toW_mem_maskSub h

theorem toW_1024_mem_octV5 : toW 11 1024 ∈ octV5 := by
  rw [octV5]
  exact toW_mem_maskSub (mem_combos_of_mem (by simp [oct5Basis]))

theorem toW_1024_not_mem_octVz : toW 11 1024 ∉ octVz := by
  rw [octVz, toW_mem_maskSub_iff_of_lt vz0Basis_lt (show 1024 < 2 ^ 11 by norm_num)]
  exact not_mem_vz_1024

private theorem mem_fixV_zpowers_iff {V : Type*} [CommGroup V] {a : MulAut V} {x : V} :
    x ∈ fixV (Subgroup.zpowers a) ↔ a x = x := by
  constructor
  · intro hx
    exact mem_fixV.1 hx a (Subgroup.mem_zpowers a)
  · intro hx
    rw [mem_fixV]
    intro g hg
    have hle : Subgroup.zpowers a ≤ MulAction.stabilizer (MulAut V) x :=
      Subgroup.zpowers_le.mpr ((MulAction.mem_stabilizer_iff).2 (by simpa [MulAut.smul_def] using hx))
    have hg' := hle hg
    rwa [MulAction.mem_stabilizer_iff, MulAut.smul_def] at hg'

private theorem imgCd_zpowers_koOne_eq :
    imgCd (Subgroup.zpowers (koPerm 1)) = Subgroup.zpowers (ko11 1) := by
  have hsub : (Subgroup.zpowers (koPerm 1)).subgroupOf AutPerm =
      Subgroup.zpowers (⟨koPerm 1, (koPerm_mem_mog22 (1 : Fin 16)).1.1⟩ : ↥AutPerm) := by
    refine le_antisymm ?_ ?_
    · intro σ hσ
      rw [Subgroup.mem_subgroupOf] at hσ
      rw [Subgroup.mem_zpowers_iff] at hσ
      rw [Subgroup.mem_zpowers_iff]
      obtain ⟨n, hn⟩ := hσ
      refine ⟨n, Subtype.ext ?_⟩
      simpa using hn
    · intro σ hσ
      rw [Subgroup.mem_subgroupOf]
      rw [Subgroup.mem_zpowers_iff]
      rw [Subgroup.mem_zpowers_iff] at hσ
      obtain ⟨n, hn⟩ := hσ
      refine ⟨n, ?_⟩
      have h := congrArg Subtype.val hn
      simpa using h
  rw [imgCd, hsub, MonoidHom.map_zpowers]
  rfl

theorem fixV_imgCd_zpowers_koOne : fixV (imgCd (Subgroup.zpowers (koPerm 1))) = octWz := by
  rw [imgCd_zpowers_koOne_eq]
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [mem_fixV_zpowers_iff] at hx
    obtain ⟨m, hm, rfl⟩ := toW_surj 11 x
    rw [ko11_toW] at hx
    have heq : actC11 (koArr 1) m = m := toW_inj (actC11_lt (koArr 1) m) hm hx
    rw [octWz]
    exact toW_mem_maskSub ((fix_koOne_iff m hm).1 heq)
  · intro x hx
    rw [mem_fixV_zpowers_iff]
    rw [octWz, mem_maskSub] at hx
    obtain ⟨m, hm, rfl⟩ := hx
    rw [ko11_toW]
    change toW 11 (actC11 (koArr 1) m) = toW 11 m
    rw [(fix_koOne_iff m (combos_lt wz0Basis_lt m hm)).2 hm]

theorem octQ_eq_zero_of_mem_octZ8 {x : W11} (hx : x ∈ octZ8) : octQ x = 0 := by
  rw [octZ8, mem_maskSub] at hx
  obtain ⟨m, hm, rfl⟩ := hx
  rw [octQ_toW, octQmask_z8 m hm]
  rfl

theorem clause3c_std :
    rk ↥(fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) ⊔ octV5) = 8 ∧
      ∀ x ∈ fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) ⊔ octV5,
        octQ x = 0 := by
  have hfix : fixV (rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1))) = octWz := by
    rw [show rImg (rhoC11 AutPerm le_rfl) (Subgroup.zpowers (koPerm 1)) =
        imgCd (Subgroup.zpowers (koPerm 1)) from rfl]
    exact fixV_imgCd_zpowers_koOne
  rw [hfix, octWz_sup_octV5]
  exact ⟨rk_octZ8, fun x hx => octQ_eq_zero_of_mem_octZ8 hx⟩

end CFSG.ASVolI.H16
