module

public import CFSG.Quasithin.AppendixH.H15.H157Fixpt

public section

namespace CFSG.ASVolI.AppH.H157

open CFSG.Quasithin CFSG.Quasithin.H153 CFSG.Quasithin.H.Coc24 CFSG.ASVolI.ChH CFSG.Monster.Code

@[expose] def Nt : Subgroup S24 :=
  M24g ⊓ Subgroup.normalizer ((Subgroup.zpowers tP : Subgroup S24) : Set S24)

theorem zpowers_tP_le_Nt : Subgroup.zpowers tP ≤ Nt := by
  rw [Subgroup.zpowers_le]
  exact ⟨tP_mem, Subgroup.le_normalizer (Subgroup.mem_zpowers tP)⟩

theorem Nt_le_M24g : Nt ≤ M24g := inf_le_left

theorem mem_tFix_iff_of_mem_Nt {n : S24} (hn : n ∈ Nt) (i : Fin 24) :
    n i ∈ tFix ↔ i ∈ tFix := by
  have hfwd : ∀ {n : S24}, n ∈ Nt → ∀ i, i ∈ tFix → n i ∈ tFix := by
    intro n hn i hi
    have hnN : n ∈ Subgroup.normalizer ((Subgroup.zpowers tP : Subgroup S24) : Set S24) :=
      (Subgroup.mem_inf.1 hn).2
    have htpi : tP i = i := (mem_tFix_iff i).1 hi
    have hmem : n⁻¹ * tP * n ∈ Subgroup.zpowers tP :=
      (Subgroup.mem_normalizer_iff''.1 hnN tP).1 (Subgroup.mem_zpowers tP)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hmul : tP * n = n * tP ^ k := by
      rw [hk]
      group
    have happ : tP (n i) = n i := by
      have h1 : (tP * n) i = (n * tP ^ k) i := congrArg (fun g : S24 => g i) hmul
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
        Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self htpi k] at h1
      exact h1
    exact (mem_tFix_iff (n i)).2 happ
  constructor
  · intro hni
    have hmem_inv : n⁻¹ ∈ Nt := Nt.inv_mem hn
    have h := hfwd hmem_inv (n i) hni
    simpa using h
  · exact hfwd hn i

noncomputable def actNt : ↥Nt →* Equiv.Perm ↥tFix where
  toFun n := (n : S24).subtypePerm (fun i => mem_tFix_iff_of_mem_Nt n.2 i)
  map_one' := by
    ext x
    rfl
  map_mul' n m := by
    ext x
    rfl

theorem card_Nt_le : Nat.card ↥Nt ≤ 2160 := by
  have hker : actNt.ker = (Subgroup.zpowers tP).subgroupOf Nt := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hn
      apply eq_zpowers_of_fix_tFix (Nt_le_M24g n.2)
      intro i hi
      have h := congrArg (fun g : Equiv.Perm ↥tFix => (g ⟨i, hi⟩ : Fin 24)) hn
      simpa [actNt] using h
    · intro hn
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hn
      have hmem : tP ^ k ∈ Nt :=
        zpowers_tP_le_Nt ((Subgroup.zpowers tP).zpow_mem (Subgroup.mem_zpowers tP) k)
      have heq : (⟨tP ^ k, hmem⟩ : ↥Nt) = n := Subtype.ext hk
      rw [← heq]
      apply Equiv.ext
      intro x
      apply Subtype.ext
      exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self ((mem_tFix_iff x.1).1 x.2) k
  have hcard_ker : Nat.card ↥actNt.ker = 3 := by
    rw [hker, Nat.card_congr (Subgroup.subgroupOfEquivOfLe zpowers_tP_le_Nt).toEquiv,
      Nat.card_zpowers, orderOf_tP]
  have hperm : Nat.card (Equiv.Perm ↥tFix) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_coe, card_tFix]
    norm_num
  have hrange : Nat.card ↥actNt.range ≤ 720 := by
    calc Nat.card ↥actNt.range ≤ Nat.card (Equiv.Perm ↥tFix) :=
          Subgroup.card_le_card_group actNt.range
      _ = 720 := hperm
  have h := Subgroup.card_ker_mul_card_range actNt
  calc Nat.card ↥Nt = Nat.card ↥actNt.ker * Nat.card ↥actNt.range := h.symm
    _ = 3 * Nat.card ↥actNt.range := by rw [hcard_ker]
    _ ≤ 3 * 720 := Nat.mul_le_mul_left 3 hrange
    _ = 2160 := by norm_num

theorem Nt_inf_KSp : Nt ⊓ KSp = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro k hk
  rw [Subgroup.mem_inf] at hk
  obtain ⟨hkN, hkK⟩ := hk
  obtain ⟨c, hc⟩ := mem_KSp_iff.1 hkK
  have hfix : ∀ i ∈ tFix, k i = i := by
    intro i hi
    have hki : k i ∈ tFix := (mem_tFix_iff_of_mem_Nt hkN i).2 hi
    have hcol : colOf (k i) = colOf i := by
      rw [← hc, colOf_ksP]
    calc k i = fixPt (colOf (k i)) := eq_fixPt_colOf hki
      _ = fixPt (colOf i) := by rw [hcol]
      _ = i := (eq_fixPt_colOf hi).symm
  have hz : k ∈ Subgroup.zpowers tP := eq_zpowers_of_fix_tFix (Nt_le_M24g hkN) hfix
  have h3 : k ^ 3 = 1 := by
    have := orderOf_dvd_of_mem_zpowers hz
    rw [orderOf_tP] at this
    exact orderOf_dvd_iff_pow_eq_one.1 this
  obtain ⟨m, hm⟩ := isPGroup_KSp ⟨k, hkK⟩
  have hm' : k ^ (2 ^ m) = 1 := by
    have := congrArg (Subtype.val) hm
    simpa [Subgroup.coe_pow] using this
  have hcop : Nat.Coprime 3 (2 ^ m) := (by decide : Nat.Coprime 3 2).pow_right m
  have hgcd : k ^ Nat.gcd 3 (2 ^ m) = 1 := (pow_gcd_eq_one (a := k)).2 ⟨h3, hm'⟩
  rw [hcop.gcd_eq_one, pow_one] at hgcd
  exact hgcd

end CFSG.ASVolI.AppH.H157
