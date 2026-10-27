module

import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod3B
public import CFSG.Quasithin.Vol2.Ch12Sec7ModCert2

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem s0_sub_s0p : ∀ s ∈ s0, s ∈ s0p := by decide

theorem s0_comp_s0p : ∀ x ∈ s0, ∀ y ∈ s0p, x.comp y ∈ s0p := by decide

theorem s0p_nodup : s0p.Nodup := by decide

theorem s0p_length : s0p.length = 16 := by decide

section Codes

variable {W : Type} [CommGroup W] (C : Coding W)

theorem two6_of_isPGroup_nm6 {H : Subgroup (MulAut W)}
    (hH : IsPGroup 2 H) {a : MulAut W} (haH : a ∈ H) (ha : C.cB a ∈ nm6) :
    two6 (C.cB a) = true := by
  obtain ⟨k, hk⟩ := hH ⟨a, haH⟩
  have hk' : a ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h60 : a ^ 60 = 1 := (C.pow_eq_one_iff a 60).2 (cert4_pow60 _ ha)
  have hdvd : orderOf a ∣ Nat.gcd (2 ^ k) 60 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk') (orderOf_dvd_of_pow_eq_one h60)
  have h4 : Nat.gcd (2 ^ k) 60 ∣ 4 := by
    have hg : Nat.gcd (2 ^ k) 60 ∣ 2 ^ k := Nat.gcd_dvd_left _ _
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hg
    rw [hj]
    have hj60 : 2 ^ j ∣ 60 := hj ▸ Nat.gcd_dvd_right _ _
    have : j ≤ 2 := by
      by_contra hj2
      have : 2 ^ 3 ∣ 60 := dvd_trans (pow_dvd_pow 2 (by omega)) hj60
      norm_num at this
    exact pow_dvd_pow 2 this
  have h4' : a ^ 4 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_trans hdvd h4)
  simp only [two6, ← C.cB_pow, h4', C.cB_one, beq_self_eq_true]

theorem conj_scalar_eq {z a : MulAut W} (hz : C.cB z ∈ zs6)
    (ha : C.cB a ∈ gm6) : z * a * z⁻¹ = a := by
  apply C.cB_injective
  rw [C.cB_mul, C.cB_mul, zs6_comm _ hz _ ha, B6.comp_assoc, ← C.cB_mul, mul_inv_cancel,
    C.cB_one, B6.comp_id]

end Codes

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem MVbar_surj
    (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    (hne : h.hyp.MVbar ≠ autOn L V) : ∀ B ∈ nm6, ∃ a ∈ h.hyp.MVbar, C.cB a = B := by
  classical
  have hc := card_MVbar_of_ne h hC hne
  set f := fun m : ↥h.hyp.MVbar =>
    (⟨C.cB m, by simpa using (MVbar_code h hC m.2).1⟩ : ↥nm6.toFinset) with hf
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (C.cB_injective (congrArg Subtype.val hab))
  have hle : Nat.card ↥nm6.toFinset ≤ Nat.card ↥h.hyp.MVbar := by
    rw [Nat.card_eq_finsetCard, hc, ← nm6_length]
    exact List.toFinset_card_le _
  have hbij := hinj.bijective_of_nat_card_le hle
  intro B hB
  obtain ⟨m, hm⟩ := hbij.2 ⟨B, by simpa using hB⟩
  exact ⟨m, m.2, congrArg Subtype.val hm⟩

theorem exists_coding_T
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V)
    (hne : h.hyp.MVbar ≠ autOn L V) :
    ∃ C : Coding ↥V, Std C T L ∧ ∀ a ∈ autOn T V, C.cB a ∈ s0p := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  obtain ⟨τ, hτT, hτL⟩ := exists_T_not_L h1222 h hC.1 hne
  have hTM : autOn T V ≤ h.hyp.MVbar := A4.autOn_mono (T_le_MV h1222 h)
  have hτM := hTM hτT
  have hBτ := MVbar_code h hC.1 hτM
  have hτn : C.cB τ ∉ gm6 := fun hg => hτL ((hC.1.1 τ).2 hg)
  have hTL := autOn_T_inf_L h1222 h
  have hLN := MVbar_le_normalizer h
  have hnorm : ∀ s ∈ s0, ∃ s' ∈ s0, (C.cB τ).comp s = s'.comp (C.cB τ) := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := hC.s0_surj s hs
    have haT : a ∈ autOn T V := A4.autOn_mono inf_le_left ha
    have haL : a ∈ autOn L V := A4.autOn_mono inf_le_right ha
    have hmem : τ * a * τ⁻¹ ∈ autOn (T ⊓ L) V := by
      rw [← hTL]
      exact Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hτT haT)
        (Subgroup.inv_mem _ hτT), (Subgroup.mem_normalizer_iff.1 (hLN hτM) a).1 haL⟩
    refine ⟨C.cB (τ * a * τ⁻¹), (hC.2 _).1 hmem, ?_⟩
    rw [← C.cB_mul, ← C.cB_mul]
    congr 1
    group
  have h2 := two6_of_isPGroup_nm6 C (isPGroup_autOn_T h1222 h) hτT hBτ.1
  obtain ⟨k, hk, u, hu, hku⟩ := cert4_tau_norm _ hBτ.1 hτn hnorm h2
  obtain ⟨z, rfl⟩ := hC.1.2 _ (zs6_sub_gm6 _ hk)
  have hzL : z ∈ autOn L V := (hC.1.1 z).2 (zs6_sub_gm6 _ hk)
  have hzτ : C.cB (z * τ * z⁻¹) = u := by
    rw [C.cB_mul, C.cB_mul, hku, B6.comp_assoc, ← C.cB_mul, mul_inv_cancel, C.cB_one,
      B6.comp_id]
  have hzc : ∀ b ∈ autOn L V, z * b * z⁻¹ = b := fun b hb =>
    conj_scalar_eq C hk ((hC.1.1 b).1 hb)
  refine ⟨C.recode z, ⟨hC.1.recode hzL, fun a => ?_⟩, fun a ha => ?_⟩
  · rw [C.recode_cB]
    constructor
    · intro ha
      rw [hzc a (A4.autOn_mono inf_le_right ha)]
      exact (hC.2 a).1 ha
    · intro ha
      have hb := (hC.2 _).2 ha
      have hbL : z * a * z⁻¹ ∈ autOn L V := A4.autOn_mono inf_le_right hb
      have e : a = z⁻¹ * (z * a * z⁻¹) * z := by group
      have hzi : z⁻¹ * (z * a * z⁻¹) * z = z * a * z⁻¹ := by
        have := hzc _ hbL
        calc z⁻¹ * (z * a * z⁻¹) * z = z⁻¹ * (z * (z * a * z⁻¹) * z⁻¹) * z := by rw [this]
          _ = z * a * z⁻¹ := by group
      rw [e, hzi]
      exact hb
  · rw [C.recode_cB]
    by_cases haL : a ∈ autOn L V
    · rw [hzc a haL]
      exact s0_sub_s0p _ ((hC.2 a).1 (hTL ▸ Subgroup.mem_inf.2 ⟨ha, haL⟩))
    ·
      have haM := hTM ha
      have hτi : τ⁻¹ ∈ h.hyp.MVbar := h.hyp.MVbar.inv_mem hτM
      have hτiL : τ⁻¹ ∉ autOn L V := fun h' => hτL (by simpa using (autOn L V).inv_mem h')
      have hlin : IsLin (C.cB (a * τ⁻¹)) := by
        rw [C.cB_mul]
        exact isLin_comp_semi ((MVbar_code h hC.1 haM).2.2.2 haL)
          ((MVbar_code h hC.1 hτi).2.2.2 hτiL) (C.cB_valid _) (C.cB_valid _)
      have haτL := (MVbar_code h hC.1 (h.hyp.MVbar.mul_mem haM hτi)).2.2.1.2 hlin
      have haτT : a * τ⁻¹ ∈ autOn (T ⊓ L) V := by
        rw [← hTL]
        exact Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ ha (Subgroup.inv_mem _ hτT), haτL⟩
      have e : z * a * z⁻¹ = (z * (a * τ⁻¹) * z⁻¹) * (z * τ * z⁻¹) := by group
      rw [e, C.cB_mul, hzτ, hzc _ haτL]
      exact s0_comp_s0p _ ((hC.2 _).1 haτT) _ hu

theorem card_autOn_T_of_ne
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    (hne : h.hyp.MVbar ≠ autOn L V) : Nat.card ↥(autOn T V) = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := card_MVbar_of_ne h hC hne
  have hle : autOn T V ≤ h.hyp.MVbar := A4.autOn_mono (T_le_MV h1222 h)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_autOn_T h1222 h)
  have hi := ((autOn T V).subgroupOf h.hyp.MVbar).card_mul_index
  rw [show Nat.card ((autOn T V).subgroupOf h.hyp.MVbar) = Nat.card (autOn T V) from
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hk, hc] at hi
  have hodd := odd_index_T h1222 h
  rw [hk]
  have hk4 : k ≤ 4 := by
    by_contra hk4
    have : 2 ^ 5 ∣ 2160 := dvd_trans (pow_dvd_pow 2 (by omega)) ⟨_, hi.symm⟩
    norm_num at this
  interval_cases k <;> omega

theorem T_surj
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : Std C T L)
    (hne : h.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p) :
    ∀ s ∈ s0p, ∃ a ∈ autOn T V, C.cB a = s := by
  classical
  set f := fun m : ↥(autOn T V) => (⟨C.cB m, by simpa using hT m m.2⟩ : ↥s0p.toFinset) with hf
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (C.cB_injective (congrArg Subtype.val hab))
  have hle : Nat.card ↥s0p.toFinset ≤ Nat.card ↥(autOn T V) := by
    rw [Nat.card_eq_finsetCard, card_autOn_T_of_ne h1222 h hC.1 hne,
      List.toFinset_card_of_nodup s0p_nodup, s0p_length]
  have hbij := hinj.bijective_of_nat_card_le hle
  intro s hs
  obtain ⟨m, hm⟩ := hbij.2 ⟨s, by simpa using hs⟩
  exact ⟨m, m.2, congrArg Subtype.val hm⟩

end CFSG.Quasithin.H13.S127.Mod

end
