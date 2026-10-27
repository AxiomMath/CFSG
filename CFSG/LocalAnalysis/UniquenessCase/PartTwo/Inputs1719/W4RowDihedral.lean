module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsDefs
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Engine
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup.X1

private theorem le_rk_of_two_mul_le_orderOf_two {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {L : Subgroup (MulAut W)} {S : Type} [Group S]
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) {p ρ : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpS : p ∣ Nat.card S) (hρ : 2 * ρ ≤ orderOf (2 : ZMod p)) :
    ρ ≤ rk W := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  have hcard : Nat.card W = 2 ^ rk W :=
    card_eq_two_pow_of_isPGroup (isPGroup_two_of_sq_eq_one hW)
  have hle := two_pow_le_card_of_dvd hW' e hp2 hpS
  rw [hcard] at hle
  have hord : orderOf (2 : ZMod p) ≤ rk W :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 hle
  omega

private theorem le_rkIdx_fixV_of_dihedral {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)} (hO2 : O2Trivial L)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) {p ρ : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hρ : 2 * ρ ≤ orderOf (2 : ZMod p))
    (hgen : ∀ t : S, t * t = 1 → t ≠ 1 → ∃ c : S, orderOf (t * (c * t * c⁻¹)) = p)
    {t : MulAut W} (htL : t ∈ L) (hto : orderOf t = 2) :
    ρ ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hto
    norm_num at hto
  have hT2 : e (QuotientGroup.mk ⟨t, htL⟩) * e (QuotientGroup.mk ⟨t, htL⟩) = 1 := by
    rw [← map_mul, ← QuotientGroup.mk_mul, ← map_one e, ← QuotientGroup.mk_one]
    congr 2
    exact Subtype.ext ht2
  have hT1 : e (QuotientGroup.mk ⟨t, htL⟩) ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk (⟨t, htL⟩ : ↥L) : ↥L ⧸ Subgroup.center ↥L) = 1 :=
      e.injective (by rw [h, map_one])
    rw [QuotientGroup.eq_one_iff] at h1
    have hzpow : (Subgroup.zpowers t).subgroupOf L = Subgroup.zpowers (⟨t, htL⟩ : ↥L) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
      constructor
      · rintro ⟨k, hk⟩
        exact ⟨k, Subtype.ext hk⟩
      · rintro ⟨k, hk⟩
        exact ⟨k, congrArg Subtype.val hk⟩
    have hP2 : IsPGroup 2 (Subgroup.zpowers t) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hto]; norm_num)
    have hPbot := hO2 (Subgroup.zpowers t) (Subgroup.zpowers_le.2 htL) (by
      rw [hzpow]
      exact Subgroup.normal_of_le_center (Subgroup.zpowers_le.2 h1)) hP2
    have hmem : t ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hPbot]
      exact Subgroup.mem_zpowers t
    exact ht1 (Subgroup.mem_bot.1 hmem)
  obtain ⟨c, hc⟩ := hgen _ hT2 hT1
  have hkey := two_pow_le_index_sq_of_dihedral hW e htL hp2 c hc
  obtain ⟨m, hm⟩ := index_fixV_eq_two_pow hW (Subgroup.zpowers t)
  rw [hm, ← pow_mul] at hkey
  have hmle : orderOf (2 : ZMod p) ≤ m * 2 :=
    (Nat.pow_le_pow_iff_right (by norm_num)).1 hkey
  have hρm : ρ ≤ m := by omega
  rwa [rkIdx, hm, padicValNat.prime_pow]

theorem le_mParam_of_dihedral {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {Y L : Subgroup (MulAut W)} (hO2 : O2Trivial L) (hYL : ∀ t ∈ Y, orderOf t = 2 → t ∈ L)
    {S : Type} [Group S] (e : (↥L ⧸ Subgroup.center ↥L) ≃* S) {p ρ : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hpS : p ∣ Nat.card S) (hρ : 2 * ρ ≤ orderOf (2 : ZMod p))
    (hgen : ∀ t : S, t * t = 1 → t ≠ 1 → ∃ c : S, orderOf (t * (c * t * c⁻¹)) = p) :
    ρ ≤ E3.mParam Y := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  unfold E3.mParam
  by_cases hEven : Even (Nat.card Y)
  · rw [if_pos hEven]
    refine le_csInf ?_ ?_
    · obtain ⟨t, hto⟩ :=
        exists_prime_orderOf_dvd_card' (G := ↥Y) 2 (even_iff_two_dvd.1 hEven)
      exact ⟨_, (t : MulAut W), t.2, by rwa [Subgroup.orderOf_coe], rfl⟩
    · rintro n ⟨t, htY, hto, rfl⟩
      exact le_rkIdx_fixV_of_dihedral hW' hO2 e hp2 hρ hgen (hYL t htY hto) hto
  · rw [if_neg hEven]
    exact le_rk_of_two_mul_le_orderOf_two hW e hp2 hpS hρ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
