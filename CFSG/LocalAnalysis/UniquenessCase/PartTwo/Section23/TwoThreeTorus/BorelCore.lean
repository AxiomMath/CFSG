module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsFiveK
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsTwoThree
import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3Natural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem not_le_stabSub_fixV {U : Type} [CommGroup U] {H S : Subgroup (MulAut U)}
    (hsimp : IsSimpleGroup ↥H) (hSH : S ≤ H) (hSne : S ≠ ⊥) (hfix : fixV H = ⊥)
    (hSfix : fixV S ≠ ⊥) : ¬ H ≤ stabSub (fixV S) := by
  intro hst
  let ℓ : Subgroup U := fixV S
  let F : Subgroup ↥H := (H ⊓ centSub ℓ).subgroupOf H
  have hFnormal : F.Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro h k hh hk
    have hh' : ∀ u ∈ ℓ, h u = u := mem_centSub.mp hh.2
    refine ⟨H.mul_mem (H.mul_mem hk hh.1) (H.inv_mem hk), ?_⟩
    exact mem_centSub.mpr fun w hw => by
      have hkw : (k : MulAut U)⁻¹ w ∈ ℓ := by
        have hkst := mem_stabSub.mp (hst hk) ((k : MulAut U)⁻¹ w)
        exact hkst.mp (by simpa using hw)
      have h1 : h ((k : MulAut U)⁻¹ w) = (k : MulAut U)⁻¹ w := hh' _ hkw
      show (k : MulAut U) (h ((k : MulAut U)⁻¹ w)) = w
      rw [h1, MulAut.apply_inv_self]
  have hSF : S.subgroupOf H ≤ F := by
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    refine ⟨hSH hx, ?_⟩
    exact mem_centSub.mpr fun w hw => (mem_fixV.mp hw) x.1 hx
  have hFne : F ≠ ⊥ := by
    intro hFbot
    apply hSne
    have h1 : S.subgroupOf H = ⊥ := le_bot_iff.mp (hFbot ▸ hSF)
    have h2 := Subgroup.map_subgroupOf_eq_of_le hSH
    rw [h1, Subgroup.map_bot] at h2
    exact h2.symm
  haveI : F.Normal := hFnormal
  rcases Subgroup.Normal.eq_bot_or_eq_top F with hb | ht
  · exact hFne hb
  · have hle : ℓ ≤ fixV H := by
      intro w hw
      rw [mem_fixV]
      intro h hh
      have hmem : (⟨h, hh⟩ : ↥H) ∈ F := by
        rw [ht]
        exact Subgroup.mem_top _
      have hcent : h ∈ centSub ℓ := (Subgroup.mem_subgroupOf.mp hmem).2
      exact (mem_centSub.mp hcent) w hw
    have hbot : ℓ = ⊥ := by
      rw [hfix] at hle
      exact le_bot_iff.mp hle
    exact hSfix hbot

theorem exists_mem_normalizer_apply_ne (hBI : KNatBorelIrr) (hTa : KTab23a)
    {U : Type} [CommGroup U] [Finite U] {H S : Subgroup (MulAut U)} {k : ℕ}
    (hnat : IsNaturalClassicalModule H k) (hperf : ⁅H, H⁆ = H) (hsimp : IsSimpleGroup ↥H)
    (hS : IsSylowIn 2 S H) (hSne : S ≠ ⊥) (hfix : fixV H = ⊥) (hk : 2 ≤ k)
    {v : U} (hv : v ∈ fixV S) (hv1 : v ≠ 1) (hv2 : v ^ 2 = 1) :
    ∃ b ∈ H ⊓ normalizer (S : Set (MulAut U)), b v ≠ v := by
  by_contra hcon
  push Not at hcon
  have hSfix : fixV S ≠ ⊥ := by
    intro hbot
    have : v ∈ (⊥ : Subgroup U) := hbot ▸ hv
    exact hv1 (Subgroup.mem_bot.mp this)
  have hnot : ¬ H ≤ stabSub (fixV S) :=
    not_le_stabSub_fixV hsimp hS.le hSne hfix hSfix
  have hJle : Subgroup.zpowers v ≤ fixV S := Subgroup.zpowers_le.mpr hv
  have hJst : StableUnder (Hinf H ⊓ normalizer (S : Set (MulAut U))) (Subgroup.zpowers v) := by
    intro x hx u hu
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hu
    have hxH : x ∈ H ⊓ normalizer (S : Set (MulAut U)) :=
      ⟨uc22p21c_Hinf_le H hx.1, hx.2⟩
    rw [← hm, map_zpow, hcon x hxH]
    exact Subgroup.zpow_mem_zpowers v m
  have hJcase :=
    hBI U H S H k hnat hperf hS inf_le_left le_rfl hnot (Subgroup.zpowers v) hJle hJst
  have hJne : Subgroup.zpowers v ≠ ⊥ := by
    intro hbot
    have : v ∈ (⊥ : Subgroup U) := hbot ▸ Subgroup.mem_zpowers v
    exact hv1 (Subgroup.mem_bot.mp this)
  have hJfix : Subgroup.zpowers v = fixV S := hJcase.resolve_left hJne
  have hcardJ : Nat.card (Subgroup.zpowers v) ≤ 2 := by
    rw [Nat.card_zpowers]
    exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hv2)
  have hcard : Nat.card (fixV S) = 2 ^ k := by
    have h := (hTa U H k hnat hperf hS.toSylow).1
    rw [fixedPointSubgroup_sylow_map (V := U) hS.toSylow] at h
    rw [hS.coe_toSylow, Subgroup.map_subgroupOf_eq_of_le hS.le] at h
    rwa [fixedPointSubgroup_eq_fixV S] at h
  have hle2 : 2 ^ k ≤ 2 := by
    rw [← hcard, ← hJfix]
    exact hcardJ
  have h4 : 4 ≤ 2 ^ k := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ)) hk
  omega

end CFSG.LocalAnalysis.UniquenessCase.UC22.TwoConj
