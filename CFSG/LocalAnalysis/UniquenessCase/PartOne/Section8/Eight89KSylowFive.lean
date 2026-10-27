module

public import Mathlib.GroupTheory.Sylow
public import Mathlib.Algebra.Module.LinearMap.End

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

private theorem k91syl_zpowers_eq_sylow {K : Type*} [Group K] [Finite K] (hK : ¬ 25 ∣ Nat.card K)
    {e : K} (he : orderOf e = 5) (P : Sylow 5 K) (hle : Subgroup.zpowers e ≤ (P : Subgroup K)) :
    Subgroup.zpowers e = P := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  have h5 : 5 ≤ Nat.card (P : Subgroup K) := by
    simpa [Nat.card_zpowers, he] using Subgroup.card_le_of_le hle
  have hdvd : Nat.card (P : Subgroup K) ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
  have hk1 : k = 1 := by
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · obtain rfl : k = 0 := by omega
      simp [hk] at h5
    · exact hK ((pow_dvd_pow 5 hgt : 5 ^ 2 ∣ 5 ^ k).trans (hk ▸ hdvd))
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, he, hk, hk1]; rfl)

private theorem k91syl_exists_sylow_eq {K : Type*} [Group K] [Finite K] (hK : ¬ 25 ∣ Nat.card K)
    {e : K} (he : orderOf e = 5) : ∃ P : Sylow 5 K, Subgroup.zpowers e = P := by
  have hp : IsPGroup 5 (Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by simp [Nat.card_zpowers, he])
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  exact ⟨P, k91syl_zpowers_eq_sylow hK he P hP⟩

private theorem k91syl_fix_of_mem_zpowers {K R W : Type*} [Group K] [Finite K] [CommRing R]
    [AddCommGroup W] [Module R W] (ρ : K →* Module.End R W) {e₀ x : K}
    (hx : x ∈ Subgroup.zpowers e₀) {w : W} (hfix : ρ e₀ w = w) : ρ x w = w := by
  obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hx)
  rw [map_pow, Module.End.pow_apply]
  exact Function.iterate_fixed hfix n

theorem exists_fixed_of_orderOf_eq_five {K R W : Type*} [Group K] [Finite K] [CommRing R]
    [AddCommGroup W] [Module R W] (hK : ¬ 25 ∣ Nat.card K) (ρ : K →* Module.End R W) {e₀ e : K}
    (he₀ : orderOf e₀ = 5) (he : orderOf e = 5) {w : W} (hw : w ≠ 0) (hfix : ρ e₀ w = w) :
    ∃ v : W, v ≠ 0 ∧ ρ e v = v := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨P₀, hP₀⟩ := k91syl_exists_sylow_eq hK he₀
  obtain ⟨P, hP⟩ := k91syl_exists_sylow_eq hK he
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P₀ P
  have hmem : e ∈ ((g • P₀ : Sylow 5 K) : Subgroup K) := by
    rw [hg, ← hP]
    exact Subgroup.mem_zpowers e
  rw [Sylow.coe_subgroup_smul] at hmem
  obtain ⟨s, hs, hse⟩ := (Subgroup.mem_smul_pointwise_iff_exists _ _ _).mp hmem
  rw [← hP₀] at hs
  rw [MulAut.smul_def, MulAut.conj_apply] at hse
  have hgi : ρ g⁻¹ (ρ g w) = w := by
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  refine ⟨ρ g w, fun h0 => hw ?_, ?_⟩
  · rw [← hgi, h0, map_zero]
  · rw [← hse, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hgi,
      k91syl_fix_of_mem_zpowers ρ hs hfix]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs
