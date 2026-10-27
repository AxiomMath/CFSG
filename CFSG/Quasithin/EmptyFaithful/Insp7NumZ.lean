module

public import CFSG.LieType.Ree.FixedSubgroupData

import CFSG.LieType.Ree.LargeReeModelSchreier
import CFSG.LieType.Ree.LargeReeInvolutionCentralizersParabolic
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.EmptyFaithful.Insp7NumA
public import CFSG.Quasithin.EmptyFaithful.Insp7NumB

public section

namespace CFSG.Quasithin

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.LieType.Ree.LargeReeInvolution CFSG.Assembly.LowTwoRank

namespace Insp7

theorem fixedOrbitRoots_subset_complement (t : ReeTag) {j k : Fin t.fixedOrbitCount} (hjk : j ≠ k) :
    t.fixedOrbitRoots j ⊆ t.fixedOrbitComplementRoots k := by
  intro α hα
  obtain ⟨hroot, hpos, hsupp⟩ := mem_fixedOrbitRoots_iff.1 hα
  have hne : ∃ i, α i ≠ 0 := by
    by_contra h
    have hz : ∀ i, α i = 0 := fun i => by
      by_contra hne
      exact h ⟨i, hne⟩
    have h0 : height α = 0 := by simp [height, hz]
    omega
  obtain ⟨i, hi⟩ := hne
  have hij : t.fixedOrbitIndex i = j := by
    by_contra hj
    exact hi (hsupp i hj)
  exact mem_fixedOrbitComplementRoots_iff.2 ⟨hroot, hpos, i, by rw [hij]; exact hjk, hi⟩

theorem reeFixedOrbitUnipotent_le_complement
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    {j k : Fin F4.fixedOrbitCount} (hjk : j ≠ k) :
    F4.reeFixedOrbitUnipotent K a j ≤ F4.reeFixedOrbitComplementUnipotent K a k :=
  inf_le_inf_right _ (rootSpan_mono (fixedOrbitRoots_subset_complement F4 hjk))

theorem two_pow_nine_dvd_card_reeGamma
    {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) : 2 ^ 9 ∣ Nat.card (F4.reeGamma K a) := by
  have h1 := card_reeFixedPosUnipotent_eq_mul (K := K) (a := a) ⟨0, by decide⟩
  have h2 := card_reeFixedOrbitUnipotent_zero (K := K) (a := a) hK
  have h3 := card_reeFixedOrbitUnipotent_one (K := K) (a := a) hK
  have hle : Nat.card (F4.reeFixedOrbitUnipotent K a ⟨1, by decide⟩) ≤
      Nat.card (F4.reeFixedOrbitComplementUnipotent K a ⟨0, by decide⟩) :=
    Subgroup.card_le_of_le (reeFixedOrbitUnipotent_le_complement (by decide))
  rw [hK] at h2 h3
  have h4 : (2 ^ (2 * a + 1)) ^ 2 * 2 ^ (2 * a + 1) ≤ Nat.card (F4.reeFixedPosUnipotent K a) := by
    rw [h1, h2]
    exact Nat.mul_le_mul_right _ (h3 ▸ hle)
  have h5 : 2 ^ 9 ≤ (2 ^ (2 * a + 1)) ^ 2 * 2 ^ (2 * a + 1) := by
    rw [← pow_mul, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpg : IsPGroup 2 ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) :=
    isPGroup_reeFixedPosUnipotent_subgroupOf (t := F4) (K := K) (a := a)
  have hUΓ : F4.reeFixedPosUnipotent K a ≤ F4.reeGamma K a := inf_le_right
  have hcard : Nat.card ((F4.reeFixedPosUnipotent K a).subgroupOf (F4.reeGamma K a)) =
      Nat.card (F4.reeFixedPosUnipotent K a) := card_subgroupOf_reeGamma hUΓ
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hpg
  rw [hcard] at hm
  have hm9 : 9 ≤ m := by
    by_contra hlt
    have : 2 ^ m < 2 ^ 9 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have h6 : Nat.card (F4.reeFixedPosUnipotent K a) ∣ Nat.card (F4.reeGamma K a) :=
    Subgroup.card_dvd_of_le hUΓ
  exact (hm ▸ pow_dvd_pow 2 hm9).trans h6

theorem numFactAt_f4
    :
    NumFactAt (fun L _ => ∃ f : ℕ, Odd f ∧ 3 ≤ f ∧ ReeTitsModel L .twistedF4 2 f) := by
  refine numFactAt_of_big (fun L _ _ hq ⟨f, hodd, h3, hmodel⟩ => ?_)
  have hs := (CFSG.LieType.Simplicity.fam_2f4_simplicity L 2 f hmodel).2
  obtain ⟨-, -, -, -, -, hiso⟩ := large_Ree_model_Schreier L 2 f hmodel
  obtain ⟨hadm, a, hfa, hrel⟩ := hmodel
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hrel
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : CharP K F4.prime := hc
  have ha : 1 ≤ a := by
    obtain ⟨k, hk⟩ := hodd
    omega
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hfa]
  obtain ⟨e'⟩ := hiso a K hfa hK ⟨e⟩
  have hcard : Nat.card L = Nat.card (F4.reeGamma K a) := Nat.card_congr e'.toEquiv
  exact bigDvd_of_simple hq hs (hcard ▸ two_pow_nine_dvd_card_reeGamma ha hK')

end Insp7

end CFSG.Quasithin
