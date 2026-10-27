module

public import CFSG.Quasithin.Vol2.F134LieF4Group

public section

namespace CFSG.Quasithin.S146zY.TwoF4

open CFSG.ABGLocalTools CFSG.LieType.BorelTits CFSG.Quasithin.F134.LieF4

theorem exists_proper_overgroup_of_not_dvd {Y : Type*} [Group Y] [Finite Y] (hBT : Holds Y 2)
    {U H : Subgroup Y} (hU : IsSylowOf 2 U ⊤) (hUH : U ≤ H)
    (hcard : ¬ Nat.card H ∣ (U.subgroupOf H).index.factorial) :
    ∃ Q : Subgroup Y, Q ≠ ⊤ ∧ H ≤ Q ∧ Subgroup.normalizer (U : Set Y) ≤ Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := (U.subgroupOf H).normalCore with hC
  have hCne : C ≠ ⊥ := by
    intro hbot
    have h := (U.subgroupOf H).index_normalCore_dvd_factorial_index
    rw [← hC, hbot, Subgroup.index_bot] at h
    exact hcard h
  set V := C.map H.subtype with hV
  have hVU : V ≤ U := by
    rintro _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (Subgroup.normalCore_le _ hc)
  have hVne : V ≠ ⊥ := by
    intro h
    apply hCne
    rwa [hV, Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at h
  have hVsub : V.subgroupOf H = C := by
    rw [hV, Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hHV : H ≤ Subgroup.normalizer (V : Set Y) := by
    have hn : (V.subgroupOf H).Normal := by
      rw [hVsub]
      exact Subgroup.normalCore_normal _
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le C)).1 hn
  obtain ⟨S, Q, hQ, hNQ, -, -, hSQ⟩ := hBT V hVne (hU.isPGroup.to_le hVU)
  have hHQ : H ≤ Q := hHV.trans hNQ
  exact ⟨Q, hQ, hHQ, normalizer_le_of_isSylowOf
    (isSylowOf_of_sylow S (Subgroup.le_normalizer.trans hSQ))
    (hU.of_le (hUH.trans hHQ) le_top) hSQ⟩

theorem not_dvd_twentyFive_mul_pow_twelve {n : ℕ} (hn : 3 ≤ n) :
    ¬ 25 * (2 ^ n) ^ 12 ∣ Nat.factorial 25 := by
  intro h
  have h36 : 2 ^ 36 ∣ 25 * (2 ^ n) ^ 12 := by
    refine Dvd.dvd.mul_left ?_ 25
    rw [← pow_mul]
    exact pow_dvd_pow 2 (by omega)
  exact (by decide : ¬ 2 ^ 36 ∣ Nat.factorial 25) (h36.trans h)

end CFSG.Quasithin.S146zY.TwoF4
