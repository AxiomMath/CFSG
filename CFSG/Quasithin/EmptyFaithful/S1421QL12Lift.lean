module

public import CFSG.Quasithin.EmptyFaithful.S1421QL12Bender

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

theorem exists_odd_lift {X X' : Type*} [Group X] [Group X'] (π : X →* X')
    (hker : IsPGroup 2 ↥π.ker) (hπ : Function.Surjective π) {d : X'} (hd : Odd (orderOf d)) :
    ∃ e : X, π e = d ∧ Odd (orderOf e) := by
  obtain ⟨e, rfl⟩ := hπ d
  set m := orderOf (π e) with hm
  have hz : e ^ m ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, pow_orderOf_eq_one]
  obtain ⟨a, ha⟩ := hker ⟨e ^ m, hz⟩
  have ha' : (e ^ m) ^ 2 ^ a = 1 := congrArg Subtype.val ha
  have hcop : Nat.Coprime (2 ^ a) m := Nat.Coprime.pow_left a (Nat.coprime_two_left.2 hd)
  obtain ⟨j, hj0, hj1⟩ := Nat.chineseRemainder hcop 0 1
  obtain ⟨j', rfl⟩ : 2 ^ a ∣ j := (Nat.modEq_zero_iff_dvd).mp hj0
  refine ⟨e ^ (2 ^ a * j'), ?_, ?_⟩
  · rw [map_pow, ← pow_mod_orderOf (π e) (2 ^ a * j'), hj1, pow_mod_orderOf, pow_one]
  · have h1 : (e ^ (2 ^ a * j')) ^ m = 1 := by
      have : (e ^ (2 ^ a * j')) ^ m = ((e ^ m) ^ 2 ^ a) ^ j' := by
        rw [← pow_mul, ← pow_mul, ← pow_mul]
        congr 1
        ring
      rw [this, ha', one_pow]
    exact Odd.of_dvd_nat hd (orderOf_dvd_of_pow_eq_one h1)

theorem exists_odd_borel_not_mem_solvRad {G : Type} [Group G]
    [Finite G] {T K1 : Subgroup G} (hS : IsSylowTwoOf (T ⊓ K1) K1)
    (hB : ∃ n : ℕ, 2 ≤ n ∧ IsBenderQuot n (OTwoQuot K1)) :
    ∃ b ∈ K1 ⊓ Subgroup.normalizer ((T ⊓ K1 : Subgroup G) : Set G),
      Odd (orderOf b) ∧ b ∉ solvRad K1 := by
  obtain ⟨n, hn, hX⟩ := hB
  set S1 : Subgroup ↥K1 := (T ⊓ K1).subgroupOf K1 with hS1
  set π : ↥K1 →* OTwoQuot K1 := QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K1) with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hS1p : IsPGroup 2 S1 := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  have hker : π.ker ≤ S1 := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 K1 := (F1.mem_pCore_iff_coe x).mp hx
    exact Subgroup.mem_subgroupOf.mpr (isSylowTwoOf_pCoreOf_le hS h1)
  have hker2 : IsPGroup 2 ↥π.ker := hS1p.to_le hker
  have hPp : IsPGroup 2 (S1.map π) := hS1p.map π
  have hPodd : ¬ 2 ∣ (S1.map π).index := by
    rw [Subgroup.index_map_eq (f := π) (H := S1) hsurj hker]
    exact hS.2.2
  obtain ⟨d, hdN, hdodd, hdsolv⟩ := IsBenderQuot.exists_oddOffSolvable hn hX hPp hPodd
  obtain ⟨d0, hd0, hd0odd⟩ := exists_odd_lift π hker2 hsurj hdodd
  have hmem : ∀ u : ↥K1, π u ∈ S1.map π ↔ u ∈ S1 := by
    intro u
    constructor
    · rintro ⟨t, ht, hπt⟩
      have hk : t⁻¹ * u ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπt, inv_mul_cancel]
      have := S1.mul_mem ht (hker hk)
      simpa using this
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hd0N : d0 ∈ Subgroup.normalizer (S1 : Set ↥K1) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [← hmem, ← hmem, map_mul, map_mul, map_inv, hd0]
    exact Subgroup.mem_normalizer_iff.mp hdN (π y)
  have hbor : (d0 : G) ∈ borelOf K1 T := by
    have h1 := F1.normalizer_subgroupOf_eq (Li := K1) (S := T)
    rw [← hS1] at h1
    rw [h1] at hd0N
    exact Subgroup.mem_subgroupOf.mp hd0N
  refine ⟨(d0 : G), hbor, ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hd0odd
  · intro hsr
    have hsolv := solvRad_isSolvable K1
    have hRn : ((solvRad K1).subgroupOf K1).Normal := solvRad_normal K1
    have hRs : Group.IsSolvable ↥((solvRad K1).subgroupOf K1) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (solvRad_le K1)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (solvRad_le K1)).injective
    refine hdsolv (((solvRad K1).subgroupOf K1).map π) (hRn.map π hsurj) ?_ ?_
    · rw [← hd0]
      exact Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hsr)
    · exact Group.isSolvable_of_surjective (MonoidHom.subgroupMap_surjective π _)

end CFSG.Quasithin
