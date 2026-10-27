module

public import CFSG.Quasithin.H13.L32AC50h
public import CFSG.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} [IsMulCommutative ↥V]

theorem mem_pCoreOf_of_triv (S14 : L32NSet14.Setting G T L V V₂) {x : G}
    (hxL : x ∈ L₁Of L (fsuV1 T V))
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) {k : G}
    (hkL : k ∈ L₁Of L (fsuV1 T V)) (hkt : k ∈ L32NSet14.trivSub V (fsuV1 T V)) :
    k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hkO
  have : ((pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 _)).mpr
      (le_normalizer_pCoreOf 2 _)
  have h3 : Nat.card (↥(L₁Of L (fsuV1 T V)) ⧸
      (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) = 3 := by
    rw [← Subgroup.index_eq_card]
    exact S14.Lp3
  have hk1 : (QuotientGroup.mk ⟨k, hkL⟩ : ↥(L₁Of L (fsuV1 T V)) ⧸
      (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) ≠ 1 := fun h =>
    hkO (Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff
      (N := (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) ⟨k, hkL⟩).mp h))
  have htop := zpowers_eq_top_of_prime_card h3 hk1
  have hxm : (QuotientGroup.mk ⟨x, hxL⟩ : ↥(L₁Of L (fsuV1 T V)) ⧸
      (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) ∈
      Subgroup.zpowers (QuotientGroup.mk ⟨k, hkL⟩ : ↥(L₁Of L (fsuV1 T V)) ⧸
        (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V))) := by
    rw [htop]; exact Subgroup.mem_top _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hxm
  have ho : (⟨k, hkL⟩ ^ j : ↥(L₁Of L (fsuV1 T V)))⁻¹ * ⟨x, hxL⟩ ∈
      (pCoreOf 2 (L₁Of L (fsuV1 T V))).subgroupOf (L₁Of L (fsuV1 T V)) := by
    rw [← QuotientGroup.eq, QuotientGroup.mk_zpow, hj]
  have hoP : (k ^ j)⁻¹ * x ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
    have := Subgroup.mem_subgroupOf.mp ho
    simpa using this
  have hxt : x ∈ L32NSet14.trivSub V (fsuV1 T V) := by
    have e : x = k ^ j * ((k ^ j)⁻¹ * x) := by group
    rw [e]
    exact mul_mem (zpow_mem hkt j) (S14.pCoreOf_L1_le hoP)
  have hle : V ≤ fsuV1 T V := fun v hv =>
    hfpf v hv ((L32NSet14.mem_trivSub.mp hxt).2.2 v hv)
  have := Subgroup.card_le_of_le hle
  rw [S14.card_V, S14.card_V1] at this
  omega

theorem inv_mem_pCoreOf (S14 : L32NSet14.Setting G T L V V₂) {x : G}
    (hxL : x ∈ L₁Of L (fsuV1 T V))
    (hfpf : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ fsuV1 T V → v ∈ fsuV1 T V) {t : G} (htT : t ∈ T)
    (htn : t ∉ L32NSet14.trivSub V (fsuV1 T V)) {y : G} (hyL : y ∈ L₁Of L (fsuV1 T V))
    (hy3 : y ^ 3 = 1) : t * y * t⁻¹ * y ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)) := by
  obtain ⟨ρ, hρ⟩ := S14.exists_rep
  have hyX := S14.L1_le_X hyL
  have htX := S14.T_le_X htT
  have hcX : t * y * t⁻¹ * y ∈ L32NSet14.nX T V :=
    mul_mem (mul_mem (mul_mem htX hyX) (inv_mem htX)) hyX
  have ht1 : ρ ⟨t, htX⟩ ≠ 1 := fun h => htn ((hρ ⟨t, htX⟩).mp h)
  have ht2 : ρ ⟨t, htX⟩ ^ 2 = 1 := by
    obtain ⟨k, hk⟩ := S14.hH.sylow.1 ⟨t, htT⟩
    refine L32NSet14.sl2_sq_of_two (k := k) ?_
    rw [← map_pow]
    have : (⟨t, htX⟩ : ↥(L32NSet14.nX T V)) ^ 2 ^ k = 1 :=
      Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have hy3' : ρ ⟨y, hyX⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, hyX⟩ : ↥(L32NSet14.nX T V)) ^ 3 = 1 := Subtype.ext (by simpa using hy3)
    rw [this, map_one]
  have hc1 : ρ ⟨_, hcX⟩ = 1 := by
    have e : (⟨t * y * t⁻¹ * y, hcX⟩ : ↥(L32NSet14.nX T V)) =
        ⟨t, htX⟩ * ⟨y, hyX⟩ * ⟨t, htX⟩⁻¹ * ⟨y, hyX⟩ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv]
    exact sl2_facts.2 _ _ ht2 hy3' ht1
  have hcL : t * y * t⁻¹ * y ∈ L₁Of L (fsuV1 T V) := by
    have h1 : t * y * t⁻¹ ∈ L₁Of L (fsuV1 T V) :=
      (Subgroup.mem_normalizer_iff.mp (S14.T_Lp htT) y).mp hyL
    exact mul_mem h1 hyL
  exact mem_pCoreOf_of_triv S14 hxL hfpf hcL ((hρ _).mp hc1)

theorem l1_le_of_cube (S14 : L32NSet14.Setting G T L V V₂) {C : Subgroup G}
    (hC : ∀ y ∈ L₁Of L (fsuV1 T V), y ^ 3 = 1 → y ∈ C) : L₁Of L (fsuV1 T V) ≤ C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard : Nat.card ↥(L₁Of L (fsuV1 T V)) =
      3 * Nat.card ↥(pCoreOf 2 (L₁Of L (fsuV1 T V))) := by
    have h := Subgroup.relIndex_mul_card (pCoreOf 2 (L₁Of L (fsuV1 T V))) (L₁Of L (fsuV1 T V))
    rw [S14.Lp3, inf_eq_left.mpr (pCoreOf_le 2 _)] at h
    exact h.symm
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V))).exists_card_eq
  have hL : L₁Of L (fsuV1 T V) = oTwoUpper (L ⊓ Subgroup.normalizer (fsuV1 T V : Set G)) :=
    oTwoRes_eq_oTwoUpper _
  have hgen : L₁Of L (fsuV1 T V) ≤ C := by
    rw [hL]
    refine (Subgroup.closure_le C).mpr fun g hg => ?_
    have hgL : g ∈ L₁Of L (fsuV1 T V) := by
      rw [hL]
      exact Subgroup.subset_closure hg
    refine hC g hgL ?_
    have h1 : orderOf g ∣ 3 * 2 ^ a := by
      rw [← ha, ← hcard]
      have := orderOf_dvd_natCard (⟨g, hgL⟩ : ↥(L₁Of L (fsuV1 T V)))
      rwa [Subgroup.orderOf_mk] at this
    have hcop : Nat.Coprime (orderOf g) (2 ^ a) :=
      Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hg.2)
    have h2 : orderOf g ∣ 3 := hcop.dvd_of_dvd_mul_right h1
    exact orderOf_dvd_iff_pow_eq_one.mp h2
  exact hgen

end CFSG.Quasithin.H13.L32A.C
