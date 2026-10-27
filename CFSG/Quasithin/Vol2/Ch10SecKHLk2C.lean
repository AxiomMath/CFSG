module

public import CFSG.Quasithin.Vol2.Ch10SecKHLk2B
public import CFSG.LocalAnalysis.QuasithinUnique.Defs

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.C10KH

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type*} [Group G]

theorem exists_pow_mul_eq' {X : Subgroup G} {x u : G} (hx : x ∈ X)
    (hu : u ∈ Subgroup.normalizer (X : Set G)) (m : ℕ) : ∃ x' ∈ X, (x * u) ^ m = x' * u ^ m := by
  induction m with
  | zero => exact ⟨1, X.one_mem, by simp⟩
  | succ m ih =>
    obtain ⟨x', hx', h⟩ := ih
    have hconj : u ^ m * x * (u ^ m)⁻¹ ∈ X :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hu m) x).mp hx
    refine ⟨x' * (u ^ m * x * (u ^ m)⁻¹), X.mul_mem hx' hconj, ?_⟩
    rw [pow_succ, h, pow_succ]
    group

theorem mem_of_orderOf_eq_three {X U : Subgroup G} (hU : IsPGroup 2 U)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) {k : G} (hk : k ∈ X ⊔ U) (h3 : orderOf k = 3) :
    k ∈ X := by
  have hk' : k ∈ ((X ⊔ U : Subgroup G) : Set G) := hk
  rw [Subgroup.coe_mul_of_right_le_normalizer_left X U hUX] at hk'
  obtain ⟨x, hx, u, hu, hxu⟩ := hk'
  have hxu' : k = x * u := hxu.symm
  subst hxu'
  obtain ⟨a, ha⟩ := hU ⟨u, hu⟩
  have ha' : u ^ 2 ^ a = 1 := congrArg Subtype.val ha
  obtain ⟨x', hx', hpow⟩ := exists_pow_mul_eq' hx (hUX hu) (2 ^ a)
  rw [ha', mul_one] at hpow
  have hk3 : (x * u) ^ 3 = 1 := by rw [← h3]; exact pow_orderOf_eq_one _
  have hmod : (x * u) ^ 2 ^ a = (x * u) ^ (2 ^ a % 3) := by
    conv_lhs => rw [← Nat.div_add_mod (2 ^ a) 3, pow_add, pow_mul, hk3, one_pow, one_mul]
  have hX : (x * u) ^ (2 ^ a % 3) ∈ X := by rw [← hmod, hpow]; exact hx'
  have h3a : 2 ^ a % 3 ≠ 0 := by
    intro h0
    have h3d : 3 ∣ 2 ^ a := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h3d)
    omega
  have hlt : 2 ^ a % 3 < 3 := Nat.mod_lt _ (by norm_num)
  rcases (by omega : 2 ^ a % 3 = 1 ∨ 2 ^ a % 3 = 2) with h1 | h2
  · rw [h1, pow_one] at hX
    exact hX
  · rw [h2] at hX
    have he : x * u = ((x * u) ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hk3, one_mul, pow_one]
    rw [he]
    exact X.pow_mem hX 2

omit [Group G] in
theorem pCoreOf_subgroupOf_map' {G : Type*} [Group G] {K Y : Subgroup G} (hYK : Y ≤ K) :
    (pCoreOf 2 (Y.subgroupOf K)).map K.subtype = pCoreOf 2 Y := by
  have h := map_pCore_mulEquiv 2 (Subgroup.subgroupOfEquivOfLe hYK)
  unfold pCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl

theorem mem_sup_of_conj_le_of_le [Finite G] {K U X : Subgroup G} {n : ℕ} (hn : n = 4 ∨ n = 5)
    {θ : ↥K →* Matrix.SpecialLinearGroup (Fin n) (ZMod 2)} (hθ : Function.Surjective θ)
    (hker : IsPGroup 2 θ.ker) (hU : IsSylowTwoOf U K) (hXK : X ≤ K)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (h9 : (pCoreOf 2 X).relIndex X = 9) {k : G}
    (hkK : k ∈ K) (hk : ∀ w ∈ pCoreOf 2 (X ⊔ U), k * w * k⁻¹ ∈ U) : k ∈ X ⊔ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U₀ : Sylow 2 ↥K :=
    (hU.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hU.1).symm).toSylow hU.2.2 with hU₀def
  have hU₀ : (U₀ : Subgroup ↥K) = U.subgroupOf K := rfl
  have hJK : X ⊔ U ≤ K := sup_le hXK hU.1
  have hsub : (X ⊔ U).subgroupOf K = X.subgroupOf K ⊔ U.subgroupOf K :=
    Subgroup.subgroupOf_sup hXK hU.1
  have hW : ∀ w : ↥K, w ∈ pCoreOf 2 (X.subgroupOf K ⊔ (U₀ : Subgroup ↥K)) ↔
      (w : G) ∈ pCoreOf 2 (X ⊔ U) := by
    intro w
    rw [hU₀, ← hsub, ← pCoreOf_subgroupOf_map' hJK]
    exact (Subgroup.mem_map_iff_mem K.subtype_injective).symm
  have hUX₀ : (U₀ : Subgroup ↥K) ≤ Subgroup.normalizer (X.subgroupOf K : Set ↥K) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have h := Subgroup.mem_normalizer_iff.1 (hUX hu) y
    simpa [Subgroup.mem_subgroupOf] using h
  have h9₀ : (pCoreOf 2 (X.subgroupOf K)).relIndex (X.subgroupOf K) = 9 := by
    rw [← Subgroup.relIndex_map_map_of_injective _ _ K.subtype_injective,
      pCoreOf_subgroupOf_map' hXK, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hXK, h9]
  have hk₀ := mem_sup_of_conj_le hn hθ hker U₀ hUX₀ h9₀ (k := ⟨k, hkK⟩) fun w hw => by
    rw [hU₀, Subgroup.mem_subgroupOf]
    simpa using hk w ((hW w).1 hw)
  have hmem : (⟨k, hkK⟩ : ↥K) ∈ (X ⊔ U).subgroupOf K := by
    rw [hsub]
    exact hk₀
  exact hmem

theorem pCoreOf_le_of_isSylowTwoOf' [Finite G] {K U Y : Subgroup G} (hU : IsSylowTwoOf U K)
    (hYK : Y ≤ K) (hUY : U ≤ Subgroup.normalizer (Y : Set G)) : pCoreOf 2 Y ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : U ≤ Subgroup.normalizer (pCoreOf 2 Y : Set G) :=
    hUY.trans (normalizer_le_normalizer_pCoreOf 2 Y)
  have hV : IsPGroup 2 (U ⊔ pCoreOf 2 Y : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hU.2.1 (pCoreOf_isPGroup 2 Y) hN
  have hVK : U ⊔ pCoreOf 2 Y ≤ K := sup_le hU.1 ((pCoreOf_le 2 Y).trans hYK)
  have hmul := Subgroup.relIndex_mul_relIndex U (U ⊔ pCoreOf 2 Y) K le_sup_left hVK
  have hodd : ¬ 2 ∣ U.relIndex (U ⊔ pCoreOf 2 Y) := fun h => by
    have h' : 2 ∣ U.relIndex K := hmul ▸ Dvd.dvd.mul_right h _
    exact hU.2.2 h'
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hV
  have hdvd : U.relIndex (U ⊔ pCoreOf 2 Y) ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hj0 : j = 0 := by
    by_contra h
    exact hodd (hj ▸ dvd_pow_self 2 h)
  rw [hj0, pow_zero, Subgroup.relIndex_eq_one] at hj
  exact le_sup_right.trans hj

end CFSG.Quasithin.Vol2.Ch10.SecB.C10KH
