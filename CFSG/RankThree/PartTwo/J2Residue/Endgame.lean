module

public import CFSG.RankThree.PartTwo.J2Residue.ConfigFacts
import CFSG.RankThree.PartTwo.J2Residue.LinAlg

public section

namespace CFSG.RankThree.PartTwo.J2Residue

open CFSG

theorem isPGroup_zpowers_of_mul_self {Γ : Type*} [Group Γ] {t : Γ} (ht : t * t = 1) :
    IsPGroup 2 (Subgroup.zpowers t) := by
  have hdvd : orderOf t ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact ht)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])

theorem natCast_ne_zero_of_lt {r n : ℕ} (hn0 : 0 < n) (hn : n < r) : (n : ZMod r) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  exact absurd (Nat.le_of_dvd hn0 h) (by omega)

theorem finrank_le_two_mul_of_neg_one {K : Type*} [Field K] (h2 : (2 : K) ≠ 0) {Γ : Type*}
    [Group Γ] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (ρ : Representation K Γ V) {k : ℕ}
    (hk : ∀ t : Γ, t * t = 1 → t ≠ 1 → Module.finrank K (LinearMap.ker (ρ t - 1)) ≤ k)
    {x z : Γ} (hz : ρ z = -1) (hz2 : z * z = 1) (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxz : x ≠ z)
    (hc : x * z = z * x) : Module.finrank K V ≤ 2 * k := by
  have hρx : ρ x * ρ x = 1 := by rw [← map_mul, hx2, map_one]
  have hsplit := finrank_eq_add_of_eq_neg_one h2 hρx hz
  have hxz2 : (x * z) * (x * z) = 1 := by
    calc (x * z) * (x * z) = x * (z * x) * z := by group
      _ = x * (x * z) * z := by rw [hc]
      _ = (x * x) * (z * z) := by group
      _ = 1 := by rw [hx2, hz2, one_mul]
  have hxz1 : x * z ≠ 1 := by
    intro h
    apply hxz
    rw [eq_inv_of_mul_eq_one_left h, inv_eq_of_mul_eq_one_right hz2]
  have h1 := hk x hx2 hx1
  have h3 := hk (x * z) hxz2 hxz1
  rw [map_mul] at h3
  omega

variable {G : Type} [Group G]

theorem isPerfect_subgroupOf {H Y : Subgroup G} (hH : Group.IsPerfect H) (hHY : H ≤ Y) :
    Group.IsPerfect (H.subgroupOf Y) := by
  haveI := hH
  exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hHY).symm.toMonoidHom)
    (MulEquiv.surjective _)

theorem subgroupOf_ne_bot {H Y : Subgroup G} (hH : H ≠ ⊥) (hHY : H ≤ Y) :
    H.subgroupOf Y ≠ ⊥ := by
  obtain ⟨h, hh, h1⟩ := (Subgroup.bot_or_exists_ne_one H).resolve_left hH
  intro hbot
  have hmem : (⟨h, hHY hh⟩ : ↥Y) ∈ H.subgroupOf Y := hh
  rw [hbot, Subgroup.mem_bot] at hmem
  exact h1 (congrArg Subtype.val hmem)

theorem mem_normalizer_subgroupOf {Y S : Subgroup G} {n : G} (hnY : n ∈ Y)
    (hnS : n ∈ Subgroup.normalizer (S : Set G)) :
    (⟨n, hnY⟩ : ↥Y) ∈ Subgroup.normalizer ((S.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro s
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  simpa using Subgroup.mem_normalizer_iff.mp hnS s

theorem centralizer_le_normalizer_zpowers (d : G) :
    Subgroup.centralizer ({d} : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  intro g hg
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  exact hg

theorem omegaZOf_pCoreOf_facts [Finite G] {LB Y : Subgroup G}
    (hU : CFSG.Open.pCoreOf 2 LB ≠ ⊥) (hLBY : LB ≤ Y)
    (hYLB : Y ≤ Subgroup.normalizer (LB : Set G)) :
    Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB) ≠ ⊥ ∧
      IsPGroup 2 (Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB)) ∧
      Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB) ≤ CFSG.Open.pCoreOf 2 LB ∧
      Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB) ≤ Y ∧
      Y ≤ Subgroup.normalizer (Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB) : Set G) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Sec3.omegaZOf (CFSG.Open.pCoreOf 2 LB) ≤ CFSG.Open.pCoreOf 2 LB :=
    fun z hz => ((mem_omegaZOf_iff _).mp hz).1
  exact ⟨omegaZOf_pCoreOf_ne_bot hU, (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 LB).to_le hle,
    hle, hle.trans ((CFSG.LieType.BorelTits.pCoreOf_le 2 LB).trans hLBY),
    le_normalizer_omegaZOf_pCoreOf hYLB⟩

end CFSG.RankThree.PartTwo.J2Residue
