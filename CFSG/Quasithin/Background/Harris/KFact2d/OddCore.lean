module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.Background.Harris.KFact2d

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type} [Group G]

theorem normal_subgroupOf_of_le_normalizer {Q Y : Subgroup G}
    (hQn : Y ≤ Subgroup.normalizer (Q : Set G)) : (Q.subgroupOf Y).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hQn g.2) _).mp hn⟩

theorem mk_pow_eq_one_iff {Q Y : Subgroup G} (hQn : Y ≤ Subgroup.normalizer (Q : Set G)) {y : G}
    (hy : y ∈ Y) (n : ℕ) :
    haveI := normal_subgroupOf_of_le_normalizer hQn
    (QuotientGroup.mk' (Q.subgroupOf Y) (⟨y, hy⟩ : ↥Y)) ^ n = 1 ↔ y ^ n ∈ Q := by
  haveI := normal_subgroupOf_of_le_normalizer hQn
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  rfl

@[expose] def twoPartMod (Q Y : Subgroup G) (hQn : Y ≤ Subgroup.normalizer (Q : Set G))
    (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Q) : Subgroup G where
  carrier := {y | y ∈ Y ∧ ∃ k : ℕ, y ^ 2 ^ k ∈ Q}
  one_mem' := ⟨Y.one_mem, 0, by simp⟩
  inv_mem' := by
    rintro y ⟨hy, k, hk⟩
    refine ⟨Y.inv_mem hy, k, ?_⟩
    rw [inv_pow]
    exact Q.inv_mem hk
  mul_mem' := by
    rintro a b ⟨ha, i, hi⟩ ⟨hb, j, hj⟩
    refine ⟨Y.mul_mem ha hb, i + j, ?_⟩
    haveI := normal_subgroupOf_of_le_normalizer hQn
    let φ : ↥Y →* ↥Y ⧸ Q.subgroupOf Y := QuotientGroup.mk' (Q.subgroupOf Y)
    have hcomm : Commute (φ ⟨a, ha⟩) (φ ⟨b, hb⟩) := by
      show φ ⟨a, ha⟩ * φ ⟨b, hb⟩ = φ ⟨b, hb⟩ * φ ⟨a, ha⟩
      rw [← map_mul, ← map_mul]
      apply QuotientGroup.eq.mpr
      rw [Subgroup.mem_subgroupOf]
      have := hab b⁻¹ (Y.inv_mem hb) a⁻¹ (Y.inv_mem ha)
      simpa [mul_assoc, mul_inv_rev] using this
    have h1 : (φ ⟨a, ha⟩) ^ 2 ^ (i + j) = 1 := by
      rw [pow_add, pow_mul]
      have : (φ ⟨a, ha⟩) ^ 2 ^ i = 1 := (mk_pow_eq_one_iff hQn ha _).mpr hi
      rw [this, one_pow]
    have h2 : (φ ⟨b, hb⟩) ^ 2 ^ (i + j) = 1 := by
      rw [add_comm, pow_add, pow_mul]
      have : (φ ⟨b, hb⟩) ^ 2 ^ j = 1 := (mk_pow_eq_one_iff hQn hb _).mpr hj
      rw [this, one_pow]
    have h3 : (φ ⟨a * b, Y.mul_mem ha hb⟩) ^ 2 ^ (i + j) = 1 := by
      have : (⟨a * b, Y.mul_mem ha hb⟩ : ↥Y) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
      rw [this, map_mul, hcomm.mul_pow, h1, h2, one_mul]
    exact (mk_pow_eq_one_iff hQn (Y.mul_mem ha hb) _).mp h3

theorem twoPartMod_le_pCoreOf {N Q Y : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hQN : N ≤ Subgroup.normalizer (Q : Set G)) (hYN : Y ≤ N)
    (hYn : N ≤ Subgroup.normalizer (Y : Set G))
    (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Q) :
    twoPartMod Q Y (hYN.trans hQN) hab ≤ pCoreOf 2 N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQn : Y ≤ Subgroup.normalizer (Q : Set G) := hYN.trans hQN
  set P := twoPartMod Q Y hQn hab with hP
  have hPN : P ≤ N := fun y hy => hYN hy.1
  have hP2 : IsPGroup 2 P := by
    intro g
    obtain ⟨hgY, k, hk⟩ := g.2
    obtain ⟨j, hj⟩ := hQ2 ⟨_, hk⟩
    refine ⟨k + j, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hj
    simp only [Subgroup.coe_pow, OneMemClass.coe_one] at this ⊢
    rw [pow_add, pow_mul]
    exact this
  have hPnorm : N ≤ Subgroup.normalizer (P : Set G) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ m ∈ N, ∀ y ∈ P, m * y * m⁻¹ ∈ P := by
      intro m hm y hy
      obtain ⟨hyY, k, hk⟩ := hy
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hYn hm) y).mp hyY, k, ?_⟩
      have : (m * y * m⁻¹) ^ 2 ^ k = m * y ^ 2 ^ k * m⁻¹ := by
        rw [conj_pow]
      rw [this]
      exact (Subgroup.mem_normalizer_iff.mp (hQN hm) _).mp hk
    intro x
    refine ⟨fun hx => key n hn x hx, fun hx => ?_⟩
    have := key n⁻¹ (N.inv_mem hn) _ hx
    simpa [mul_assoc] using this
  exact le_pCoreOf_of_le_normalizer 2 hPN hPnorm hP2

theorem le_pCoreOf_of_abelian_mod {N Q Y V : Subgroup G} (hQ2 : IsPGroup 2 Q)
    (hQN : N ≤ Subgroup.normalizer (Q : Set G)) (hYN : Y ≤ N)
    (hYn : N ≤ Subgroup.normalizer (Y : Set G))
    (hab : ∀ a ∈ Y, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ Q) (hV : V ≤ Y) (hV2 : IsPGroup 2 V) :
    V ≤ pCoreOf 2 N := by
  refine le_trans ?_ (twoPartMod_le_pCoreOf hQ2 hQN hYN hYn hab)
  intro v hv
  obtain ⟨k, hk⟩ := hV2 ⟨v, hv⟩
  refine ⟨hV hv, k, ?_⟩
  have : v ^ 2 ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  rw [this]
  exact Q.one_mem

end CFSG.Quasithin.Background.Harris.KFact2d
