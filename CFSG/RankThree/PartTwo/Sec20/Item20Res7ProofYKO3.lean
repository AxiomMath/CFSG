module

public import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofCover
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools
import CFSG.RankThree.PartTwo.Sec18.Item186a

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open scoped Pointwise

@[expose] def Step204YKO3Comm : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        yTwenty X c ≤ kTwenty M c ⊔ inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c) →
          ∀ k ∈ kTwenty M c, ∀ o ∈ inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c),
            k * o * k⁻¹ * o⁻¹ ∈
              CFSG.Open.pCoreOf 2 (inSubgroup (CFSG.pPrimeCore 3) (yTwenty X c))

namespace Res7

variable {G : Type} [Group G] [Finite G]

theorem inf_le_pCoreOf_of_coprime {K J : Subgroup G}
    (hsimple : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K)) (hKJ : K ≤ Subgroup.normalizer (J : Set G))
    (hJ3 : Nat.Coprime 3 (Nat.card J)) {c : G} (hcK : c ∈ K) (hc : orderOf c = 3) :
    K ⊓ J ≤ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set I : Subgroup K := J.subgroupOf K with hI
  have hIn : I.Normal := by
    refine ⟨fun x hx k => ?_⟩
    rw [hI, Subgroup.mem_subgroupOf] at hx ⊢
    have := (Subgroup.mem_normalizer_iff.mp (hKJ k.2) x).mp hx
    simpa using this
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥K) with hπ
  have hImn : (I.map π).Normal := Subgroup.Normal.map hIn π (QuotientGroup.mk'_surjective _)
  have hI3 : Nat.Coprime 3 (Nat.card I) := by
    have h1 : Nat.card I = Nat.card (J ⊓ K : Subgroup G) := by
      rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_left) hJ3
  have hIm3 : Nat.Coprime 3 (Nat.card (I.map π)) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_map_dvd I π) hI3
  have hIm : I.map π = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (I.map π) with h | h
    · exact h
    · exfalso
      have hc1 : π ⟨c, hcK⟩ ≠ 1 := by
        intro h1
        rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
          Sec18.mem_pCore_iff_mem_pCoreOf] at h1
        exact Res6.not_mem_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hc h1
      have hc3 : (π ⟨c, hcK⟩) ^ 3 = 1 := by
        rw [← map_pow]
        have : (⟨c, hcK⟩ : K) ^ 3 = 1 := Subtype.ext (by
          rw [Subgroup.coe_pow, Subgroup.coe_one, ← hc, pow_orderOf_eq_one])
        rw [this, map_one]
      have hord : orderOf (π ⟨c, hcK⟩) = 3 := orderOf_eq_prime hc3 hc1
      have hmem : π ⟨c, hcK⟩ ∈ I.map π := by rw [h]; exact Subgroup.mem_top _
      have hdvd : 3 ∣ Nat.card (I.map π) := by
        rw [← hord, ← Subgroup.orderOf_mk _ hmem]
        exact orderOf_dvd_natCard _
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hIm3 hdvd
  intro x hx
  have hmem : π ⟨x, hx.1⟩ ∈ I.map π := ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.mpr hx.2, rfl⟩
  rw [hIm, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact (Sec18.mem_pCore_iff_mem_pCoreOf _).mp hmem

end Res7

theorem step204YKO3_of_comm (h : Step204YKO3Comm) : Step204YKO3 := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hle
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := kTwenty M c with hKdef
  set Y := yTwenty X c with hYdef
  set O3 := inSubgroup (CFSG.pPrimeCore 3) Y with hO3
  set Q₂ := CFSG.Open.pCoreOf 2 O3 with hQ₂
  have hcomm := h G A M L N c T i j P hset X hX hXM hm hle
  have hKX : K ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
  have hKY : K ≤ Y := Res6.kTwenty_le_yTwenty hset hKX
  have hO3Y : O3 ≤ Y := Res6.inSubgroup_pPrimeCore_le 3 Y
  have hYO3 : Y ≤ Subgroup.normalizer (O3 : Set G) := Res6.le_normalizer_inSubgroup_pPrimeCore 3 Y
  have hYQ : Y ≤ Subgroup.normalizer (Q₂ : Set G) :=
    hYO3.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 O3)
  have hc := Res6.orderOf_c_of_setting204 hset
  have hcK : c ∈ K := self_mem_normalClosureIn M c
  have hQO3 : Q₂ ≤ O3 := CFSG.LieType.BorelTits.pCoreOf_le 2 O3
  have hYKQ : Y ≤ K ⊔ Q₂ := by
    refine (Res6.yTwenty_le_normalClosureIn_self hset X).trans ?_
    rw [normalClosureIn, Subgroup.closure_le]
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ ((K ⊔ O3 : Subgroup G) : Set G) := hle hy
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K O3 (hKY.trans hYO3)] at hy'
    obtain ⟨k, hk, o, ho, rfl⟩ := hy'
    have h1 : c⁻¹ * o * c⁻¹⁻¹ * o⁻¹ ∈ Q₂ := hcomm c⁻¹ (K.inv_mem hcK) o ho
    have h2 : o * c * o⁻¹ = c * (c⁻¹ * o * c⁻¹⁻¹ * o⁻¹) := by group
    have h3 : o * c * o⁻¹ ∈ K ⊔ Q₂ := by
      rw [h2]
      exact (K ⊔ Q₂).mul_mem (Subgroup.mem_sup_left hcK) (Subgroup.mem_sup_right h1)
    have hkn : k ∈ Subgroup.normalizer ((K ⊔ Q₂ : Subgroup G) : Set G) :=
      Res6.mem_normalizer_sup (Subgroup.le_normalizer hk) (hYQ (hKY hk))
    have h4 := (Subgroup.mem_normalizer_iff.mp hkn _).mp h3
    rw [SetLike.mem_coe]
    convert h4 using 1
    group
  have hKO3 : K ⊓ O3 ≤ CFSG.Open.pCoreOf 2 K :=
    Res7.inf_le_pCoreOf_of_coprime (Res6.isSimpleGroup_of_setting204 hset) (hKY.trans hYO3)
      (Res6.coprime_card_inSubgroup_pPrimeCore 3 Y) hcK hc
  have hW2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 K ⊔ Q₂ : Subgroup G) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).to_sup_of_normal_right'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 O3)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans (hKY.trans hYQ))
  refine hW2.to_le ?_
  intro o ho
  have ho' : o ∈ ((K ⊔ Q₂ : Subgroup G) : Set G) := hYKQ (hO3Y ho)
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K Q₂ (hKY.trans hYQ)] at ho'
  obtain ⟨k, hk, q, hq, rfl⟩ := ho'
  have hkO3 : k ∈ O3 := by
    have : k * q * q⁻¹ ∈ O3 := O3.mul_mem ho (O3.inv_mem (hQO3 hq))
    simpa using this
  exact Subgroup.mul_mem_sup (hKO3 ⟨hk, hkO3⟩) hq

end CFSG.RankThree.PartTwo.Sec20
