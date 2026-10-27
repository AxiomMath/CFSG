module

public import CFSG.RankThree.PartTwo.Sec15.Item152Proof
import CFSG.RankThree.PartTwo.Sec15.Item152StepsEnd
import CFSG.GroupTheory.ABGDGroups.LinearDecomposition
import CFSG.RankThree.PartTwo.Sec15.Item153

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Gagen152SL25Res

variable {G : Type} [Group G] [Finite G]

theorem mem_oTwoOddIn_of_mem_pCore {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {X P N : Subgroup G}
    (hPX : P ≤ X) (hP : IsPGroup p P) (hC : X ⊓ Subgroup.centralizer (P : Set G) ≤ oTwoOddIn X)
    (hHX : X ≤ Subgroup.normalizer ((P ⊔ CFSG.Open.pCoreOf 2 X : Subgroup G) : Set G))
    (hN2 : IsPGroup 2 N) (hPN : P ≤ Subgroup.normalizer (N : Set G)) {z : G} (hzX : z ∈ X)
    (hzN : z ∈ N) : z ∈ oTwoOddIn X := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine mem_oTwoOddIn_of_commutator_mem hp2 hPX hP hC hzX fun u hu => ?_
  set Q := CFSG.Open.pCoreOf 2 X with hQ
  set H := P ⊔ Q with hH
  have hPQ : P ≤ Subgroup.normalizer (Q : Set G) :=
    hPX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X)
  haveI hQH : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_sup_right : Q ≤ H)).mpr
      (sup_le hPQ (Subgroup.le_normalizer (H := Q)))
  have huz : u * z * u⁻¹ ∈ N :=
    (Subgroup.mem_normalizer_iff.mp (hPN hu) z).mp hzN
  have hcN : ⁅z, u⁆ ∈ N := by
    rw [commutatorElement_def]
    have h := N.mul_mem hzN (N.inv_mem huz)
    convert h using 1
    group
  have hzuH : z * u * z⁻¹ ∈ H :=
    (Subgroup.mem_normalizer_iff.mp (hHX hzX) u).mp (Subgroup.mem_sup_left hu)
  have hcH : ⁅z, u⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem hzuH (H.inv_mem (Subgroup.mem_sup_left hu))
  obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hN2 ⟨⁅z, u⁆, hcN⟩
  have hpow : (⟨⁅z, u⁆, hcH⟩ : ↥H) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using congrArg Subtype.val hk
  have hodd : Odd (Q.subgroupOf H).index := by
    have hPQbot : P ⊓ Q = ⊥ :=
      (IsPGroup.disjoint_of_ne p 2 hp2 P Q hP (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)).eq_bot
    have hQPbot : Q.subgroupOf P = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have hxQ : (x : G) ∈ Q := Subgroup.mem_subgroupOf.mp hx
      have hmem : (x : G) ∈ P ⊓ Q := ⟨x.2, hxQ⟩
      rw [hPQbot] at hmem
      exact Subtype.ext (Subgroup.mem_bot.mp hmem)
    haveI hQPN : (Q.subgroupOf P).Normal := by rw [hQPbot]; infer_instance
    have hcard : Nat.card (↥P ⧸ Q.subgroupOf P) = Nat.card P := by
      rw [hQPbot]
      exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
    have hoddP : Odd (Nat.card P) := by
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
      rw [hn]
      exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
    rw [Subgroup.index_eq_card,
      ← Nat.card_congr (QuotientGroup.quotientInfEquivProdNormalizerQuotient P Q hPQ).toEquiv,
      hcard]
    exact hoddP
  have hpowN : (⟨⁅z, u⁆, hcH⟩ : ↥H) ^ 2 ^ k ∈ Q.subgroupOf H := by
    rw [hpow]
    exact (Q.subgroupOf H).one_mem
  have hmem : (⟨⁅z, u⁆, hcH⟩ : ↥H) ∈ Q.subgroupOf H :=
    CFSG.ABGDGroups.mem_of_pow_two_pow_mem (N := Q.subgroupOf H) hodd hpowN
  exact Subgroup.mem_subgroupOf.mp hmem

theorem pCoreOf_le_of_le_sup {Y L : Subgroup G} (hLY : L ≤ Y)
    (hY : Y ≤ L ⊔ CFSG.Open.pCoreOf 2 Y) : CFSG.Open.pCoreOf 2 L ≤ CFSG.Open.pCoreOf 2 Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 Y with hQ
  set K := CFSG.Open.pCoreOf 2 L ⊔ Q with hK
  have hPL : CFSG.Open.pCoreOf 2 L ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hQY : Q ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hKY : K ≤ Y := sup_le (hPL.trans hLY) hQY
  have hYQ : Y ≤ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.le_normalizer (H := Y)).trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y)
  have hLNK : L ≤ Subgroup.normalizer (K : Set G) := by
    refine (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L) (hLY.trans hYQ)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup (CFSG.Open.pCoreOf 2 L) Q)
  have hQNK : Q ≤ Subgroup.normalizer (K : Set G) :=
    (le_sup_right : Q ≤ K).trans (Subgroup.le_normalizer (H := K))
  have hYNK : Y ≤ Subgroup.normalizer (K : Set G) := hY.trans (sup_le hLNK hQNK)
  have hK2 : IsPGroup 2 K :=
    IsPGroup.to_sup_of_normal_right' (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) (hPL.trans (hLY.trans hYQ))
  exact le_sup_left.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKY hYNK hK2)

theorem pCoreOf_le_pCoreOf_n155 {A Y : Subgroup G} (hY : Y ∈ scriptY0Star A (lB A)) :
    CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2
      (oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G)))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYX : Y ≤ oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) :=
    le_oPrimeResidualOf_delta hY.prop.1 (Subgroup.le_normalizer (H := Y))
  have hXN : oPrimeResidualOf 3 (delta A (lB A) (Subgroup.normalizer (Y : Set G))) ≤
      Subgroup.normalizer (Y : Set G) := by
    unfold CFSG.GH74.GLS.oPrimeResidualOf
    exact (Subgroup.map_subtype_le _).trans (delta_le _)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans hYX)
    (hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y)

end Gagen152SL25Res

end CFSG.RankThree.PartTwo.Sec15
