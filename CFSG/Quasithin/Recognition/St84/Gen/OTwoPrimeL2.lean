module

public import CFSG.Quasithin.EmptyFaithful.S1421F112
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.Quasithin.EmptyFaithful.S1421QNSSurv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {G : Type*} [Group G]

theorem le_oTwoPrime_of_isL2Quot_of_two_le {A E : Subgroup G} [Finite ↥A] {n : ℕ}
    (hn : 2 ≤ n) (hAE : A ≤ E) (hq : IsL2Quot n (oTwoQuot ↥A)) :
    A ≤ oTwoPrime E := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let L := oTwoPrime E
  let D := pCoreOf 2 A
  let N := A ⊓ L
  have hNL : N ≤ L := inf_le_right
  have hNA : N ≤ A := inf_le_left
  have hDle : D ≤ N := by
    refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 A) ?_
    exact le_oTwoPrime_of_isPGroup
      (pCore_isPGroup (G := ↥A) (p := 2) |>.map A.subtype)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 A).trans hAE)
  have hAN : A ≤ Subgroup.normalizer (N : Set G) := by
    have hAL : A ≤ Subgroup.normalizer (L : Set G) := hAE.trans (le_normalizer_oTwoPrime E)
    exact (le_inf Subgroup.le_normalizer hAL).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hNnormal : (N.subgroupOf A).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hAN
  have hqe : D.subgroupOf A = CFSG.pCore 2 ↥A := CFSG.openPCoreOf_subgroupOf 2 A
  haveI hDnormal : (D.subgroupOf A).Normal := by
    rw [hqe]
    exact CFSG.pCore_normal
  let π : ↥A →* (↥A ⧸ D.subgroupOf A) := QuotientGroup.mk' (D.subgroupOf A)
  let Nbar : Subgroup (↥A ⧸ D.subgroupOf A) := (N.subgroupOf A).map π
  have hNbarNormal : Nbar.Normal :=
    hNnormal.map π (QuotientGroup.mk'_surjective (N := D.subgroupOf A))
  haveI : Nbar.Normal := hNbarNormal
  haveI : IsSimpleGroup (↥A ⧸ D.subgroupOf A) := by
    have e : (↥A ⧸ D.subgroupOf A) ≃* oTwoQuot ↥A :=
      QuotientGroup.quotientMulEquivOfEq hqe
    exact e.isSimpleGroup_congr.mpr
      (CFSG.Quasithin.S1421NS.isSimpleGroup_of_isL2Quot hn hq)
  have hcard : Nat.card (↥A ⧸ D.subgroupOf A) = 2 ^ n * (4 ^ n - 1) := by
    have e : (↥A ⧸ D.subgroupOf A) ≃* (↥A ⧸ CFSG.pCore 2 ↥A) :=
      QuotientGroup.quotientMulEquivOfEq hqe
    rw [Nat.card_congr e.toEquiv]
    exact IsL2Quot.card (f := n) (by omega) hq
  have hNbarNe : Nbar ≠ ⊥ := by
    intro hbar
    have hle : N.subgroupOf A ≤ π.ker :=
      (Subgroup.map_eq_bot_iff (N.subgroupOf A) (f := π)).mp hbar
    rw [QuotientGroup.ker_mk'] at hle
    have hND : N ≤ D := by
      intro n hn
      have hmemN : (⟨n, hNA hn⟩ : ↥A) ∈ N.subgroupOf A :=
        Subgroup.mem_subgroupOf.mpr hn
      have hmemD : (⟨n, hNA hn⟩ : ↥A) ∈ D.subgroupOf A := hle hmemN
      exact Subgroup.mem_subgroupOf.mp hmemD
    have h2dvd : 2 ∣ Nat.card (↥A ⧸ D.subgroupOf A) := by
      rw [hcard]
      refine dvd_mul_of_dvd_left ?_ _
      rw [show n = n - 1 + 1 by omega, pow_succ]
      simpa [mul_comm] using dvd_mul_right 2 (2 ^ (n - 1))
    obtain ⟨q, hq2⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    obtain ⟨x, rfl⟩ := (QuotientGroup.mk'_surjective (N := D.subgroupOf A)) q
    have hx2q : (π x) ^ 2 = 1 := by
      rw [← hq2]
      exact pow_orderOf_eq_one (π x)
    have hx2ker : x * x ∈ D.subgroupOf A := by
      have h1 : π (x * x) = 1 := by
        rw [map_mul]
        simpa [pow_two] using hx2q
      exact (QuotientGroup.eq_one_iff (x * x)).mp h1
    have hx2D : ((x * x : ↥A) : G) ∈ D := Subgroup.mem_subgroupOf.mp hx2ker
    have hDp : IsPGroup 2 D :=
      pCore_isPGroup (G := ↥A) (p := 2) |>.map A.subtype
    obtain ⟨k, hk⟩ := hDp ⟨((x * x : ↥A) : G), hx2D⟩
    have hx2pow : ((x : G) * (x : G)) ^ 2 ^ k = 1 := by
      simpa using congrArg Subtype.val hk
    have hxpow : (x : G) ^ 2 ^ (k + 1) = 1 := by
      calc (x : G) ^ 2 ^ (k + 1) = (x : G) ^ (2 * 2 ^ k) := by rw [pow_succ']
        _ = ((x : G) ^ 2) ^ 2 ^ k := by rw [pow_mul]
        _ = ((x : G) * (x : G)) ^ 2 ^ k := by rw [pow_two]
        _ = 1 := hx2pow
    have hz : IsPGroup 2 (Subgroup.zpowers (x : G)) :=
      IsPGroup.of_card_dvd_pow (n := k + 1) (by
        rw [Nat.card_zpowers]
        exact orderOf_dvd_of_pow_eq_one hxpow)
    have hxL : (x : G) ∈ L :=
      le_oTwoPrime_of_isPGroup hz ((Subgroup.zpowers_le.mpr x.2).trans hAE)
        (Subgroup.mem_zpowers (x : G))
    have hxN : (x : G) ∈ N := ⟨x.2, hxL⟩
    have hxD : (x : G) ∈ D := hND hxN
    have hx1 : π x = 1 :=
      (QuotientGroup.eq_one_iff x).mpr (Subgroup.mem_subgroupOf.mpr hxD)
    rw [hx1] at hq2
    simpa using hq2
  have hNbarTop : Nbar = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top Nbar with h | h
    · exact absurd h hNbarNe
    · exact h
  have htopN : (N.subgroupOf A) ⊔ (D.subgroupOf A) = ⊤ := by
    have hmap : ((N.subgroupOf A) ⊔ (D.subgroupOf A)).map π = ⊤ := by
      rw [Subgroup.map_sup]
      change Nbar ⊔ (D.subgroupOf A).map π = ⊤
      have hmapD : (D.subgroupOf A).map π = ⊥ := by
        refine (Subgroup.map_eq_bot_iff (D.subgroupOf A) (f := π)).mpr ?_
        intro y hy
        rw [QuotientGroup.ker_mk']
        exact hy
      rw [hNbarTop, hmapD, sup_bot_eq]
    have hcomap := Subgroup.comap_map_eq_self (f := π)
      (H := (N.subgroupOf A) ⊔ (D.subgroupOf A)) (by
        rw [QuotientGroup.ker_mk']
        exact le_sup_right)
    rw [hmap] at hcomap
    simpa using hcomap.symm
  have hsup : N ⊔ D = A := by
    have h1 : (N ⊔ D).subgroupOf A = ⊤ := by
      rw [Subgroup.subgroupOf_sup hNA (CFSG.LieType.BorelTits.pCoreOf_le 2 A)]
      exact htopN
    exact le_antisymm
      (sup_le hNA (CFSG.LieType.BorelTits.pCoreOf_le 2 A))
      ((Subgroup.subgroupOf_eq_top (H := N ⊔ D) (K := A)).mp h1)
  have hNAeq : N = A := by
    rw [sup_eq_left.mpr hDle] at hsup
    exact hsup
  rw [← hNAeq]
  exact hNL

end CFSG.Quasithin
