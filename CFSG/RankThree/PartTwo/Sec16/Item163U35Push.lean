module

public import CFSG.RankThree.PartTwo.Sec14.Item1411StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec13.Item13Basic
import CFSG.RankThree.PartTwo.Sec15.Item153
import CFSG.RankThree.PartTwo.Sec16.Item162Res7PushA7
import CFSG.RankThree.PartTwo.Sec17.Item17Q0ProofTools
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec16

namespace Proof163U35

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.PartTwo.Sec15 CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Sec17.Proof17Q0 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCoreOf_le_of_mem_scriptQPiStar_normalizer {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} (hA : IsE27 A) (h146 : Item146 A LB) {K T : Subgroup G}
    (hQ : CFSG.Open.pCoreOf 2 K ∈ scriptQ A LB)
    (hT : T ∈ scriptQPiStar A LB (Subgroup.normalizer (K : Set G)) (piOf 2)) :
    CFSG.Open.pCoreOf 2 K ≤ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := CFSG.Open.pCoreOf 2 K
  have hTK : T ≤ Subgroup.normalizer (K : Set G) := hT.prop.1.2
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) :=
    hTK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hQpi : Q ∈ scriptQPi A LB (Subgroup.normalizer (K : Set G)) (piOf 2) :=
    ⟨⟨hQ, (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans Subgroup.le_normalizer⟩,
      (isPiSubgroup_piOf_iff Nat.prime_two Q).mpr
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)⟩
  have hUT : T ⊔ Q ∈ scriptQPi A LB (Subgroup.normalizer (K : Set G)) (piOf 2) :=
    sup_mem_scriptQPi_of_item146 hA h146 hT.prop hQpi hTQ
  exact (le_sup_right : Q ≤ T ⊔ Q).trans (hT.2 hUT le_sup_left)

private theorem isQuasisimple_quotient_sup_of_scriptY4 {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} {K₁ K₂ : Subgroup G}
    (hK₁ : K₁ ∈ scriptY4 A LB) (hK₂ : K₂ ∈ scriptY4 A LB)
    (h₁₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set G))
    (h₂₁ : K₂ ≤ Subgroup.normalizer (K₁ : Set G))
    (hcov : K₂ ≤ K₁ ⊔ CFSG.Open.pCoreOf 2 K₂) :
    CFSG.IsQuasisimple (↥(K₁ ⊔ K₂) ⧸ CFSG.pCore 2 ↥(K₁ ⊔ K₂)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := CFSG.Open.pCoreOf 2 (K₁ ⊔ K₂)
  have hK₁X : K₁ ≤ K₁ ⊔ K₂ := le_sup_left
  have hK₂X : K₂ ≤ K₁ ⊔ K₂ := le_sup_right
  have hX_N : K₁ ⊔ K₂ ≤ Subgroup.normalizer (N : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (K₁ ⊔ K₂)
  have hK₁_N : K₁ ≤ Subgroup.normalizer (N : Set G) := hK₁X.trans hX_N
  have hO₁N : CFSG.Open.pCoreOf 2 K₁ ≤ N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans hK₁X)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₁)
        (h₂₁.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have hO₂N : CFSG.Open.pCoreOf 2 K₂ ≤ N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₂).trans hK₂X)
      (sup_le (h₁₂.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₂))
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₂))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₂)
  have hXN : K₁ ⊔ N = K₁ ⊔ K₂ := by
    refine le_antisymm (sup_le le_sup_left (CFSG.LieType.BorelTits.pCoreOf_le 2 _)) ?_
    refine sup_le le_sup_left (hcov.trans ?_)
    exact sup_le le_sup_left (hO₂N.trans le_sup_right)
  have hinf : N ⊓ K₁ = CFSG.Open.pCoreOf 2 K₁ := by
    refine le_antisymm ?_ (le_inf hO₁N (CFSG.LieType.BorelTits.pCoreOf_le 2 K₁))
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K₁ ⊔ K₂)).to_le inf_le_left)
    exact (le_inf hK₁_N Subgroup.le_normalizer).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  haveI : (N.subgroupOf (K₁ ⊔ K₂)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hX_N
  let f : ↥K₁ →* ↥(K₁ ⊔ K₂) ⧸ N.subgroupOf (K₁ ⊔ K₂) :=
    (QuotientGroup.mk' (N.subgroupOf (K₁ ⊔ K₂))).comp
      (Subgroup.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂))
  have hsurj : Function.Surjective f := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (N.subgroupOf (K₁ ⊔ K₂)) q
    have hx : (x : G) ∈ ((K₁ ⊔ N : Subgroup G) : Set G) := by
      rw [hXN]
      exact x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K₁ N hK₁_N] at hx
    obtain ⟨k, hk, n, hn, hkn⟩ := hx
    have hnX : n ∈ K₁ ⊔ K₂ := (CFSG.LieType.BorelTits.pCoreOf_le 2 (K₁ ⊔ K₂)) hn
    refine ⟨⟨k, hk⟩, ?_⟩
    have hf : f ⟨k, hk⟩ = QuotientGroup.mk' (N.subgroupOf (K₁ ⊔ K₂))
        (Subgroup.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂) ⟨k, hk⟩) := rfl
    rw [hf, QuotientGroup.mk'_eq_mk']
    exact ⟨⟨n, hnX⟩, hn, Subtype.ext (by simpa using hkn)⟩
  have hker : f.ker = CFSG.pCore 2 ↥K₁ := by
    refine Subgroup.ext fun y => ?_
    rw [MonoidHom.mem_ker]
    have hfy : f y = QuotientGroup.mk' (N.subgroupOf (K₁ ⊔ K₂))
        (Subgroup.inclusion (le_sup_left : K₁ ≤ K₁ ⊔ K₂) y) := rfl
    rw [hfy, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hyN
      exact (CFSG.mem_openPCoreOf_iff y).mp (hinf ▸ ⟨hyN, y.2⟩)
    · intro hy
      exact hO₁N ((CFSG.mem_openPCoreOf_iff y).mpr hy)
  have hq : CFSG.IsQuasisimple (↥(K₁ ⊔ K₂) ⧸ N.subgroupOf (K₁ ⊔ K₂)) := by
    have e2 : ↥K₁ ⧸ CFSG.pCore 2 ↥K₁ ≃* ↥(K₁ ⊔ K₂) ⧸ N.subgroupOf (K₁ ⊔ K₂) :=
      (QuotientGroup.quotientMulEquivOfEq hker).symm.trans
        (QuotientGroup.quotientKerEquivOfSurjective f hsurj)
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e2 hK₁.2.2.2
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (QuotientGroup.quotientMulEquivOfEq (CFSG.openPCoreOf_subgroupOf 2 (K₁ ⊔ K₂))) hq

theorem sup_mem_scriptY0 {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ scriptY0 A LB) (hK₂ : K₂ ∈ scriptY0 A LB)
    (h₁₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set G))
    (h₂₁ : K₂ ≤ Subgroup.normalizer (K₁ : Set G))
    (hcov : K₂ ≤ K₁ ⊔ CFSG.Open.pCoreOf 2 K₂) (htop : K₁ ⊔ K₂ ≠ ⊤) :
    K₁ ⊔ K₂ ∈ scriptY0 A LB := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hX : K₁ ⊔ K₂ ∈ scriptY A := by
    refine ⟨htop, ?_⟩
    exact (le_inf hK₁.1.1.2 hK₂.1.1.2).trans
      (Subgroup.inf_normalizer_le_normalizer_sup K₁ K₂)
  have hXoRes : K₁ ⊔ K₂ = oPrimeResidualOf 3 (K₁ ⊔ K₂) := by
    refine le_antisymm ?_ (Subgroup.map_subtype_le _)
    exact sup_le (hK₁.1.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_left))
      (hK₂.1.2.1.le.trans (oPrimeResidualOf_mono 3 le_sup_right))
  have hXdelta : K₁ ⊔ K₂ = delta A LB (K₁ ⊔ K₂) := by
    refine le_antisymm ?_ (delta_le _)
    exact sup_le (hK₁.1.2.2.1.le.trans (delta_mono le_sup_left))
      (hK₂.1.2.2.1.le.trans (delta_mono le_sup_right))
  have hXq : CFSG.IsQuasisimple (↥(K₁ ⊔ K₂) ⧸ CFSG.pCore 2 ↥(K₁ ⊔ K₂)) :=
    isQuasisimple_quotient_sup_of_scriptY4 hK₁.1 hK₂.1 h₁₂ h₂₁ hcov
  have hO₁X : CFSG.Open.pCoreOf 2 K₁ ≤ CFSG.Open.pCoreOf 2 (K₁ ⊔ K₂) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₁).trans le_sup_left)
      (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₁)
        (h₂₁.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₁)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₁)
  have hO₂ne : CFSG.Open.pCoreOf 2 (K₁ ⊔ K₂) ≠ ⊥ := fun hbot =>
    hK₁.2.2 (le_bot_iff.mp (hbot ▸ hO₁X))
  exact ⟨⟨hX, hXoRes, hXdelta, hXq⟩, ⟨hX, hO₂ne⟩⟩

theorem eq_of_mem_scriptY0Star {A : Subgroup G} {LB : Subgroup G → Subgroup G}
    {K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ scriptY0Star A LB) (hK₂ : K₂ ∈ scriptY0Star A LB)
    (h₁₂ : K₁ ≤ Subgroup.normalizer (K₂ : Set G))
    (h₂₁ : K₂ ≤ Subgroup.normalizer (K₁ : Set G))
    (hcov : K₂ ≤ K₁ ⊔ CFSG.Open.pCoreOf 2 K₂) (htop : K₁ ⊔ K₂ ≠ ⊤) : K₁ = K₂ := by
  have hsup : K₁ ⊔ K₂ ∈ scriptY0 A LB :=
    sup_mem_scriptY0 hK₁.prop hK₂.prop h₁₂ h₂₁ hcov htop
  refine le_antisymm ?_ ?_
  · exact le_sup_left.trans (hK₂.2 hsup le_sup_right)
  · exact le_sup_right.trans (hK₁.2 hsup le_sup_left)

private theorem commutator_mem_of_eq_sup_pCoreOf {K M : Subgroup G} {b : G}
    (hcov : K = M ⊔ CFSG.Open.pCoreOf 2 K)
    (hMb : M ≤ Subgroup.centralizer ({b} : Set G))
    (hbO : b ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G)) :
    ∀ y ∈ K, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
  intro y hy
  have hMK : M ≤ K := (le_sup_left : M ≤ M ⊔ CFSG.Open.pCoreOf 2 K).trans hcov.symm.le
  have h := commutatorElement_mem_of_eq_sup (Y := K) (V := CFSG.Open.pCoreOf 2 K)
    (L := M) (x := b) hcov
    (hMK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)) hbO hMb y hy
  rw [show b * y * b⁻¹ * y⁻¹ = ⁅y, b⁆⁻¹ by rw [commutatorElement_def]; group]
  exact (CFSG.Open.pCoreOf 2 K).inv_mem h

private theorem commutator_le_pCoreOf_sup_of_centralizes {K T C : Subgroup G}
    (hT : IsPGroup 2 T) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hCK : C ≤ Subgroup.normalizer (K : Set G))
    (hCT : C ≤ Subgroup.normalizer (T : Set G))
    (hcent : ∀ b ∈ C, ∀ y ∈ K, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K) :
    ⁅T, C⁆ ≤ CFSG.Open.pCoreOf 2 (K ⊔ T) := by
  rw [Subgroup.commutator_le]
  intro t ht b hb
  have h1 := commutator_mem_pCoreOf_sup hT hTK hZ (hCK hb) (hCT hb) (hcent b hb)
    (x := t) ((le_sup_right : T ≤ K ⊔ T) ht)
  rw [show ⁅t, b⁆ = (b * t * b⁻¹ * t⁻¹)⁻¹ by rw [commutatorElement_def]; group]
  exact (CFSG.Open.pCoreOf 2 (K ⊔ T)).inv_mem h1

theorem pCoreOf_sup_eq_commutator {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) (h146 : Item146 A (lB A)) (h142 : Concl142 A (lB A))
    {K T : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hT : T ∈ scriptQPiStar A (lB A) (Subgroup.normalizer (K : Set G)) (piOf 2))
    (hcov : K = (K ⊓ L) ⊔ CFSG.Open.pCoreOf 2 K) (hKT : CFSG.Open.pCoreOf 2 K ≤ T)
    (hZ : Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥)
    (hC : CFSG.Open.pCoreOf 2 (K ⊔ T) ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) :
    CFSG.Open.pCoreOf 2 (K ⊔ T) = ⁅T, Subgroup.zpowers c⁆ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : Late.IsE27 A := Late.isE27_of_mem_partTwoE h.toSec13Data.mem_partTwoE
  have hcA : c ∈ A := (zpowers_mem_omegaA_iff.mp h.toSec13Data.zpowers_mem_omegaA).1
  have hcK : c ∈ Subgroup.normalizer (K : Set G) := hAK hcA
  have hAT : A ≤ Subgroup.normalizer (T : Set G) := (mem_scriptQ_iff.mp hT.prop.1.1).2.1
  have hcT : c ∈ Subgroup.normalizer (T : Set G) := hAT hcA
  have hAKT : A ≤ Subgroup.normalizer (K ⊔ T : Subgroup G) :=
    (le_inf hAK hAT).trans (Subgroup.inf_normalizer_le_normalizer_sup K T)
  have hcO : c ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K) hcK
  have hcentral : ∀ b ∈ Subgroup.zpowers c, ∀ y ∈ K,
      b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 K := by
    intro b hb y hy
    have hMb : K ⊓ L ≤ Subgroup.centralizer ({b} : Set G) := by
      intro l hl
      have hlc : Commute l c :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (Sec13Data.le_centralizer h.toSec13Data hl.2)
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hlc.zpow_right j)
    exact commutator_mem_of_eq_sup_pCoreOf hcov hMb
      (Subgroup.zpowers_le.mpr hcO hb) y hy
  have hQleT : CFSG.Open.pCoreOf 2 (K ⊔ T) ≤ T :=
    pCoreOf_sup_le_of_centralizes h h146 h142 hAK hT
      (hcentral c (Subgroup.mem_zpowers c)) hKT
  have hcomm_le : ⁅T, Subgroup.zpowers c⁆ ≤ CFSG.Open.pCoreOf 2 (K ⊔ T) :=
    commutator_le_pCoreOf_sup_of_centralizes
      (isPGroup_of_mem_scriptQPi Nat.prime_two hT.prop) hT.prop.1.2 hZ
      (Subgroup.zpowers_le.mpr hcK) (Subgroup.zpowers_le.mpr hcT)
      (fun b hb => hcentral b hb)
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (K ⊔ T)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (K ⊔ T)
  have hcompl : ¬ 3 ∣ Nat.card (CFSG.Open.pCoreOf 2 (K ⊔ T)) := by
    intro h3
    obtain ⟨n, hn⟩ := hQ2.exists_card_eq
    rw [hn] at h3
    exact absurd (Nat.prime_three.dvd_of_dvd_pow h3) (by norm_num)
  have hpgroup : IsPGroup 3 (Subgroup.zpowers c) := by
    have hord : orderOf c ∣ 3 := orderOf_dvd_of_pow_eq_one (hE.1.2 c hcA)
    rcases (Nat.dvd_prime Nat.prime_three).mp hord with h1 | h3
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1]; norm_num)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h3]; norm_num)
  have hnorm : Subgroup.zpowers c ≤
      Subgroup.normalizer (CFSG.Open.pCoreOf 2 (K ⊔ T) : Set G) :=
    Subgroup.zpowers_le.mpr
      ((hAKT.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (K ⊔ T)))
        hcA)
  have hfact :=
    CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_centralizer_factorization
      3 Nat.prime_three (Subgroup.zpowers c) (CFSG.Open.pCoreOf 2 (K ⊔ T))
      hpgroup hcompl hnorm
  have hCbot : CFSG.Open.pCoreOf 2 (K ⊔ T) ⊓
      Subgroup.centralizer (Subgroup.zpowers c : Set G) = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [← hC]
    exact inf_le_inf_left _ (Subgroup.centralizer_le
      (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers c)))
  have hQeq : CFSG.Open.pCoreOf 2 (K ⊔ T) =
      ⁅CFSG.Open.pCoreOf 2 (K ⊔ T), Subgroup.zpowers c⁆ := by
    calc CFSG.Open.pCoreOf 2 (K ⊔ T)
        = ⁅CFSG.Open.pCoreOf 2 (K ⊔ T), Subgroup.zpowers c⁆ ⊔
          (CFSG.Open.pCoreOf 2 (K ⊔ T) ⊓
            Subgroup.centralizer (Subgroup.zpowers c : Set G)) := hfact
      _ = ⁅CFSG.Open.pCoreOf 2 (K ⊔ T), Subgroup.zpowers c⁆ ⊔ ⊥ := by rw [hCbot]
      _ = ⁅CFSG.Open.pCoreOf 2 (K ⊔ T), Subgroup.zpowers c⁆ := sup_bot_eq _
  refine le_antisymm ?_ hcomm_le
  calc CFSG.Open.pCoreOf 2 (K ⊔ T)
      = ⁅CFSG.Open.pCoreOf 2 (K ⊔ T), Subgroup.zpowers c⁆ := hQeq
    _ ≤ ⁅T, Subgroup.zpowers c⁆ := Subgroup.commutator_mono hQleT le_rfl

end Proof163U35

end CFSG.RankThree.PartTwo.Sec16
