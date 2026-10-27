module

import CFSG.LocalAnalysis.ProperTwoGeneratedCore.EscapingCaseOneQuotient
import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddKernelNormalizerTransferLift
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uh
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Config
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Layer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer
  (involution_lift_normalizing_prime_subgroup)

theorem centralizer_le_map_of_isPGroup {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime]
    (N : Subgroup X) [N.Normal] (hodd : Odd (Nat.card N)) (hNp : ¬ p ∣ Nat.card N)
    {A B : Subgroup X} (hA : IsPGroup p A)
    (hB : ∀ t : X, orderOf t = 2 → t ∈ normalizer (A : Set X) →
      ¬ IsCyclic ↥(A ⊓ centralizer ({t} : Set X)) → centralizer ({t} : Set X) ≤ B)
    {y : X ⧸ N} (hy : orderOf y = 2)
    (hyA : y ∈ normalizer ((A.map (QuotientGroup.mk' N) : Subgroup (X ⧸ N)) : Set (X ⧸ N)))
    (hnc : ¬ IsCyclic ↥(A.map (QuotientGroup.mk' N) ⊓ centralizer ({y} : Set (X ⧸ N)))) :
    centralizer ({y} : Set (X ⧸ N)) ≤ B.map (QuotientGroup.mk' N) := by
  have hker : (QuotientGroup.mk' N).ker = N := QuotientGroup.ker_mk' N
  have hyi : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution y := by
    refine ⟨fun h1 => ?_, ?_⟩
    · rw [h1, orderOf_one] at hy
      exact absurd hy (by norm_num)
    · rw [← hy]
      exact pow_orderOf_eq_one y
  obtain ⟨t, htA, hti, rfl⟩ := involution_lift_normalizing_prime_subgroup
    (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) p Fact.out (by rw [hker]; exact hodd)
    (by rw [hker]; exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hNp) A hA hyi hyA
  have ht : orderOf t = 2 := orderOf_eq_prime hti.2 hti.1
  have hinj := CFSG.OrderReductions.ThompsonQuotient.prime_subgroup_injective_of_coprime_kernel p
    (QuotientGroup.mk' N) (by rw [hker]; exact hNp) A hA
  have hle : A.map (QuotientGroup.mk' N) ⊓
      centralizer ({QuotientGroup.mk' N t} : Set (X ⧸ N)) ≤
        (A ⊓ centralizer ({t} : Set X)).map (QuotientGroup.mk' N) := by
    rintro _ ⟨⟨a, ha, rfl⟩, hac⟩
    have hcomm := mem_centralizer_singleton_iff.mp hac
    have hta : t * a * t⁻¹ ∈ A := (mem_normalizer_iff.mp htA a).mp ha
    have himg : QuotientGroup.mk' N (t * a * t⁻¹) = QuotientGroup.mk' N a := by
      rw [map_mul, map_mul, map_inv, ← hcomm, mul_inv_cancel_right]
    have hfix : t * a * t⁻¹ = a := congrArg Subtype.val (hinj (a₁ := ⟨_, hta⟩) (a₂ := ⟨a, ha⟩)
      (Subtype.ext himg))
    exact ⟨a, ⟨ha, mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hfix).symm⟩, rfl⟩
  have hncA : ¬ IsCyclic ↥(A ⊓ centralizer ({t} : Set X)) := by
    intro hcyc
    haveI : IsCyclic ↥((A ⊓ centralizer ({t} : Set X)).map (QuotientGroup.mk' N)) :=
      isCyclic_of_surjective ((QuotientGroup.mk' N).subgroupMap _)
        ((QuotientGroup.mk' N).subgroupMap_surjective _)
    exact hnc (Subgroup.isCyclic_of_le hle)
  rw [← CFSG.ProperTwoGeneratedCore.Assembly.map_centralizer_eq hodd ht]
  exact Subgroup.map_mono (hB t ht htA hncA)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem centralizer_le_of_not_isCyclic (k : Sec7Core4 G) {A : Subgroup G} (hAM : A ≤ k.M)
    (hA : IsPGroup k.p A) {t : G} (ht : orderOf t = 2)
    (hnc : ¬ IsCyclic ↥(A ⊓ centralizer ({t} : Set G))) :
    centralizer ({t} : Set G) ≤ k.M := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  obtain ⟨E, hER, hEel, hEcard⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22u_exists_elemAbelian_sq k.prime k.odd
      (hA.to_le inf_le_left) hnc
  have hCN := CFSG.RankThree.PartOne.StrongP.centralizer_singleton_le_normalizer_zpowers t
  have hrank : 2 ≤ CFSG.Open.pRank k.p (normalizer ((zpowers t : Subgroup G) : Set G) ⊓ k.M) :=
    CFSG.SectionRank.le_pRank k.prime.one_lt
      (le_inf (hER.trans (inf_le_right.trans hCN)) (hER.trans (inf_le_left.trans hAM))) hEel
      hEcard
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    exact absurd ht (by norm_num)
  have h2 : IsPGroup 2 ↥(zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  exact hCN.trans (k.huniq _ (zpowers_ne_bot.2 ht1) h2 hrank)

theorem centralizer_le_of_isPGroup_of_not_isCyclic (k : Sec7Core4 G) {H : Subgroup G}
    (hH : Config k H) {A : Subgroup G} (hAH : A ≤ H ⊓ k.M) (hA : IsPGroup k.p A)
    {y : ↥H ⧸ CFSG.pPrimeCore k.p ↥H} (hy : orderOf y = 2)
    (hyA : y ∈ normalizer (((A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) :
      Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)))
    (hnc : ¬ IsCyclic ↥((A.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ⊓
      centralizer ({y} : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)))) :
    centralizer ({y} : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≤
      ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  refine centralizer_le_map_of_isPGroup (CFSG.pPrimeCore k.p ↥H)
    (k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank)
    ((k.prime.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (p := k.p) (G := ↥H)))
    hA.comap_subtype ?_ hy hyA hnc
  intro t ht _ hnct
  have hle : (A.subgroupOf H ⊓ centralizer ({t} : Set ↥H)).map H.subtype ≤
      A ⊓ centralizer ({(t : G)} : Set G) := by
    rintro _ ⟨a, ⟨haA, hat⟩, rfl⟩
    exact ⟨haA, mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hat))⟩
  have hncG : ¬ IsCyclic ↥(A ⊓ centralizer ({(t : G)} : Set G)) := by
    intro hcyc
    have hcyc' : IsCyclic ↥((A.subgroupOf H ⊓ centralizer ({t} : Set ↥H)).map H.subtype) :=
      Subgroup.isCyclic_of_le hle
    exact hnct ((Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).isCyclic.mpr
      hcyc')
  have hCM := k.centralizer_le_of_not_isCyclic (hAH.trans inf_le_right) hA
    ((Subgroup.orderOf_coe t).trans ht) hncG
  intro c hc
  exact mem_subgroupOf.mpr ⟨c.2, hCM (mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc)))⟩

theorem centralizer_le_of_not_isCyclic_inf_fstar (k : Sec7Core4 G) {H : Subgroup G}
    (hH : Config k H) {P : Subgroup G} (hPH : P ≤ H ⊓ k.M) (hP : IsPGroup k.p P)
    {y : ↥H ⧸ CFSG.pPrimeCore k.p ↥H} (hy : orderOf y = 2)
    (hyQ : y ∈ normalizer (((P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ⊓
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) :
        Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)))
    (hnc : ¬ IsCyclic ↥((P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ⊓
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) ⊓
        centralizer ({y} : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)))) :
    centralizer ({y} : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≤
      ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) := by
  have hF : (fstarPreimage k.p H).subgroupOf H =
      (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H)).comap
        (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) :=
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _
  have hmap : ((P ⊓ fstarPreimage k.p H).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) =
        (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ⊓
          CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) := by
    rw [show (P ⊓ fstarPreimage k.p H).subgroupOf H =
        P.subgroupOf H ⊓ (fstarPreimage k.p H).subgroupOf H from Subgroup.comap_inf _ _ _, hF,
      Subgroup.map_inf_comap]
  refine k.centralizer_le_of_isPGroup_of_not_isCyclic hH (A := P ⊓ fstarPreimage k.p H)
    (inf_le_left.trans hPH) (hP.to_le inf_le_left) hy ?_ ?_
  · rw [hmap]
    exact hyQ
  · rw [hmap]
    exact hnc

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
