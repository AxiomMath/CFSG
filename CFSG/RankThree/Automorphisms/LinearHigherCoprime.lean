module

public import CFSG.RankThree.Automorphisms.CoprimeCyclicTools
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherLinearOuterOrder
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSLInnerInvolution

public section

namespace CFSG.RankThree.Automorphisms

open CFSG.LocalAnalysis.ComponentInitial LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (relIndex_inner_linearAutGroup_dvd)
open CFSG.ComponentClassification.UnbalancedCatalog.EvenLinearSL (mem_semilinearAutGroup_of_odd)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem sub_one_dvd_card_projectiveSL {K : Type*} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) :
    Nat.card K - 1 ∣ Nat.card (projectiveSL n K) := by
  set q := Nat.card K with hq
  have hq1 : 1 < q := Finite.one_lt_card
  have hSL := card_SL_eq (K := K) (n := n) (by omega)
  have hsplit := (scalars n K).card_eq_card_quotient_mul_card_subgroup
  have hZ := card_scalars_dvd (K := K) (n := n) (by omega)
  have hprod : (q - 1) * (q - 1) ∣ ∏ j ∈ Finset.Icc 2 n, (q ^ j - 1) := by
    have hsub : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 n := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rw [Finset.mem_Icc]
      omega
    refine dvd_trans ?_ (Finset.prod_dvd_prod_of_subset _ _ _ hsub)
    rw [Finset.prod_pair (by norm_num)]
    have h2 := Nat.pow_sub_one_dvd_pow_sub_one (x := q) (one_dvd 2)
    have h3 := Nat.pow_sub_one_dvd_pow_sub_one (x := q) (one_dvd 3)
    rw [pow_one] at h2 h3
    exact mul_dvd_mul h2 h3
  have h1 : (q - 1) * (q - 1) ∣ Nat.card (projectiveSL n K) * (q - 1) := by
    refine (hprod.trans (Dvd.intro_left _ hSL.symm)).trans ?_
    rw [hsplit]
    exact mul_dvd_mul_left _ hZ
  exact Nat.dvd_of_mul_dvd_mul_right (by omega) h1

theorem higher_linear_coprime_odd_prime_automorphism_subgroups_cyclic {K : Type} [Field K]
    [Finite K] {n : ℕ} (hn : 3 ≤ n) {p : ℕ} (hp : p.Prime) (hodd : Odd p)
    (hpT : ¬ p ∣ Nat.card (projectiveSL n K)) :
    (∀ P : Subgroup (MulAut (projectiveSL n K)), IsPGroup p P → IsCyclic P) ∧
    ∀ (E : Type*) [Group E] [IsElementaryAbelian p E], Nat.card E = p ^ 2 →
      ∀ α : E →* MulAut (projectiveSL n K), p ≤ Nat.card α.ker := by
  have : Fact p.Prime := ⟨hp⟩
  set D := linearAutGroup n K with hD
  set Es := semilinearAutGroup n K with hEs
  have hpq : Nat.Coprime (Nat.card K - 1) p :=
    ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h =>
      hpT (h.trans (sub_one_dvd_card_projectiveSL hn))).symm
  have hgen := (automorphism_generation (K := K) hn).1
  obtain ⟨hID, -, hDnorm, -, -, ⟨g, hgE, hg⟩, -⟩ := standard_outer_quotients (n := n) (K := K)
  rw [hgen] at hDnorm
  have : D.Normal := ⟨fun d hd x =>
    hDnorm.conj_mem ⟨d, Subgroup.mem_top d⟩ hd ⟨x, Subgroup.mem_top x⟩⟩
  have : IsCyclic (Es ⧸ D.subgroupOf Es) := by
    refine ⟨⟨QuotientGroup.mk ⟨g, hgE⟩, fun y => ?_⟩⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨k, hk⟩ := hg x x.2
    refine ⟨-k, ?_⟩
    change (QuotientGroup.mk (⟨g, hgE⟩ : Es) : Es ⧸ D.subgroupOf Es) ^ (-k) = QuotientGroup.mk x
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq, Subgroup.mem_subgroupOf, zpow_neg, inv_inv,
      Subgroup.coe_mul, Subgroup.coe_zpow]
    exact hk
  have hID' : inner (projectiveSL n K) ≤ D := hID
  have hDcop : Nat.Coprime (Nat.card D) p := by
    rw [← Subgroup.relIndex_mul_card (inner (projectiveSL n K)) D, inf_of_le_left hID']
    refine Nat.Coprime.mul_left ?_ (coprime_card_inner hp hpT)
    exact Nat.Coprime.coprime_dvd_left ((relIndex_inner_linearAutGroup_dvd (k := K)
      (by omega : 1 ≤ n)).trans (Nat.gcd_dvd_right _ _)) hpq
  have hcyc : ∀ P : Subgroup (MulAut (projectiveSL n K)), IsPGroup p P → IsCyclic P := by
    intro P hP
    have hPE : P ≤ Es := fun x hx => by
      obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hP) ⟨x, hx⟩
      rw [Subgroup.orderOf_mk] at hm
      exact mem_semilinearAutGroup_of_odd hn (by rw [hm]; exact hodd.pow)
    exact isCyclic_of_le_of_inf_eq_bot hPE (inf_eq_bot_of_isPGroup_of_coprime hP hDcop)
  exact ⟨hcyc, fun E _ _ hE α => le_card_ker_of_isElementaryAbelian hp hcyc hE α⟩

end CFSG.RankThree.Automorphisms
