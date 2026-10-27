module

public import Mathlib.GroupTheory.IsPerfect
import CFSG.RankThree.PartTwo.Sec5.Bender.Core
import CFSG.GroupTheory.FrobeniusNormalComplement
import CFSG.LocalAnalysis.SectionRank.Ccomm.FrattiniAut

public section

namespace CFSG.RankThree.PartOne

theorem exists_pow_eq_one_not_mem_center_of_isPerfect {p : ℕ} [hpf : Fact p.Prime] (hp2 : p ≠ 2)
    {Z : Type} [Group Z] [Finite Z] (hZp : Group.IsPerfect Z) (hZ3 : p ∣ Nat.card Z) :
    ∃ e : Z, e ^ p = 1 ∧ e ∉ Subgroup.center Z := by
  by_contra hcon
  push Not at hcon
  have hfrob : ∀ Q : Subgroup Z, IsPGroup p Q →
      IsPGroup p (Subgroup.normalizer (Q : Set Z) ⧸
        (Subgroup.centralizer (Q : Set Z)).subgroupOf (Subgroup.normalizer (Q : Set Z))) := by
    intro Q hQ
    by_cases hQ1 : Q = ⊥
    · subst hQ1
      have htop : (Subgroup.centralizer ((⊥ : Subgroup Z) : Set Z)).subgroupOf
          (Subgroup.normalizer ((⊥ : Subgroup Z) : Set Z)) = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Subgroup.coe_bot, Set.mem_singleton_iff] at hy
        rw [hy, one_mul, mul_one]
      exact IsPGroup.of_card (n := 0) (by
        rw [pow_zero, ← Subgroup.index_eq_card, htop, Subgroup.index_top])
    · obtain ⟨D, -, -, hDexp, -, hkey⟩ :=
        CFSG.RankThree.PartTwo.Sec5.Bender.exists_critical_faithful (p := p) hp2 hQ hQ1
      have hDZ : ∀ K : Subgroup Z, K ≤ Subgroup.centralizer (D : Set Z) := by
        intro K k _
        rw [Subgroup.mem_centralizer_iff]
        intro d hd
        exact (Subgroup.mem_center_iff.mp (hcon d (hDexp d hd)) k).symm
      refine CFSG.SectionRank.Ccomm.isPGroup_of_forall_prime_orderOf fun x ℓ hℓ hx => ?_
      by_contra hℓ3
      obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
      have hg0 : orderOf g ≠ 0 := (orderOf_pos g).ne'
      obtain ⟨b, m, hm3, hbm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hg0 p hpf.out.ne_one
      have hmdvd : m ∣ orderOf g := ⟨p ^ b, by rw [hbm, mul_comm]⟩
      have hm0 : 0 < m := Nat.pos_of_ne_zero (fun h => hm3 (by rw [h]; exact dvd_zero p))
      have hdiv : orderOf g / m = p ^ b := by
        rw [hbm, Nat.mul_div_cancel _ hm0]
      have hord : orderOf (g ^ (p ^ b)) = m := by
        rw [← hdiv]
        exact orderOf_pow_orderOf_div hg0 hmdvd
      set h := g ^ (p ^ b) with hh
      set K := Subgroup.zpowers ((h : Subgroup.normalizer (Q : Set Z)) : Z) with hK
      have hK3 : ¬ p ∣ Nat.card K := by
        rw [hK, Nat.card_zpowers, Subgroup.orderOf_coe, hord]
        exact hm3
      have hKN : K ≤ Subgroup.normalizer (Q : Set Z) := by
        rw [hK, Subgroup.zpowers_le]
        exact h.2
      have hKC := hkey K hK3 hKN (hDZ K)
      have hhC : ((h : Subgroup.normalizer (Q : Set Z)) : Z) ∈ Subgroup.centralizer (Q : Set Z) :=
        hKC (Subgroup.mem_zpowers _)
      have h1 : QuotientGroup.mk' _ h = (1 : Subgroup.normalizer (Q : Set Z) ⧸
          (Subgroup.centralizer (Q : Set Z)).subgroupOf (Subgroup.normalizer (Q : Set Z))) := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact Subgroup.mem_subgroupOf.mpr hhC
      rw [hh, map_pow] at h1
      have h2 : orderOf (QuotientGroup.mk' _ g : Subgroup.normalizer (Q : Set Z) ⧸
          (Subgroup.centralizer (Q : Set Z)).subgroupOf (Subgroup.normalizer (Q : Set Z))) ∣
            p ^ b := orderOf_dvd_of_pow_eq_one h1
      rw [hx] at h2
      have h3 : ℓ ∣ p := hℓ.dvd_of_dvd_pow h2
      exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ hpf.out).mp h3)
  obtain ⟨N, hNn, hNcop, k, hk⟩ :=
    ((CFSG.GroupTheory.frobenius_normal_p_complement p).1).mpr hfrob
  have hq3 : IsPGroup p (Z ⧸ N) := IsPGroup.of_card (n := k) (by
    rw [← Subgroup.index_eq_card, hk])
  have hqp : Group.IsPerfect (Z ⧸ N) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N)
  have hNtop : N = ⊤ := by
    by_contra hne
    have : Nontrivial (Z ⧸ N) := QuotientGroup.nontrivial_iff.mpr hne
    have : Group.IsNilpotent (Z ⧸ N) := hq3.isNilpotent
    exact Group.IsPerfect.not_isSolvable (Z ⧸ N) inferInstance
  rw [hNtop, Subgroup.card_top] at hNcop
  exact (Nat.Prime.coprime_iff_not_dvd hpf.out).mp hNcop.symm hZ3

end CFSG.RankThree.PartOne
