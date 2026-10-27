module

public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem commute_of_normal_of_card_dvd_three {Q : Type*} [Group Q] (A : Subgroup Q) [A.Normal]
    (hA : Nat.card A ∣ 3) {p : ℕ} (hp : Odd p) {a g : Q} (ha : a ∈ A) (hg : g ^ p = 1) :
    g * a = a * g := by
  have hfin : Finite A := Nat.finite_of_card_ne_zero fun h => by
    rw [h] at hA
    exact absurd (zero_dvd_iff.1 hA) (by norm_num)
  have hcard : Nat.card (MulAut A) ∣ 2 := by
    rcases (Nat.dvd_prime Nat.prime_three).1 hA with h1 | h3
    · have : IsCyclic A := by
        have : Subsingleton A := (Nat.card_eq_one_iff_unique.1 h1).1
        infer_instance
      rw [IsCyclic.card_mulAut, h1]
      simp
    · have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have := isCyclic_of_prime_card h3
      rw [IsCyclic.card_mulAut, h3, Nat.totient_prime Nat.prime_three]
  set c : MulAut A := MulAut.conjNormal g with hc
  have hcp : c ^ p = 1 := by rw [hc, ← map_pow, hg, map_one]
  have h1 : orderOf c ∣ p := orderOf_dvd_of_pow_eq_one hcp
  have h2 : orderOf c ∣ 2 := (orderOf_dvd_natCard c).trans hcard
  have h3 : orderOf c ∣ Nat.gcd p 2 := Nat.dvd_gcd h1 h2
  have hcop : Nat.gcd p 2 = 1 := by
    rw [Nat.gcd_comm]
    exact Nat.coprime_two_left.2 hp
  rw [hcop] at h3
  have hc1 : c = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h3)
  have h4 : (c ⟨a, ha⟩ : Q) = a := by rw [hc1]; rfl
  rw [hc, MulAut.conjNormal_apply] at h4
  rw [mul_inv_eq_iff_eq_mul] at h4
  exact h4

theorem mem_of_pow_mul_eq_one_of_index_dvd_three {G : Type*} [Group G] (I D : Subgroup G)
    [I.Normal] [D.Normal] (hidx : (I.subgroupOf D).index ∣ 3) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p ≠ 3) {d γ : G} (hd : d ∈ D) (hγ : γ ^ p = 1)
    (hdγ : (d * γ) ^ p = 1) : d ∈ I := by
  set o := QuotientGroup.mk' I with ho
  have hAnormal : (D.map o).Normal := ‹D.Normal›.map o (QuotientGroup.mk'_surjective I)
  have hcardA : Nat.card (D.map o) ∣ 3 := by
    have h1 := (Subgroup.index_ker (o.domRestrict D)).symm
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk', MonoidHom.domRestrict_range] at h1
    rw [h1]
    exact hidx
  have hao : o d ∈ D.map o := Subgroup.mem_map_of_mem o hd
  have hgp : (o γ) ^ p = 1 := by rw [← map_pow, hγ, map_one]
  have hcomm : Commute (o d) (o γ) :=
    (commute_of_normal_of_card_dvd_three (D.map o) hcardA (hp.odd_of_ne_two hp2) hao hgp).symm
  have h1 : (o d) ^ p = 1 := by
    have h2 : (o d * o γ) ^ p = 1 := by rw [← map_mul, ← map_pow, hdγ, map_one]
    rwa [hcomm.mul_pow, hgp, mul_one] at h2
  have h3 : (o d) ^ 3 = 1 := by
    have h2 := orderOf_dvd_natCard (⟨o d, hao⟩ : D.map o)
    rw [Subgroup.orderOf_mk] at h2
    exact orderOf_dvd_iff_pow_eq_one.1 (h2.trans hcardA)
  have h4 : orderOf (o d) ∣ Nat.gcd p 3 :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h3)
  rw [(Nat.coprime_primes hp Nat.prime_three).2 hp3] at h4
  have h5 : o d = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 h4)
  rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h5

theorem mem_inner_of_pow_mul_eq_one_of_index_dvd_three {C : Type*} [Group C]
    {D : Subgroup (MulAut C)} [D.Normal] (hidx : ((inner C).subgroupOf D).index ∣ 3) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p) {d γ : MulAut C} (hd : d ∈ D) (hγ : γ ^ p = 1)
    (hdγ : (d * γ) ^ p = 1) : d ∈ inner C :=
  mem_of_pow_mul_eq_one_of_index_dvd_three (inner C) D hidx hp (by omega) (by omega) hd hγ hdγ

end CFSG.RankThree.PartOne.KE
