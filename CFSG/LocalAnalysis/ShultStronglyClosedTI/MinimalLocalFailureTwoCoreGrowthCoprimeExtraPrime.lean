module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeCyclicProduct
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthCoprimeTwoPower

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime

universe u

theorem two_group_root_scalar_order_data
    {G : Type u} [Group G] [Finite G] (M Q X : Subgroup G)
    (hM : IsPGroup 2 M) (hQM : Q ≤ M)
    (hXcard : Nat.card X = Nat.card Q - 1) :
    ∃ e : ℕ, 0 < e ∧ Nat.card Q = 2 ^ e ∧ Even (Nat.card Q) ∧
      Odd (Nat.card X) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ : IsPGroup 2 Q :=
    hM.of_injective (Subgroup.inclusion hQM) (Subgroup.inclusion_injective hQM)
  obtain ⟨e, hQcard⟩ := hQ.exists_card_eq
  have he : 0 < e := by
    by_contra h
    have he0 : e = 0 := by omega
    have hXpos := Nat.card_pos (α := X)
    rw [hXcard, hQcard, he0] at hXpos
    norm_num at hXpos
  have hQeven : Even (Nat.card Q) := by
    rw [hQcard]
    exact Nat.even_pow.mpr ⟨by decide, ne_of_gt he⟩
  have hXodd : Odd (Nat.card X) := by
    rw [hXcard]
    exact Nat.Even.sub_odd (Nat.card_pos (α := Q)) hQeven odd_one
  exact ⟨e, he, hQcard, hQeven, hXodd⟩

theorem scalar_centralizer_extra_prime_cubic_data
    {G : Type u} [Group G] [Finite G] (M Q X J : Subgroup G)
    [(Q.subgroupOf M).Normal] [Subgroup.Normalizes X M] [Subgroup.Normalizes J M]
    [IsCyclic X] (hM : IsPGroup 2 M) (hQM : Q ≤ M) (hQproper : ¬ M ≤ Q)
    (hInv : ∀ m : G, m ∈ M → orderOf m = 2 → m ∈ Q)
    (hXcard : Nat.card X = Nat.card Q - 1)
    (hXQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hJQ : J ≤ Subgroup.normalizer (Q : Set G))
    (hJX : J ≤ Subgroup.centralizer (X : Set G)) (hdis : Disjoint X J)
    (hJfixQ : ∀ y : G, y ∈ J → ∀ m : G, m ∈ Q → y * m * y⁻¹ = m)
    (hscalar : ∀ x : G, x ∈ X → x ≠ 1 →
      ∀ m : G, m ∈ M → m ∈ Q → x * m * x⁻¹ = m → m = 1)
    (hJkernel : ∀ y : G, y ∈ J → y ≠ 1 → Odd (orderOf y) →
      ∀ m : G, m ∈ M → y * m * y⁻¹ = m → m ∈ Q)
    {p : ℕ} (hp : p.Prime) (hpJ : p ∣ Nat.card J)
    (hpPlus : p ∣ Nat.card Q + 1) :
    Nat.Coprime (Nat.card X) (Nat.card J) ∧ Odd p ∧ ¬ p ∣ Nat.card Q - 1 ∧
      ∃ y : G, y ∈ J ∧ orderOf y = p ∧
        IsCyclic (X ⊔ Subgroup.zpowers y : Subgroup G) ∧
        Nat.card (X ⊔ Subgroup.zpowers y : Subgroup G) = p * (Nat.card Q - 1) ∧
        p * (Nat.card Q - 1) ∣ Nat.card (M ⧸ Q.subgroupOf M) - 1 ∧
        ∃ e d : ℕ, Nat.card Q = 2 ^ e ∧ Nat.card (M ⧸ Q.subgroupOf M) = 2 ^ d ∧
          0 < e ∧ 0 < d ∧ e ∣ d ∧ 2 * e ≤ d ∧ Nat.card Q ^ 3 ≤ Nat.card M := by
  obtain ⟨e, he, hQcard, hQeven, hXodd⟩ :=
    two_group_root_scalar_order_data M Q X hM hQM hXcard
  have hcop : Nat.Coprime (Nat.card X) (Nat.card J) :=
    scalar_centralizer_orders_coprime M Q X J hM hQproper hInv hXodd hXQ hJQ
      hJX hdis hJfixQ hscalar hJkernel
  have hpOdd : Odd p := Odd.of_dvd_nat hQeven.add_one hpPlus
  have hnot : ¬ p ∣ Nat.card Q - 1 := by
    intro h
    have hpX : p ∣ Nat.card X := by simpa only [hXcard] using h
    exact hp.ne_one ((hcop.of_dvd_left hpX).eq_one_of_dvd hpJ)
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := J) p hpJ
  have hyG : orderOf (y : G) = p := by simpa only [orderOf_submonoid] using hy
  have hyOdd : Odd (orderOf (y : G)) := by rw [hyG]; exact hpOdd
  obtain ⟨hEcyc, hEcard, hdiv⟩ :=
    scalar_centralizer_cyclic_product_card_divisor M Q X J hM hQproper hInv hXodd
      hXQ hJQ hJX hdis hJfixQ hscalar hJkernel (y : G) y.property hyOdd
  have hdiv' : p * (Nat.card Q - 1) ∣ Nat.card (M ⧸ Q.subgroupOf M) - 1 := by
    simpa only [hyG, hXcard] using hdiv
  have hQMcard : Nat.card (Q.subgroupOf M) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQM).toEquiv
  have hQMproper : Q.subgroupOf M ≠ ⊤ := by
    intro h
    exact hQproper (Subgroup.subgroupOf_eq_top.mp h)
  obtain ⟨d, hdcard, hd, hexp, hdouble, hlower⟩ :=
    two_group_card_cube_le_of_extra_prime_divisor hM (Q.subgroupOf M) hQMproper he
      (by simpa only [hQMcard] using hQcard)
      (by simpa only [hQMcard] using hdiv')
      (by simpa only [hQMcard] using hnot)
  refine ⟨hcop, hpOdd, hnot, (y : G), y.property, hyG, hEcyc, ?_, hdiv',
    e, d, hQcard, hdcard, he, hd, hexp, hdouble, ?_⟩
  · simpa only [hyG, hXcard] using hEcard
  · simpa only [hQMcard] using hlower

end CFSG.ShultStronglyClosedTI.TwoCoreGrowthCoprime
