module

public import CFSG.RankThree.PartTwo.Sec21.FF84Defs

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_normalizer_of_lt {p : ℕ} [Fact p.Prime] {P Q : Subgroup G}
    (hQ : IsPGroup p Q) (hPQ : P < Q) : ∃ x ∈ Q, x ∉ P ∧ x ∈ Nor P := by
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hlt : P.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    have : Q ≤ P := by
      intro x hx
      have : (⟨x, hx⟩ : ↥Q) ∈ P.subgroupOf Q := by rw [htop]; trivial
      exact this
    exact absurd hPQ (not_lt_of_ge this)
  have hn := normalizerCondition_of_isNilpotent (G := ↥Q) (P.subgroupOf Q) hlt
  obtain ⟨y, hy, hyn⟩ := SetLike.exists_of_lt hn
  refine ⟨y, y.2, hyn, ?_⟩
  rw [Subgroup.mem_normalizer_iff] at hy ⊢
  intro z
  constructor
  · intro hz
    exact (hy ⟨z, hPQ.le hz⟩).1 hz
  · intro hz
    have hzQ : z ∈ Q := by
      have h1 : (y : G) * z * (y : G)⁻¹ ∈ Q := hPQ.le hz
      have : z = (y : G)⁻¹ * ((y : G) * z * (y : G)⁻¹) * y := by group
      rw [this]
      exact Q.mul_mem (Q.mul_mem (Q.inv_mem y.2) h1) y.2
    exact (hy ⟨z, hzQ⟩).2 hz

theorem isSylowOf_of_normalizer {p : ℕ} [Fact p.Prime] {B D : Subgroup G} (hBD : B ≤ D)
    (hB : IsPGroup p B)
    (hN : ∀ g ∈ D, g ∈ Nor B → (∃ k : ℕ, g ^ p ^ k = 1) → g ∈ B) : IsSylowOf p B D := by
  refine ⟨hBD, hB, ?_⟩
  have hB' : IsPGroup p (B.subgroupOf D) :=
    hB.comap_of_injective D.subtype (Subgroup.subtype_injective D)
  obtain ⟨S, hS⟩ := hB'.exists_le_sylow
  have hEq : B.subgroupOf D = (S : Subgroup ↥D) := by
    by_contra hne
    have hlt : B.subgroupOf D < (S : Subgroup ↥D) := lt_of_le_of_ne hS hne
    obtain ⟨x, hxS, hxn, hxnor⟩ := exists_mem_normalizer_of_lt S.isPGroup' hlt
    have hnor : (x : G) ∈ Nor B := by
      rw [Subgroup.mem_normalizer_iff] at hxnor ⊢
      intro z
      constructor
      · intro hz
        exact (hxnor ⟨z, hBD hz⟩).1 hz
      · intro hz
        have hzD : z ∈ D := by
          have h1 : (x : G) * z * (x : G)⁻¹ ∈ D := hBD hz
          have : z = (x : G)⁻¹ * ((x : G) * z * (x : G)⁻¹) * x := by group
          rw [this]
          exact D.mul_mem (D.mul_mem (D.inv_mem x.2) h1) x.2
        exact (hxnor ⟨z, hzD⟩).2 hz
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, hxS⟩
    have hk2 : x ^ p ^ k = 1 := congrArg Subtype.val hk
    exact hxn (hN x x.2 hnor ⟨k, congrArg Subtype.val hk2⟩)
  have hnd := Sylow.not_dvd_index S
  rw [Subgroup.relIndex, hEq]
  exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hnd

theorem le_of_isSylowOf {p : ℕ} [Fact p.Prime] {B H Q : Subgroup G} (hB : IsSylowOf p B H)
    (hQH : Q ≤ H) (hQ : IsPGroup p Q) (hBQ : B ≤ Q) : Q ≤ B := by
  have h1 := Subgroup.relIndex_mul_relIndex B Q H hBQ hQH
  have hcop : Nat.Coprime p (B.relIndex Q) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro _ h1) hB.2.2
  obtain ⟨n, hn⟩ := IsPGroup.index (G := ↥Q) hQ (B.subgroupOf Q)
  have hn0 : n = 0 := by
    by_contra hn0
    have hd : p ∣ B.relIndex Q := by
      rw [Subgroup.relIndex, hn]; exact dvd_pow_self p hn0
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hcop hd
  rw [hn0, pow_zero] at hn
  exact Subgroup.relIndex_eq_one.1 hn

theorem isPGroup_zpowers {p : ℕ} [Fact p.Prime] {g : G} {k : ℕ} (hk : g ^ p ^ k = 1) :
    IsPGroup p (Subgroup.zpowers g) := by
  have hd : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Fact.out).1 hd
  exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])

theorem commute_of_sq_commute {g u : G} {k : ℕ} (hk : g ^ 3 ^ k = 1)
    (hc : Commute (g ^ 2) u) : Commute g u := by
  obtain ⟨m, hm⟩ : Odd (3 ^ k) := Odd.pow (by decide)
  have h1 : g * (g ^ 2) ^ m = 1 := by
    calc g * (g ^ 2) ^ m = g ^ (2 * m + 1) := by rw [← pow_mul, pow_succ']
      _ = 1 := by rw [← hm]; exact hk
  have : g = ((g ^ 2) ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
  rw [this]
  exact (hc.pow_left m).inv_left

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
