module


public import CFSG.RankThree.PartOne.KLC.PRankTwo
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.S11d.FixedFacts

public section

namespace CFSG.RankThree.PartOne.KLCE

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne

section Rank

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_of_pRank_one {p : ℕ} (hp : p.Prime) (hpr : CFSG.pRank p G = 1)
    {A : Subgroup G} {x : G} (hx : orderOf x = p) (hxA : ∀ a ∈ A, a * x = x * a)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥A)) : ¬ p ∣ Nat.card ↥A := by
  intro hdvd
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨e', he'⟩ := exists_prime_orderOf_dvd_card' p hdvd
  set e : G := (e' : G) with hedef
  have heo : orderOf e = p := by rw [hedef, Subgroup.orderOf_coe]; exact he'
  have hep : e ^ p = 1 := by rw [← heo]; exact pow_orderOf_eq_one e
  have hxp : x ^ p = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hcomm : Commute e x := hxA e e'.2
  have hind : ∀ i j : ℤ, e ^ i * x ^ j = 1 → (p : ℤ) ∣ i ∧ (p : ℤ) ∣ j := by
    intro i j hij
    have h1 : e ^ i = (x ^ j)⁻¹ := eq_inv_of_mul_eq_one_left hij
    by_cases hi : (p : ℤ) ∣ i
    · refine ⟨hi, ?_⟩
      have h2 : e ^ i = 1 := by
        obtain ⟨k, rfl⟩ := hi
        rw [zpow_mul, zpow_natCast, hep, one_zpow]
      rw [h2] at h1
      have := orderOf_dvd_iff_zpow_eq_one.2 (inv_eq_one.1 h1.symm)
      rwa [hx] at this
    · exfalso
      by_cases hj : (p : ℤ) ∣ j
      · have h2 : x ^ j = 1 := by
          obtain ⟨k, rfl⟩ := hj
          rw [zpow_mul, zpow_natCast, hxp, one_zpow]
        rw [h2, inv_one] at h1
        have := orderOf_dvd_iff_zpow_eq_one.2 h1
        rw [heo] at this
        exact hi this
      · have hxj : x ^ j ∈ A := by
          have : (x ^ j)⁻¹ ∈ A := by
            rw [← h1]
            exact A.zpow_mem e'.2 i
          simpa using A.inv_mem this
        have hxz : x ∈ Subgroup.zpowers (x ^ j) :=
          CFSG.RankThree.PartOne.FieldFix.mem_zpowers_zpow_of_pow_eq_one hp hxp hj
        have hxmem : x ∈ A := (Subgroup.zpowers_le.2 hxj) hxz
        have hZx : (⟨x, hxmem⟩ : A) ∈ Subgroup.center ↥A := by
          rw [Subgroup.mem_center_iff]
          intro a
          exact Subtype.ext (hxA a a.2)
        have h3 : orderOf (⟨⟨x, hxmem⟩, hZx⟩ : Subgroup.center ↥A) = p := by
          rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hx]
        exact hZ (h3 ▸ _root_.orderOf_dvd_natCard (⟨⟨x, hxmem⟩, hZx⟩ : Subgroup.center ↥A))
  have h2 := KLC.two_le_pRank_of_two_commuting hp hcomm hep hxp hind
  omega

end Rank

section Outer

variable {G : Type} [Group G]

theorem not_inner_of_moved {p : ℕ} (hp : p.Prime) {α : MulAut G} (hα : α ^ p = 1) {A : Subgroup G}
    [Finite ↥A] (hA : ∀ g ∈ A, α g ∈ A) (hdvd : ¬ p ∣ Nat.card ↥A)
    (hmove : ∃ g ∈ A, α g ≠ g) : ∀ e ∈ A, ¬ ∀ g ∈ A, α g = e * g * e⁻¹ := by
  intro e he hall
  obtain ⟨g₀, hg₀, hne⟩ := hmove
  have hiter : ∀ (j : ℕ) (g : G), g ∈ A → (α ^ j) g = e ^ j * g * (e ^ j)⁻¹ := by
    intro j
    induction j with
    | zero => intro g _; simp
    | succ j ih =>
      intro g hg
      rw [pow_succ, MulAut.mul_apply, ih (α g) (hA g hg), hall g hg]
      group
  have hcentral : ∀ g ∈ A, Commute (e ^ p) g := by
    intro g hg
    have h1 := hiter p g hg
    rw [hα, MulAut.one_apply] at h1
    exact (eq_mul_inv_iff_mul_eq.1 h1).symm
  have hord : ¬ p ∣ orderOf e := fun h => hdvd (h.trans (by
    have := orderOf_dvd_natCard (⟨e, he⟩ : ↥A)
    rwa [Subgroup.orderOf_mk] at this))
  have hcop : Nat.Coprime p (orderOf e) := (Nat.Prime.coprime_iff_not_dvd hp).2 hord
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.2 hcop
  have hepow : e = (e ^ p) ^ u := by
    have h1 : e ^ (u * (p : ℤ) + v * (orderOf e : ℤ)) = e := by rw [huv, zpow_one]
    rw [zpow_add, mul_comm u (p : ℤ), mul_comm v (orderOf e : ℤ), zpow_mul, zpow_mul, zpow_natCast,
      zpow_natCast, pow_orderOf_eq_one, one_zpow, mul_one] at h1
    exact h1.symm
  have hc : Commute e g₀ := by
    have := (hcentral g₀ hg₀).zpow_left u
    rwa [← hepow] at this
  exact hne (by rw [hall g₀ hg₀, hc.eq, mul_inv_cancel_right])

theorem component_outer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hpr : CFSG.pRank p G = 1) {x : G} (hx : orderOf x = p) {α : MulAut G} (hα : α ^ p = 1)
    {Q : Subgroup G} (hQx : ∀ y ∈ Q, y * x = x * y) (hQα : ∀ g ∈ Q, α g ∈ Q) {n : ℕ} (hn0 : 0 < n)
    (hnp : n < p) (hZ : ∀ z ∈ Subgroup.center ↥Q, z ^ n = 1)
    (hmove : ∃ g ∈ Q, α g ≠ g) : ∀ e ∈ Q, ¬ ∀ g ∈ Q, α g = e * g * e⁻¹ := by
  have : Fact p.Prime := ⟨hp⟩
  have hZd : ¬ p ∣ Nat.card (Subgroup.center ↥Q) := by
    intro hdvd
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center ↥Q) p hdvd
    have h1 : (z : ↥Q) ^ n = 1 := hZ z z.2
    have h2 : (z ^ n : Subgroup.center ↥Q) = 1 := Subtype.ext h1
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hz] at this
    exact absurd (Nat.le_of_dvd hn0 this) (by omega)
  exact not_inner_of_moved hp hα hQα (not_dvd_card_of_pRank_one hp hpr hx hQx hZd) hmove

end Outer

section Odd

theorem odd_index_of_sq_mem {X : Type} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (h : ∀ g : X, g ^ 2 ∈ N → g ∈ N) : Odd N.index := by
  by_contra hodd
  have heven : 2 ∣ N.index := by
    rcases Nat.even_or_odd N.index with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  rw [Subgroup.index_eq_card] at heven
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨q, hq⟩ := exists_prime_orderOf_dvd_card' (G := X ⧸ N) 2 heven
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have h2 : (g : X ⧸ N) ^ 2 = 1 := by rw [← hq]; exact pow_orderOf_eq_one _
  have hg2 : g ^ 2 ∈ N := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact h2
  have hg : g ∈ N := h g hg2
  have h1 : (g : X ⧸ N) = 1 := (QuotientGroup.eq_one_iff g).2 hg
  rw [h1, orderOf_one] at hq
  omega


end Odd

end CFSG.RankThree.PartOne.KLCE
