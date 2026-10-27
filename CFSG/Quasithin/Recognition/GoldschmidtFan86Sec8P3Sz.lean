module

public import CFSG.Quasithin.Recognition.RuTypeSz2

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Open CFSG.Quasithin Subgroup

namespace Sec8P3

variable {G : Type*} [Group G] {x w : G}

theorem conj_eq_pow_three (hx : x ^ 5 = 1) (h : w⁻¹ * x * w = x ^ 2) : w * x * w⁻¹ = x ^ 3 := by
  have h1 : (w * x * w⁻¹) ^ 2 = x := by
    rw [conj_pow, ← h]
    group
  have h5 : (w * x * w⁻¹) ^ 5 = 1 := by
    rw [conj_pow, hx]
    group
  calc w * x * w⁻¹ = (w * x * w⁻¹) ^ 6 := by rw [pow_succ _ 5, h5, one_mul]
    _ = x ^ 3 := by rw [show 6 = 2 * 3 by norm_num, pow_mul, h1]

theorem conj_inv_zpow (h : w⁻¹ * x * w = x ^ 2) (k : ℤ) : w⁻¹ * x ^ k * w = x ^ (2 * k) := by
  have h1 : (w⁻¹ * x * w) ^ k = w⁻¹ * x ^ k * w := by
    have := map_zpow (MulAut.conj w⁻¹) x k
    simpa [MulAut.conj_apply] using this.symm
  rw [← h1, h, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem conj_zpow_three (hx : x ^ 5 = 1) (h : w⁻¹ * x * w = x ^ 2) (k : ℤ) :
    w * x ^ k * w⁻¹ = x ^ (3 * k) := by
  rw [← conj_zpow, conj_eq_pow_three hx h, ← zpow_natCast, ← zpow_mul]
  norm_num

theorem closure_le_normalizer (hx : x ^ 5 = 1) (h : w⁻¹ * x * w = x ^ 2) :
    closure ({x, w} : Set G) ≤ Subgroup.normalizer (zpowers x : Set G) := by
  rw [closure_le]
  rintro g (rfl | rfl)
  · exact Subgroup.le_normalizer (mem_zpowers g)
  · rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
      exact ⟨3 * k, (conj_zpow_three hx h k).symm⟩
    · intro hy
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hy
      refine mem_zpowers_iff.2 ⟨2 * k, ?_⟩
      calc x ^ (2 * k) = g⁻¹ * x ^ k * g := (conj_inv_zpow h k).symm
        _ = y := by rw [hk]; group

theorem card_closure_pair (hx : orderOf x = 5) (hw : orderOf w = 4) (h : w⁻¹ * x * w = x ^ 2) :
    Finite ↥(closure ({x, w} : Set G)) ∧ Nat.card ↥(closure ({x, w} : Set G)) = 20 := by
  have hx5 : x ^ 5 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
  have hw4 : w ^ 4 = 1 := by rw [← hw]; exact pow_orderOf_eq_one w
  set X : Subgroup G := closure ({x, w} : Set G) with hX
  have hxX : x ∈ X := subset_closure (by simp)
  have hwX : w ∈ X := subset_closure (by simp)
  have hAX : zpowers x ≤ X := zpowers_le.2 hxX
  have hnorm : ((zpowers x).subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAX).2 (closure_le_normalizer hx5 h)
  set A' : Subgroup ↥X := (zpowers x).subgroupOf X with hA'
  set qw : ↥X ⧸ A' := QuotientGroup.mk (⟨w, hwX⟩ : ↥X) with hqw
  have hgen : ∀ (g : G) (hg : g ∈ X), (QuotientGroup.mk (⟨g, hg⟩ : ↥X) : ↥X ⧸ A') ∈
      zpowers qw := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g hg => (QuotientGroup.mk (⟨g, hg⟩ : ↥X) :
      ↥X ⧸ A') ∈ zpowers qw) ?_ ?_ ?_ ?_ hg
    · rintro g (rfl | rfl)
      · have hmem : (⟨g, hxX⟩ : ↥X) ∈ A' := by simp [hA', Subgroup.mem_subgroupOf]
        have : (QuotientGroup.mk (⟨g, hxX⟩ : ↥X) : ↥X ⧸ A') = 1 :=
          (QuotientGroup.eq_one_iff _).2 hmem
        rw [this]
        exact one_mem _
      · exact mem_zpowers _
    · exact one_mem _
    · intro a b ha hb iha ihb
      exact mul_mem iha ihb
    · intro a ha iha
      exact inv_mem iha
  have hq4 : qw ^ 4 = 1 := by
    rw [hqw, ← QuotientGroup.mk_pow]
    have : (⟨w, hwX⟩ : ↥X) ^ 4 = 1 := Subtype.ext (by simpa using hw4)
    rw [this, QuotientGroup.mk_one]
  have hqord : orderOf qw ∣ 4 := orderOf_dvd_of_pow_eq_one hq4
  have hQtop : zpowers qw = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨⟨g, hg⟩, rfl⟩ := QuotientGroup.mk_surjective q
    exact hgen g hg
  have hQcard : Nat.card (↥X ⧸ A') = orderOf qw := by
    rw [← Nat.card_zpowers, hQtop, Subgroup.card_top]
  have hAcard : Nat.card ↥A' = 5 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv, Nat.card_zpowers, hx]
  have hmul : Nat.card ↥X = Nat.card (↥X ⧸ A') * Nat.card ↥A' :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup A'
  have hqpos : 0 < orderOf qw := by
    refine Nat.pos_of_ne_zero fun h0 => ?_
    rw [h0] at hqord
    omega
  have hXpos : 0 < Nat.card ↥X := by
    rw [hmul, hQcard, hAcard]
    omega
  have hXfin : Finite ↥X := Nat.finite_of_card_ne_zero hXpos.ne'
  have hle : Nat.card ↥X ≤ 20 := by
    have : orderOf qw ≤ 4 := Nat.le_of_dvd (by norm_num) hqord
    rw [hmul, hQcard, hAcard]
    omega
  have h5 : 5 ∣ Nat.card ↥X := by
    have := Subgroup.orderOf_dvd_natCard X hxX
    rwa [hx] at this
  have h4 : 4 ∣ Nat.card ↥X := by
    have := Subgroup.orderOf_dvd_natCard X hwX
    rwa [hw] at this
  have h20 : 20 ∣ Nat.card ↥X := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h5 h4
  exact ⟨hXfin, le_antisymm hle (Nat.le_of_dvd hXpos h20)⟩

theorem nonempty_mulEquiv_sz_of_pair (hx : orderOf x = 5) (hw : orderOf w = 4)
    (h : w⁻¹ * x * w = x ^ 2) : Nonempty (↥(closure ({x, w} : Set G)) ≃* ↥(Sz 0)) := by
  obtain ⟨hfin, hcard⟩ := card_closure_pair hx hw h
  have hSzfin : Finite ↥(Sz 0) := Nat.finite_of_card_ne_zero (by rw [card_Sz_zero]; norm_num)
  have hxX : x ∈ closure ({x, w} : Set G) := subset_closure (by simp)
  have hwX : w ∈ closure ({x, w} : Set G) := subset_closure (by simp)
  let u : ↥(closure ({x, w} : Set G)) := ⟨x, hxX⟩
  let w' : ↥(closure ({x, w} : Set G)) := ⟨w⁻¹, inv_mem hwX⟩
  have hu : orderOf u = 5 := by rw [Subgroup.orderOf_mk, hx]
  have hrel : w' * u * w'⁻¹ = u ^ 2 := Subtype.ext (by simpa [u, w'] using h)
  exact RuType.nonempty_mulEquiv_of_frob20 hcard card_Sz_zero hu hrel RuType.sz_zero_frob20.1
    RuType.sz_zero_frob20.2

end Sec8P3

end CFSG.Quasithin.Fan86
