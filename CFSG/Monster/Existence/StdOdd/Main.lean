module

public import CFSG.Monster.Existence.StdOdd.CaseB
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.Monster.Existence.StdOdd

open Subgroup

section Restrict

variable {R : Type*} [Group R]

theorem card_centralizer_subtype_dvd (M : Subgroup R) (x : M) :
    Nat.card (centralizer ({x} : Set M)) ∣ Nat.card (centralizer ({(x : R)} : Set R)) := by
  have hle : (centralizer ({x} : Set M)).map M.subtype ≤ centralizer ({(x : R)} : Set R) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ centralizer ({x} : Set M) := hy
    rw [Subgroup.mem_centralizer_iff] at hy' ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    exact congrArg Subtype.val (hy' x rfl)
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [card_map_subtype_eq] at h1

theorem CentralizerFacts.restrict (hC : CentralizerFacts R) (M : Subgroup R) :
    CentralizerFacts M where
  c5 x hx := (card_centralizer_subtype_dvd M x).trans
    (hC.c5 (x : R) (by rw [Subgroup.orderOf_coe]; exact hx))
  c7 x hx := (card_centralizer_subtype_dvd M x).trans
    (hC.c7 (x : R) (by rw [Subgroup.orderOf_coe]; exact hx))
  c11 x hx := (card_centralizer_subtype_dvd M x).trans
    (hC.c11 (x : R) (by rw [Subgroup.orderOf_coe]; exact hx))
  c13 x hx := by
    have h1 : Nat.card (centralizer ({x} : Set M)) ∣ 13 :=
      (card_centralizer_subtype_dvd M x).trans
        (dvd_of_eq (hC.c13 (x : R) (by rw [Subgroup.orderOf_coe]; exact hx)))
    have h2 : 13 ∣ Nat.card (centralizer ({x} : Set M)) := by
      rw [← hx]
      refine Subgroup.orderOf_dvd_natCard _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rfl
    exact Nat.dvd_antisymm h1 h2
  c17 x hx := (card_centralizer_subtype_dvd M x).trans
    (hC.c17 (x : R) (by rw [Subgroup.orderOf_coe]; exact hx))
  c19 x hx := (card_centralizer_subtype_dvd M x).trans
    (hC.c19 (x : R) (by rw [Subgroup.orderOf_coe]; exact hx))

theorem mem_normalizer_map_subtype {M : Subgroup R} {T : Subgroup M} {g : M}
    (hg : g ∈ normalizer (T : Set M)) :
    (g : R) ∈ normalizer ((T.map M.subtype : Subgroup R) : Set R) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro x
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact ⟨g * t * g⁻¹, (hg t).1 ht, rfl⟩
  · rintro ⟨t', ht', hx⟩
    have hxM : x = M.subtype (g⁻¹ * t' * g) := by
      have h1 : (g : R) * x * (g : R)⁻¹ = t' := hx.symm
      have h2 : x = (g : R)⁻¹ * (t' : R) * (g : R) := by
        rw [← h1]
        group
      simpa using h2
    refine ⟨g⁻¹ * t' * g, ?_, hxM.symm⟩
    refine (hg (g⁻¹ * t' * g)).2 ?_
    have h3 : g * (g⁻¹ * t' * g) * g⁻¹ = t' := by group
    rw [h3]
    exact ht'

theorem ThreeLocalFacts.restrict (hT : ThreeLocalFacts R) (M : Subgroup R) :
    ThreeLocalFacts M where
  rank3 A h3 hcomm := by
    have h := hT.rank3 (A.map M.subtype)
      (by
        rintro _ ⟨a, ha, rfl⟩
        show (M.subtype a) ^ 3 = 1
        rw [← map_pow, h3 a ha, map_one])
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hcomm a ha b hb))
    rwa [card_map_subtype_eq] at h
  syl5 T hT9 g hg := by
    have := hT.syl5 (T.map M.subtype) (by rw [card_map_subtype_eq, hT9])
      (g : R) (mem_normalizer_map_subtype hg)
    rwa [Subgroup.orderOf_coe] at this
  syl13 T hT9 g hg := by
    have := hT.syl13 (T.map M.subtype) (by rw [card_map_subtype_eq, hT9])
      (g : R) (mem_normalizer_map_subtype hg)
    rwa [Subgroup.orderOf_coe] at this
  sub7 T hT8 g hg := by
    have := hT.sub7 (T.map M.subtype) (by rw [card_map_subtype_eq, hT8])
      (g : R) (mem_normalizer_map_subtype hg)
    rwa [Subgroup.orderOf_coe] at this
  elem11 X h3 hcomm hX g hg := by
    have := hT.elem11 (X.map M.subtype)
      (by
        rintro _ ⟨a, ha, rfl⟩
        show (M.subtype a) ^ 3 = 1
        rw [← map_pow, h3 a ha, map_one])
      (by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (hcomm a ha b hb))
      (by rw [card_map_subtype_eq, hX]) (g : R) (mem_normalizer_map_subtype hg)
    rwa [Subgroup.orderOf_coe] at this

end Restrict

section Arith

theorem le_six_of_dvd {n a : ℕ} (h3 : 3 ^ a ∣ n) (hdvd : n ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19) :
    a ≤ 6 :=
  le_of_pow_dvd_mul (m := 5 ^ 2 * 7 * 11 * 19) (by norm_num)
    (by simpa only [mul_assoc] using h3.trans hdvd)

theorem bound_of_shape {n a : ℕ} (h : CaseBShape n a) (ha9 : a ≤ 9)
    (e5 : a = 9 → ¬ 5 ∣ n) (e13 : a = 9 → ¬ 13 ∣ n) (e7 : a = 8 → ¬ 7 ∣ n) (e11 : ¬ 11 ∣ n) :
    n ≤ 54463 := by
  rcases h with h | ⟨h, ha⟩ | ⟨k, hk, h, ha⟩ | ⟨k, hk, h, ha⟩ | ⟨k, hk, h, ha⟩
  · rw [h]
    calc 3 ^ a ≤ 3 ^ 9 := Nat.pow_le_pow_right (by norm_num) ha9
      _ ≤ 54463 := by norm_num
  · have d5 : 5 ∣ n := ⟨3 ^ a, by rw [h]; ring⟩
    rcases ha with rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (rw [h]; norm_num; done)
      | exact absurd d5 (e5 rfl)
  · have d7 : 7 ∣ n := ⟨3 ^ a * k, by rw [h]; ring⟩
    rcases ha with rfl | rfl | rfl <;> rcases hk with rfl | rfl
    all_goals first
      | (rw [h]; norm_num; done)
      | exact absurd d7 (e7 rfl)
  · exact absurd ⟨3 ^ a * k, by rw [h]; ring⟩ e11
  · have d13 : 13 ∣ n := ⟨3 ^ a * k, by rw [h]; ring⟩
    rcases ha with rfl | rfl | rfl <;> rcases hk with rfl | rfl
    all_goals first
      | (rw [h]; norm_num; done)
      | exact absurd d13 (e13 rfl)

theorem bound2_of_shape {n a : ℕ} (h : CaseBShape n a) (e13 : ¬ 13 ∣ n) (e11 : ¬ 11 ∣ n)
    (hdvd : n ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19) : n ≤ 9477 := by
  rcases h with h | ⟨h, ha⟩ | ⟨k, hk, h, ha⟩ | ⟨k, hk, h, ha⟩ | ⟨k, hk, h, ha⟩
  · have h2 : a ≤ 6 := le_six_of_dvd (h ▸ dvd_rfl) hdvd
    rw [h]
    calc 3 ^ a ≤ 3 ^ 6 := Nat.pow_le_pow_right (by norm_num) h2
      _ ≤ 9477 := by norm_num
  · have h2 : a ≤ 6 := le_six_of_dvd (h ▸ Dvd.intro 5 rfl) hdvd
    rw [h]
    calc 3 ^ a * 5 ≤ 3 ^ 6 * 5 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) h2)
      _ ≤ 9477 := by norm_num
  · rcases ha with rfl | rfl | rfl <;> rcases hk with rfl | rfl
    all_goals first
      | (rw [h]; norm_num; done)
      | (exfalso; rw [h] at hdvd; revert hdvd; decide)
  · exact absurd ⟨3 ^ a * k, by rw [h]; ring⟩ e11
  · exact absurd ⟨3 ^ a * k, by rw [h]; ring⟩ e13

end Arith

section Abstract

variable {G : Type*} [Group G] [Finite G]

open CFSG

theorem odd_bounds_abstract (hodd : Odd (Nat.card G))
    (hdvd : Nat.card G ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19) (hC : CentralizerFacts G)
    (hT : ThreeLocalFacts G) :
    Nat.card G ≤ 54463 ∧ (Nat.card G ∣ 3 ^ 6 * 5 ^ 2 * 7 * 11 * 19 → Nat.card G ≤ 9477) := by
  have hsolv : Group.IsSolvable G := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  by_cases hA : ∃ r : ℕ, r.Prime ∧ r ≠ 3 ∧ pCore r G ≠ ⊥
  · obtain ⟨r, hr, hr3, hne⟩ := hA
    have : Fact r.Prime := ⟨hr⟩
    have h := card_le_of_normal_subgroup hodd hdvd hC hr3 (S := pCore r G) pCore_isPGroup hne
    refine ⟨by omega, fun h2 => ?_⟩
    have h49 : ¬ 7 ^ 2 ∣ Nat.card G := fun h7 => by
      have := h7.trans h2
      revert this
      decide
    have := h.2 h49
    omega
  · push Not at hA
    obtain ⟨a, ctx, hmax⟩ := caseB_ctx hsolv hodd hdvd hC hA
    have hshape := caseB_shape ctx hsolv hmax
    have hn := ctx.normal
    have e5 : a = 9 → ¬ 5 ∣ Nat.card G := by
      intro ha h5
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 5 h5
      exact hT.syl5 (pCore 3 G) (by rw [ctx.card, ha]) g (mem_normalizer_of_normal g) hg
    have e13 : a = 9 → ¬ 13 ∣ Nat.card G := by
      intro ha h13
      have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 13 h13
      exact hT.syl13 (pCore 3 G) (by rw [ctx.card, ha]) g (mem_normalizer_of_normal g) hg
    have e7 : a = 8 → ¬ 7 ∣ Nat.card G := by
      intro ha h7
      have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 7 h7
      exact hT.sub7 (pCore 3 G) (by rw [ctx.card, ha]) g (mem_normalizer_of_normal g) hg
    have e11 : ¬ 11 ∣ Nat.card G := by
      intro h11
      have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
      obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := G) 11 h11
      exact ctx.e4_false hT (ctx.feasible11 hg) hg
    refine ⟨bound_of_shape hshape ctx.le_nine e5 e13 e7 e11, fun h2 => ?_⟩
    exact bound2_of_shape hshape
      (fun h13 => by
        have := h13.trans h2
        revert this
        decide) e11 h2

end Abstract

section Final

variable {R : Type*} [Group R] [Finite R]

omit [Finite R] in
theorem card_dvd_of_odd (hR : Nat.card R = 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19)
    (M : Subgroup R) (hM : Odd (Nat.card M)) :
    Nat.card M ∣ 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 := by
  have h1 : Nat.card M ∣ Nat.card R := Subgroup.card_subgroup_dvd_card M
  rw [hR] at h1
  exact odd_dvd_of_dvd_two_pow_mul 36 hM (by simpa only [mul_assoc] using h1)

theorem odd_bounds_of_facts
    (hR : Nat.card R = 2 ^ 36 * 3 ^ 9 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19)
    (hC : CentralizerFacts R) (hT : ThreeLocalFacts R) : StdOddBounds R :=
  ⟨fun M hM => (odd_bounds_abstract hM (card_dvd_of_odd hR M hM) (hC.restrict M)
      (hT.restrict M)).1,
    fun M hM hd => (odd_bounds_abstract hM (card_dvd_of_odd hR M hM) (hC.restrict M)
      (hT.restrict M)).2 hd⟩

end Final

end CFSG.Monster.Existence.StdOdd
