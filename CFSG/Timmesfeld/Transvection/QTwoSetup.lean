module

public import CFSG.Fischer.Classification.Skeleton
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Timmesfeld.Transvection.Defs

public section

namespace CFSG.Timmesfeld.Transvection.QTwo

open CFSG.Timmesfeld.ARS CFSG.Blueprint.Fischer

variable {H : Type} [Group H]

theorem eq_one_or_eq_of_mem_zpowers {x y : H} (hx : x * x = 1) (hy : y ∈ Subgroup.zpowers x) :
    y = 1 ∨ y = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  have h2 : x ^ (2 : ℤ) = 1 := by rw [zpow_two, hx]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem eq_zpowers_of_card_eq_two {X : Subgroup H} (hX : Nat.card X = 2) {x : H} (hx : x ∈ X)
    (hx1 : x ≠ 1) : X = Subgroup.zpowers x := by
  have hfin : Finite X := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hdvd : orderOf x ∣ 2 := by
    rw [← hX, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  have hord : orderOf x = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hx1
    · exact h
  refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hx) ?_).symm
  rw [hX, Nat.card_zpowers, hord]

theorem card_zpowers_eq_two {x : H} (hx : x * x = 1) (hx1 : x ≠ 1) :
    Nat.card (Subgroup.zpowers x) = 2 := by
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [sq, hx]) hx1

theorem conjSub_zpowers {G : Type*} [Group G] (x g : G) :
    conjSub (Subgroup.zpowers x) g = Subgroup.zpowers (g * x * g⁻¹) := by
  rw [conjSub, MonoidHom.map_zpowers]
  rfl

theorem commuting_zpowers_iff {x y : H} :
    Commuting (Subgroup.zpowers x) (Subgroup.zpowers y) ↔ x * y = y * x := by
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x) y (Subgroup.mem_zpowers y)
  · intro h a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
    obtain ⟨l, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_zpow h k l)

theorem mul_mul_eq_of_opposite {x y : H} (hx : x * x = 1) (hy : y * y = 1) (hx1 : x ≠ 1)
    (h : Opposite (Subgroup.zpowers x) (Subgroup.zpowers y)) : y * x * y = x * y * x := by
  obtain ⟨b, hb, hb1, hbe⟩ := h.2.1 x (Subgroup.mem_zpowers x) hx1
  have hby : b = y := (eq_one_or_eq_of_mem_zpowers hy hb).resolve_left hb1
  subst hby
  rw [conjSub_zpowers, conjSub_zpowers] at hbe
  have hyinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hy
  have hxinv : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx
  rw [hyinv, hxinv] at hbe
  have hmem : b * x * b ∈ Subgroup.zpowers (x * b * x) := hbe ▸ Subgroup.mem_zpowers _
  have hsq : (x * b * x) * (x * b * x) = 1 := by
    simp only [mul_assoc]
    rw [← mul_assoc x x, hx, one_mul, ← mul_assoc b b, hy, one_mul, hx]
  rcases eq_one_or_eq_of_mem_zpowers hsq hmem with h1 | h1
  · exfalso
    apply hx1
    calc x = b * (b * x * b) * b := by
          simp only [← mul_assoc, hy, one_mul]
          rw [mul_assoc, hy, mul_one]
      _ = 1 := by rw [h1, mul_one, hy]
  · exact h1

theorem orderOf_mul_eq_three_of_braid {x y : H} (hx : x * x = 1) (hy : y * y = 1) (hxy : x ≠ y)
    (h : y * x * y = x * y * x) : orderOf (x * y) = 3 := by
  apply orderOf_eq_prime
  · calc (x * y) ^ 3 = (x * y * x) * (y * x * y) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = (y * x * y) * (y * x * y) := by rw [h]
      _ = 1 := by
          simp only [mul_assoc]
          rw [← mul_assoc y y, hy, one_mul, ← mul_assoc x x, hx, one_mul, hy]
  · intro h1
    apply hxy
    calc x = x * (y * y) := by rw [hy, mul_one]
      _ = (x * y) * y := by rw [mul_assoc]
      _ = y := by rw [h1, one_mul]

section Class

variable {Δ : Set (Subgroup H)}

theorem card_eq_two (hΔ : IsTransvectionClass Δ) {A : Subgroup H} (hA : A ∈ Δ)
    (h2 : Nat.card A = 2) {X : Subgroup H} (hX : X ∈ Δ) : Nat.card X = 2 :=
  (hΔ.root.card_eq hX hA).trans h2

variable (hΔ : IsTransvectionClass Δ) (hcard : ∀ X ∈ Δ, Nat.card X = 2)
include hΔ hcard

theorem mem_iff_exists_zpowers (X : Subgroup H) :
    X ∈ Δ ↔ ∃ x ∈ rootElts Δ, X = Subgroup.zpowers x := by
  constructor
  · intro hX
    obtain ⟨x, hx, hx1⟩ := hΔ.root.exists_ne_one hX
    exact ⟨x, ⟨X, hX, hx, hx1⟩, eq_zpowers_of_card_eq_two (hcard X hX) hx hx1⟩
  · rintro ⟨x, ⟨Y, hY, hxY, hx1⟩, rfl⟩
    rwa [← eq_zpowers_of_card_eq_two (hcard Y hY) hxY hx1]

theorem zpowers_mem {x : H} (hx : x ∈ rootElts Δ) : Subgroup.zpowers x ∈ Δ :=
  (mem_iff_exists_zpowers hΔ hcard _).2 ⟨x, hx, rfl⟩

omit hcard in
theorem mul_self_of_mem {x : H} (hx : x ∈ rootElts Δ) : x * x = 1 := by
  obtain ⟨X, hX, hxX, -⟩ := hx
  exact hΔ.root.mul_self X hX x hxX

omit hΔ hcard in
theorem ne_one_of_mem {x : H} (hx : x ∈ rootElts Δ) : x ≠ 1 := by
  obtain ⟨X, -, -, hx1⟩ := hx
  exact hx1

omit hcard in
theorem eq_of_zpowers_eq {x y : H} (hx : x ∈ rootElts Δ) (hy : y ∈ rootElts Δ)
    (h : Subgroup.zpowers x = Subgroup.zpowers y) : x = y := by
  have hmem : x ∈ Subgroup.zpowers y := h ▸ Subgroup.mem_zpowers x
  exact (eq_one_or_eq_of_mem_zpowers (mul_self_of_mem hΔ hy) hmem).resolve_left
    (ne_one_of_mem hx)

theorem rootElts_eq_isConj {x₀ : H} (hx₀ : x₀ ∈ rootElts Δ) :
    rootElts Δ = {x | IsConj x₀ x} := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg⟩ := hΔ.root.exists_conjSub_eq (zpowers_mem hΔ hcard hx₀) (zpowers_mem hΔ hcard hx)
    rw [conjSub_zpowers] at hg
    have hxm : x ∈ Subgroup.zpowers (g * x₀ * g⁻¹) := hg ▸ Subgroup.mem_zpowers x
    have hsq : (g * x₀ * g⁻¹) * (g * x₀ * g⁻¹) = 1 := by
      simp only [mul_assoc, inv_mul_cancel_left]
      rw [← mul_assoc x₀ x₀, mul_self_of_mem hΔ hx₀, one_mul, mul_inv_cancel]
    rcases eq_one_or_eq_of_mem_zpowers hsq hxm with h1 | h1
    · exact absurd h1 (ne_one_of_mem hx)
    · exact isConj_iff.2 ⟨g, h1.symm⟩
  · intro hx
    obtain ⟨g, rfl⟩ := isConj_iff.1 hx
    have hmem : Subgroup.zpowers (g * x₀ * g⁻¹) ∈ Δ := by
      rw [← conjSub_zpowers]
      exact hΔ.root.conjSub_mem (zpowers_mem hΔ hcard hx₀) g
    refine (mem_iff_exists_zpowers hΔ hcard _).1 hmem |>.elim fun y ⟨hy, hyeq⟩ => ?_
    have hy' : g * x₀ * g⁻¹ ∈ Subgroup.zpowers y := hyeq ▸ Subgroup.mem_zpowers _
    rcases eq_one_or_eq_of_mem_zpowers (mul_self_of_mem hΔ hy) hy' with h1 | h1
    · exfalso
      apply ne_one_of_mem hx₀
      have : x₀ = g⁻¹ * (g * x₀ * g⁻¹) * g := by group
      rw [this, h1, mul_one, inv_mul_cancel]
    · rw [h1]
      exact hy

theorem closure_rootElts : Subgroup.closure (rootElts Δ) = ⊤ := by
  rw [eq_top_iff, ← hΔ.root.gen]
  refine iSup₂_le fun X hX => ?_
  obtain ⟨x, hx, rfl⟩ := (mem_iff_exists_zpowers hΔ hcard X).1 hX
  exact (Subgroup.zpowers_le).2 (Subgroup.subset_closure hx)

theorem commute_or_orderOf_eq_three {x y : H} (hx : x ∈ rootElts Δ) (hy : y ∈ rootElts Δ) :
    x * y = y * x ∨ orderOf (x * y) = 3 := by
  by_cases hxy : x = y
  · exact Or.inl (by rw [hxy])
  have hne : Subgroup.zpowers x ≠ Subgroup.zpowers y := fun h =>
    hxy (eq_of_zpowers_eq hΔ hx hy h)
  rcases hΔ.commuting_or_opposite (zpowers_mem hΔ hcard hx) (zpowers_mem hΔ hcard hy) hne with
    h | h
  · exact Or.inl (commuting_zpowers_iff.1 h)
  · exact Or.inr (orderOf_mul_eq_three_of_braid (mul_self_of_mem hΔ hx)
      (mul_self_of_mem hΔ hy) hxy (mul_mul_eq_of_opposite (mul_self_of_mem hΔ hx)
        (mul_self_of_mem hΔ hy) (ne_one_of_mem hx) h))

theorem pair_rootElts [Finite H] {x₀ : H} (hx₀ : x₀ ∈ rootElts Δ) : Pair H (rootElts Δ) := by
  refine ⟨inferInstance, ⟨x₀, rootElts_eq_isConj hΔ hcard hx₀⟩, fun e he => ?_,
    fun e he f hf => ?_, closure_rootElts hΔ hcard⟩
  · exact orderOf_eq_prime (by rw [sq, mul_self_of_mem hΔ he]) (ne_one_of_mem he)
  · rcases commute_or_orderOf_eq_three hΔ hcard he hf with h | h
    · have h2 : (e * f) ^ 2 = 1 := by
        rw [sq, mul_assoc, ← mul_assoc f, ← h, mul_assoc, mul_self_of_mem hΔ hf, mul_one,
          mul_self_of_mem hΔ he]
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h2) with h' | h'
      · simp [h']
      · simp [h']
    · simp [h]

end Class

structure QHyp (H : Type) [Group H] (D : Set H) : Prop where
  hyp : CFSG.Fischer.Classification.Hyp H D
  rank : ∃ e ∈ D, ∃ f ∈ D, e ≠ f ∧ e * f = f * e
  points : ∀ e ∈ D, ∀ f ∈ D, (∀ d ∈ D, d * e = e * d ↔ d * f = f * d) → e = f
  thick : ∀ e ∈ D, ∀ f ∈ D, e ≠ f → e * f = f * e →
    ∃ g ∈ D, g ≠ e ∧ g ≠ f ∧ ∀ d ∈ D, d * e = e * d → d * f = f * d → d * g = g * d

theorem qHyp_rootElts {H : Type} [Group H] {Δ : Set (Subgroup H)} (h : TransvectionHyp H Δ)
    {A : Subgroup H} (hA : A ∈ Δ) (h2 : Nat.card A = 2) : QHyp H (rootElts Δ) := by
  have hΔ := h.cls
  have hcard : ∀ X ∈ Δ, Nat.card X = 2 := fun X hX => card_eq_two hΔ hA h2 hX
  have := h.finite
  obtain ⟨hS, hthick⟩ := h.small ⟨A, hA, h2⟩
  obtain ⟨a, haA, ha1⟩ := hΔ.root.exists_ne_one hA
  have ha : a ∈ rootElts Δ := ⟨A, hA, haA, ha1⟩
  have hcomm : ∀ {x y : H}, Commuting (Subgroup.zpowers x) (Subgroup.zpowers y) ↔ x * y = y * x :=
    commuting_zpowers_iff
  refine ⟨⟨pair_rootElts hΔ hcard ha, h.center, hS⟩, ?_, ?_, ?_⟩
  · obtain ⟨X, hX, Y, hY, hXY, hc⟩ := h.rank
    obtain ⟨x, hx, rfl⟩ := (mem_iff_exists_zpowers hΔ hcard X).1 hX
    obtain ⟨y, hy, rfl⟩ := (mem_iff_exists_zpowers hΔ hcard Y).1 hY
    exact ⟨x, hx, y, hy, fun e => hXY (by rw [e]), hcomm.1 hc⟩
  · intro e he f hf hef
    have := h.points _ (zpowers_mem hΔ hcard he) _ (zpowers_mem hΔ hcard hf) fun C hC => by
      obtain ⟨c, hc, rfl⟩ := (mem_iff_exists_zpowers hΔ hcard C).1 hC
      rw [hcomm, hcomm]
      constructor
      · intro h'
        exact ((hef c hc).1 h'.symm).symm
      · intro h'
        exact ((hef c hc).2 h'.symm).symm
    exact eq_of_zpowers_eq hΔ he hf this
  · intro e he f hf hef hc
    obtain ⟨C, hC, hCe, hCf, hall⟩ := hthick _ (zpowers_mem hΔ hcard he) _
      (zpowers_mem hΔ hcard hf) (fun h' => hef (eq_of_zpowers_eq hΔ he hf h'))
      (hcomm.2 hc)
    obtain ⟨g, hg, rfl⟩ := (mem_iff_exists_zpowers hΔ hcard C).1 hC
    refine ⟨g, hg, fun h' => hCe (by rw [h']), fun h' => hCf (by rw [h']), fun d hd hde hdf => ?_⟩
    exact hcomm.1 (hall _ (zpowers_mem hΔ hcard hd) (hcomm.2 hde) (hcomm.2 hdf))

theorem mem_iff_conjSub_map {K : Type*} [Group K] {Δ : Set (Subgroup H)} {D : Set H}
    (hΔ : ∀ X : Subgroup H, X ∈ Δ ↔ ∃ x ∈ D, X = Subgroup.zpowers x)
    (hD : ∀ x ∈ D, ∀ y, IsConj x y ↔ y ∈ D) (Φ : K →* H) (hΦ : Function.Surjective Φ)
    {T : Subgroup K} {t₀ : K} (hT : T = Subgroup.zpowers t₀) (ht₀ : Φ t₀ ∈ D)
    (X : Subgroup H) : X ∈ Δ ↔ ∃ g, X = (conjSub T g).map Φ := by
  have himg : ∀ g : K, (conjSub T g).map Φ = Subgroup.zpowers (Φ g * Φ t₀ * (Φ g)⁻¹) := by
    intro g
    rw [hT, conjSub_zpowers, MonoidHom.map_zpowers, map_mul, map_mul, map_inv]
  rw [hΔ]
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, hc⟩ := isConj_iff.1 ((hD _ ht₀ x).2 hx)
    obtain ⟨g, rfl⟩ := hΦ c
    exact ⟨g, by rw [himg, hc]⟩
  · rintro ⟨g, rfl⟩
    exact ⟨_, (hD _ ht₀ _).1 (isConj_iff.2 ⟨Φ g, rfl⟩), himg g⟩

end CFSG.Timmesfeld.Transvection.QTwo
