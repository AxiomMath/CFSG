module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Data.Rat.Star
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Walter.J1

open scoped Classical

variable {G : Type*} [Group G]

@[expose] def involutions (G : Type*) [Group G] : Set G := {u | orderOf u = 2}

abbrev RightCosets (H : Subgroup G) := Quotient (QuotientGroup.rightRel H)

abbrev rightCoset (H : Subgroup G) (g : G) : RightCosets H := Quotient.mk _ g

@[expose] noncomputable def cosetInvolutions (H : Subgroup G) (q : RightCosets H) : ℕ :=
  {u | u ∈ involutions G ∧ rightCoset H u = q}.ncard

@[expose] noncomputable def cosetCount (H : Subgroup G) (n : ℕ) : ℕ :=
  Nat.card {q : RightCosets H // q ≠ rightCoset H 1 ∧ cosetInvolutions H q = n}

@[expose] def involutionsOf (H : Subgroup G) (n : ℕ) : Set G :=
  {u | u ∈ involutions G ∧ u ∉ H ∧ cosetInvolutions H (rightCoset H u) = n}

@[expose] noncomputable def benderC (H : Subgroup G) : ℕ :=
  {u | u ∈ involutionsOf H 1 ∧ ∃ h ∈ H, h ≠ 1 ∧ h * u = u * h}.ncard

theorem mem_involutions {u : G} : u ∈ involutions G ↔ orderOf u = 2 := Iff.rfl

theorem mem_involutions_iff {u : G} : u ∈ involutions G ↔ u * u = 1 ∧ u ≠ 1 := by
  rw [mem_involutions]
  constructor
  · intro h
    refine ⟨by rw [← pow_two, ← h, pow_orderOf_eq_one], fun h1 => ?_⟩
    rw [h1, orderOf_one] at h
    omega
  · rintro ⟨h2, h1⟩
    exact orderOf_eq_prime (by rwa [pow_two]) h1

theorem rightCoset_eq_iff {H : Subgroup G} {a b : G} :
    rightCoset H a = rightCoset H b ↔ b * a⁻¹ ∈ H := by
  rw [Quotient.eq, QuotientGroup.rightRel_apply]

theorem rightCoset_eq_one_iff {H : Subgroup G} {u : G} :
    rightCoset H u = rightCoset H 1 ↔ u ∈ H := by
  rw [rightCoset_eq_iff, one_mul, inv_mem_iff]

theorem cosetInvolutions_eq {H : Subgroup G} {u : G} (hu : u ∈ involutions G) (huH : u ∉ H) :
    cosetInvolutions H (rightCoset H u) = {h | h ∈ H ∧ u * h * u⁻¹ = h⁻¹}.ncard := by
  obtain ⟨hu2, hu1⟩ := mem_involutions_iff.mp hu
  have huinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  unfold cosetInvolutions
  refine Set.ncard_congr (fun v _ => v * u⁻¹) ?_ ?_ ?_
  · rintro v ⟨hv, hvu⟩
    obtain ⟨hv2, -⟩ := mem_involutions_iff.mp hv
    rw [rightCoset_eq_iff] at hvu
    refine ⟨by simpa using H.inv_mem hvu, ?_⟩
    rw [huinv]
    calc u * (v * u) * u = u * (v * (u * u)) := by group
      _ = u * v := by rw [hu2, mul_one]
      _ = (v * u)⁻¹ := by
        rw [mul_inv_rev, huinv, inv_eq_of_mul_eq_one_right hv2]
  · intro a b _ _ hab
    exact mul_right_cancel hab
  · rintro h ⟨hh, hhu⟩
    refine ⟨h * u, ⟨mem_involutions_iff.mpr ⟨?_, ?_⟩, ?_⟩, by simp⟩
    · calc h * u * (h * u) = h * (u * h * u⁻¹) * (u * u) := by group
        _ = 1 := by rw [hhu, hu2]; group
    · intro h1
      apply huH
      have : u = h⁻¹ := by
        calc u = h⁻¹ * (h * u) := by group
          _ = h⁻¹ := by rw [h1, mul_one]
      rw [this]
      exact H.inv_mem hh
    · rw [rightCoset_eq_iff, mul_inv_rev, huinv, ← mul_assoc, hu2, one_mul]
      exact H.inv_mem hh

section Counting

variable [Finite G]

omit [Finite G] in
theorem ncard_eq_sum_ncard_fiber {α β : Type*} [Finite α] (S : Set α) (f : α → β)
    (t : Finset β) (h : ∀ x ∈ S, f x ∈ t) :
    S.ncard = ∑ b ∈ t, {x | x ∈ S ∧ f x = b}.ncard := by
  have : Fintype α := Fintype.ofFinite α
  rw [Set.ncard_eq_toFinset_card', Finset.card_eq_sum_card_fiberwise (f := f) (t := t)]
  · refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Set.ncard_eq_toFinset_card']
    exact congrArg Finset.card (by ext x; simp)
  · intro x hx
    exact h x (by simpa using hx)

theorem cosetInvolutions_le (H : Subgroup G) (q : RightCosets H) :
    cosetInvolutions H q ≤ Nat.card G := by
  unfold cosetInvolutions
  rw [← Set.ncard_univ]
  exact Set.ncard_le_ncard (Set.subset_univ _)

theorem involutionsOf_ncard (H : Subgroup G) (n : ℕ) :
    (involutionsOf H n).ncard = n * cosetCount H n := by
  have : Fintype G := Fintype.ofFinite G
  set T : Finset (RightCosets H) :=
    Finset.univ.filter (fun q => q ≠ rightCoset H 1 ∧ cosetInvolutions H q = n)
  have hT : cosetCount H n = T.card := by
    unfold cosetCount
    rw [Nat.card_eq_fintype_card, ← Fintype.card_coe]
    exact Fintype.card_congr (Equiv.subtypeEquivRight (fun q => by simp [T]))
  rw [ncard_eq_sum_ncard_fiber (involutionsOf H n) (fun u => rightCoset H u) T, hT,
    Finset.sum_const_nat (m := n), mul_comm]
  · intro q hq
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    have hset : {x | x ∈ involutionsOf H n ∧ rightCoset H x = q} =
        {u | u ∈ involutions G ∧ rightCoset H u = q} := by
      ext u
      simp only [involutionsOf, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨⟨hu, -, -⟩, hq'⟩
        exact ⟨hu, hq'⟩
      · rintro ⟨hu, hq'⟩
        refine ⟨⟨hu, fun huH => hq.1 ?_, by rw [hq']; exact hq.2⟩, hq'⟩
        rw [← hq', rightCoset_eq_one_iff.mpr huH]
    rw [hset]
    exact hq.2
  · intro u hu
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => hu.2.1 (rightCoset_eq_one_iff.mp h), hu.2.2⟩

theorem ncard_involutions_diff (H : Subgroup G) :
    (involutions G \ (H : Set G)).ncard =
      ∑ n ∈ Finset.range (Nat.card G + 1), (involutionsOf H n).ncard := by
  rw [ncard_eq_sum_ncard_fiber _ (fun u => cosetInvolutions H (rightCoset H u))
    (Finset.range (Nat.card G + 1))]
  · refine Finset.sum_congr rfl (fun n _ => ?_)
    congr 1
    ext u
    simp [involutionsOf, and_assoc]
  · intro u _
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (cosetInvolutions_le H _)

theorem ncard_involutions_eq (H : Subgroup G) :
    (involutions G).ncard = (involutions G ∩ (H : Set G)).ncard +
      ∑ n ∈ Finset.range (Nat.card G + 1), n * cosetCount H n := by
  rw [← Set.ncard_inter_add_ncard_sdiff_eq_ncard (involutions G) (H : Set G),
    ncard_involutions_diff]
  simp only [involutionsOf_ncard]

theorem index_eq (H : Subgroup G) :
    H.index = 1 + ∑ n ∈ Finset.range (Nat.card G + 1), cosetCount H n := by
  have : Fintype G := Fintype.ofFinite G
  have hidx : H.index = Fintype.card (RightCosets H) := by
    rw [Subgroup.index, ← Nat.card_eq_fintype_card]
    exact (Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel H)).symm
  rw [hidx, ← Nat.card_eq_fintype_card, ← Set.ncard_univ,
    ← Set.ncard_sdiff_singleton_add_one (Set.mem_univ (rightCoset H 1)), add_comm,
    ncard_eq_sum_ncard_fiber _ (fun q => cosetInvolutions H q) (Finset.range (Nat.card G + 1))]
  · congr 1
    refine Finset.sum_congr rfl (fun n _ => ?_)
    unfold cosetCount
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr (Equiv.subtypeEquivRight (fun q => by simp))
  · intro q _
    simp only [Finset.mem_range]
    exact Nat.lt_succ_of_le (cosetInvolutions_le H q)

omit [Finite G] in
theorem cosetInvolutions_conj {H : Subgroup G} {h : G} (hh : h ∈ H) (u : G) :
    cosetInvolutions H (rightCoset H (h * u * h⁻¹)) = cosetInvolutions H (rightCoset H u) := by
  unfold cosetInvolutions
  symm
  refine Set.ncard_congr (fun v _ => h * v * h⁻¹) ?_ ?_ ?_
  · rintro v ⟨hv, hvu⟩
    refine ⟨?_, ?_⟩
    · rw [mem_involutions, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hv
    · rw [rightCoset_eq_iff] at hvu ⊢
      rw [show h * u * h⁻¹ * (h * v * h⁻¹)⁻¹ = h * (u * v⁻¹) * h⁻¹ by group]
      exact H.mul_mem (H.mul_mem hh hvu) (H.inv_mem hh)
  · intro a b _ _ hab
    simpa using hab
  · rintro w ⟨hw, hwu⟩
    refine ⟨h⁻¹ * w * h, ⟨?_, ?_⟩, by group⟩
    · rw [mem_involutions, show h⁻¹ * w * h = h⁻¹ * w * h⁻¹⁻¹ by group, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq]
      exact hw
    · rw [rightCoset_eq_iff] at hwu ⊢
      rw [show u * (h⁻¹ * w * h)⁻¹ = h⁻¹ * (h * u * h⁻¹ * w⁻¹) * h by group]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) hwu) hh

omit [Finite G] in
theorem conj_mem_involutionsOf {H : Subgroup G} {n : ℕ} {u : G} (hu : u ∈ involutionsOf H n)
    {h : G} (hh : h ∈ H) : h * u * h⁻¹ ∈ involutionsOf H n := by
  obtain ⟨hu, huH, hun⟩ := hu
  refine ⟨?_, fun hc => huH ?_, by rw [cosetInvolutions_conj hh, hun]⟩
  · rw [mem_involutions, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hu
  · have : u = h⁻¹ * (h * u * h⁻¹) * h := by group
    rw [this]
    exact H.mul_mem (H.mul_mem (H.inv_mem hh) hc) hh

theorem card_dvd_ncard_of_free {H : Subgroup G} {X : Set G}
    (hX : ∀ u ∈ X, ∀ h ∈ H, h * u * h⁻¹ ∈ X)
    (hfree : ∀ u ∈ X, ∀ h ∈ H, h * u = u * h → h = 1) : Nat.card H ∣ X.ncard := by
  let orb : G → Set G := fun u => (fun h => h * u * h⁻¹) '' (H : Set G)
  have hmem : ∀ u v : G, v ∈ orb u → orb v = orb u := by
    rintro u v ⟨k, hk, rfl⟩
    ext w
    constructor
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l * k, H.mul_mem hl hk, by group⟩
    · rintro ⟨l, hl, rfl⟩
      exact ⟨l * k⁻¹, H.mul_mem hl (H.inv_mem hk), by group⟩
  have hself : ∀ u, u ∈ orb u := fun u => ⟨1, H.one_mem, by group⟩
  have hcard : ∀ u ∈ X, (orb u).ncard = Nat.card H := by
    intro u hu
    have hinj : Set.InjOn (fun h => h * u * h⁻¹) (H : Set G) := by
      intro a ha b hb hab
      have hab : a * u * a⁻¹ = b * u * b⁻¹ := hab
      have h1 : (b⁻¹ * a) * u = u * (b⁻¹ * a) := by
        calc (b⁻¹ * a) * u = b⁻¹ * (a * u * a⁻¹) * a := by group
          _ = b⁻¹ * (b * u * b⁻¹) * a := by rw [hab]
          _ = u * (b⁻¹ * a) := by group
      have := hfree u hu _ (H.mul_mem (H.inv_mem hb) ha) h1
      rw [inv_mul_eq_one] at this
      exact this.symm
    rw [hinj.ncard_image]
    exact (Nat.card_coe_set_eq (H : Set G)).symm
  have hsub : ∀ u ∈ X, orb u ⊆ X := by
    rintro u hu _ ⟨k, hk, rfl⟩
    exact hX u hu k hk
  have : Finite (Set G) := inferInstance
  set t : Finset (Set G) := (orb '' X).toFinite.toFinset
  rw [ncard_eq_sum_ncard_fiber X orb t (fun u hu => by simp [t]; exact ⟨u, hu, rfl⟩)]
  refine Finset.dvd_sum (fun O hO => ?_)
  simp only [t, Set.Finite.mem_toFinset] at hO
  obtain ⟨u, hu, rfl⟩ := hO
  have hfib : {x | x ∈ X ∧ orb x = orb u} = orb u := by
    ext v
    constructor
    · rintro ⟨-, hv⟩
      rw [← hv]
      exact hself v
    · intro hv
      exact ⟨hsub u hu hv, hmem u v hv⟩
  rw [hfib, hcard u hu]

theorem exists_cosetCount_one_eq (H : Subgroup G) :
    ∃ m : ℕ, cosetCount H 1 = benderC H + m * Nat.card H := by
  set Y := {u | u ∈ involutionsOf H 1 ∧ ∃ h ∈ H, h ≠ 1 ∧ h * u = u * h}
  set X := {u | u ∈ involutionsOf H 1 ∧ ∀ h ∈ H, h * u = u * h → h = 1}
  have hsplit : (involutionsOf H 1).ncard = Y.ncard + X.ncard := by
    rw [← Set.ncard_union_eq]
    · congr 1
      ext u
      simp only [Y, X, Set.mem_union, Set.mem_ofPred_eq]
      constructor
      · intro hu
        by_cases h : ∃ h ∈ H, h ≠ 1 ∧ h * u = u * h
        · exact Or.inl ⟨hu, h⟩
        · push Not at h
          exact Or.inr ⟨hu, fun k hk hku => by_contra fun hk1 => h k hk hk1 hku⟩
      · rintro (⟨hu, -⟩ | ⟨hu, -⟩) <;> exact hu
    · rw [Set.disjoint_left]
      rintro u ⟨-, k, hk, hk1, hku⟩ ⟨-, hfree⟩
      exact hk1 (hfree k hk hku)
  have hdvd : Nat.card H ∣ X.ncard := by
    apply card_dvd_ncard_of_free
    · rintro u ⟨hu, hfree⟩ h hh
      refine ⟨conj_mem_involutionsOf hu hh, fun k hk hku => ?_⟩
      have h1 : (h⁻¹ * k * h) * u = u * (h⁻¹ * k * h) := by
        calc (h⁻¹ * k * h) * u = h⁻¹ * (k * (h * u * h⁻¹)) * h := by group
          _ = h⁻¹ * ((h * u * h⁻¹) * k) * h := by rw [hku]
          _ = u * (h⁻¹ * k * h) := by group
      have := hfree _ (H.mul_mem (H.mul_mem (H.inv_mem hh) hk) hh) h1
      calc k = h * (h⁻¹ * k * h) * h⁻¹ := by group
        _ = 1 := by rw [this]; group
    · rintro u ⟨-, hfree⟩ h hh hhu
      exact hfree h hh hhu
  obtain ⟨m, hm⟩ := hdvd
  refine ⟨m, ?_⟩
  have h1 := involutionsOf_ncard H 1
  rw [one_mul] at h1
  rw [← h1, hsplit, hm, mul_comm]
  rfl

theorem cosetCount_one_lt (H : Subgroup G) (f : ℚ)
    (hf : f = ((involutions G).ncard : ℚ) / H.index - 1) (hpos : 0 < f) :
    (cosetCount H 1 : ℚ) < f⁻¹ * (((involutions G ∩ (H : Set G)).ncard : ℚ) +
        ∑ n ∈ Finset.Ico 2 (Nat.card G + 1), ((n : ℚ) - 1) * cosetCount H n) - 1 -
      ∑ n ∈ Finset.Ico 2 (Nat.card G + 1), (cosetCount H n : ℚ) := by
  have hG : 1 ≤ Nat.card G := Nat.card_pos
  have hsplit : ∀ g : ℕ → ℚ, ∑ n ∈ Finset.range (Nat.card G + 1), g n =
      g 0 + g 1 + ∑ n ∈ Finset.Ico 2 (Nat.card G + 1), g n := by
    intro g
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (show 0 ≤ 2 by norm_num)
      (show 2 ≤ Nat.card G + 1 by omega), ← Finset.range_eq_Ico, Finset.sum_range_succ,
      Finset.sum_range_one]
  have hJ := ncard_involutions_eq H
  have hN := index_eq H
  have hJq : ((involutions G).ncard : ℚ) = ((involutions G ∩ (H : Set G)).ncard : ℚ) +
      (cosetCount H 1 : ℚ) + ∑ n ∈ Finset.Ico 2 (Nat.card G + 1), (n : ℚ) * cosetCount H n := by
    rw [hJ]
    push_cast
    rw [hsplit (fun n => ((n : ℚ) * (cosetCount H n : ℚ)))]
    simp only [CharP.cast_eq_zero, zero_mul, zero_add, Nat.cast_one, one_mul]
    ring
  have hNq : (H.index : ℚ) = 1 + cosetCount H 0 + cosetCount H 1 +
      ∑ n ∈ Finset.Ico 2 (Nat.card G + 1), (cosetCount H n : ℚ) := by
    rw [hN]
    push_cast
    rw [hsplit (fun n => (cosetCount H n : ℚ))]
    ring
  set A := ∑ n ∈ Finset.Ico 2 (Nat.card G + 1), (cosetCount H n : ℚ)
  set B := ∑ n ∈ Finset.Ico 2 (Nat.card G + 1), (n : ℚ) * cosetCount H n
  have hBA : ∑ n ∈ Finset.Ico 2 (Nat.card G + 1), ((n : ℚ) - 1) * cosetCount H n = B - A := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun n _ => by ring)
  rw [hBA]
  have hNpos : (0 : ℚ) < H.index := by
    rw [hNq]
    positivity
  set N : ℚ := (H.index : ℚ)
  set jH : ℚ := ((involutions G ∩ (H : Set G)).ncard : ℚ)
  set b0 : ℚ := (cosetCount H 0 : ℚ)
  set b1 : ℚ := (cosetCount H 1 : ℚ)
  have hfN : f * N = jH + (B - A) - 1 - b0 := by
    rw [hf, sub_mul, div_mul_cancel₀ _ hNpos.ne', hJq, hNq]
    ring
  have hkey : jH + (B - A) = f * N + 1 + b0 := by linarith
  rw [hkey, mul_add, mul_add, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  have hb0 : (0 : ℚ) ≤ b0 := Nat.cast_nonneg _
  have h1 : 0 < f⁻¹ * 1 := by rw [mul_one]; exact inv_pos.mpr hpos
  have h2 : 0 ≤ f⁻¹ * b0 := mul_nonneg (inv_pos.mpr hpos).le hb0
  rw [hNq]
  linarith

end Counting

end CFSG.Walter.J1
