module

public import CFSG.Timmesfeld.RankTwo.LevisBMinusFrame

public section

namespace CFSG.Timmesfeld.RankTwo

open CFSG.LieType CFSG.LieType.Universal CFSG.LieType.Universal.Spin
open CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.Steinberg
open scoped commutatorElement

section Roots

variable (n : ℕ)

@[expose] def MinusLong (γ : Fin (n - 1) → ℤ) : Prop :=
  ∃ x : Fin (n - 1) × Fin (n - 1) × Bool × Bool, x.1 ≠ x.2.1 ∧
    toStdB (n - 1) γ = Pi.single x.1 (boolSign x.2.2.1) + Pi.single x.2.1 (boolSign x.2.2.2)

@[expose] def MinusShort (γ : Fin (n - 1) → ℤ) : Prop :=
  ∃ x : Fin (n - 1) × Bool, toStdB (n - 1) γ = Pi.single x.1 (boolSign x.2)

variable {n}

theorem MinusLong.of_eq {γ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j) (s t : Bool)
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t)) :
    MinusLong n γ :=
  ⟨(i, j, s, t), hij, h⟩

theorem MinusShort.of_eq {γ : Fin (n - 1) → ℤ} (i : Fin (n - 1)) (s : Bool)
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) : MinusShort n γ :=
  ⟨(i, s), h⟩

theorem MinusShort.not_long {γ : Fin (n - 1) → ℤ} (h : MinusShort n γ) : ¬ MinusLong n γ := by
  rintro ⟨⟨i, j, s, t⟩, hij, hL⟩
  obtain ⟨⟨k, u⟩, hS⟩ := h
  exact single_ne_single_add_single hij (boolSign_ne_zero s) (boolSign_ne_zero t)
    (hS.symm.trans hL)

theorem minusLong_or_minusShort {γ : Fin (n - 1) → ℤ}
    (hγ : γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅) :
    MinusLong n γ ∨ MinusShort n γ := by
  rcases exists_toStdB_eq_of_mem_roots n hγ with ⟨i, j, hij, s, t, h⟩ | ⟨i, s, h⟩
  · exact Or.inl (.of_eq hij s t h)
  · exact Or.inr (.of_eq i s h)

theorem MinusLong.mem_roots {γ : Fin (n - 1) → ℤ} (h : MinusLong n γ) :
    γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅ := by
  obtain ⟨⟨i, j, s, t⟩, hij, h⟩ := h
  exact mem_roots_of_toStdB_eq_long n hij s t h

theorem MinusShort.mem_roots {γ : Fin (n - 1) → ℤ} (h : MinusShort n γ) :
    γ ∈ RootSystem.roots (isFiniteType_cartanB (n - 1)) ∅ := by
  obtain ⟨⟨i, s⟩, h⟩ := h
  exact mem_roots_of_toStdB_eq_short n i s h

theorem MinusLong.reflection {γ : Fin (n - 1) → ℤ} (h : MinusLong n γ) (k : Fin (n - 1)) :
    MinusLong n (RootSystem.reflection (cartanB (n - 1)) k γ) := by
  obtain ⟨⟨i, j, s, t⟩, hij, h⟩ := h
  by_cases hk : k.val + 1 < n - 1
  · exact .of_eq ((Equiv.swap k ⟨k.val + 1, hk⟩).injective.ne hij) _ _
      (toStdB_reflection_long_of_lt n hk h)
  · exact .of_eq hij _ _ (toStdB_reflection_long_of_not_lt n hk h)

theorem MinusShort.reflection {γ : Fin (n - 1) → ℤ} (h : MinusShort n γ) (k : Fin (n - 1)) :
    MinusShort n (RootSystem.reflection (cartanB (n - 1)) k γ) := by
  obtain ⟨⟨i, s⟩, h⟩ := h
  by_cases hk : k.val + 1 < n - 1
  · exact .of_eq _ _ (toStdB_reflection_short_of_lt n hk h)
  · exact .of_eq _ _ (toStdB_reflection_short_of_not_lt n hk h)

end Roots

section Elements

variable (n : ℕ) {F : Type} [Field F]

open Classical in
@[expose] noncomputable def minusXL (b c : F) (γ : Fin (n - 1) → ℤ) (a : F) :
    spinGroup (quadMinus n F b c) :=
  if h : MinusLong n γ then mlr n b c h.choose.1 h.choose.2.1 h.choose.2.2.1 h.choose.2.2.2 a
  else 1

open Classical in
@[expose] noncomputable def minusXS {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (γ : Fin (n - 1) → ℤ) (p : Fin 2 → F) : spinGroup (quadMinus n F b c) :=
  if h : MinusShort n γ then msr n hirr h.choose.1 h.choose.2 p else 1

variable {n} {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem minusXL_of_long {γ : Fin (n - 1) → ℤ} (hγ : MinusLong n γ) :
    ∃ (i j : Fin (n - 1)) (hij : i ≠ j) (s t : Bool),
      toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t) ∧
        ∀ a, minusXL n b c γ a = (minusFrame n b c).longRoot hij s t (.ofAdd a) := by
  obtain ⟨hne, e⟩ := hγ.choose_spec
  refine ⟨_, _, hne, _, _, e, fun a => ?_⟩
  rw [minusXL, dite_eq_left hγ, mlr_of_ne hne]

theorem minusXS_of_short {γ : Fin (n - 1) → ℤ} (hγ : MinusShort n γ) :
    ∃ (i : Fin (n - 1)) (s : Bool), toStdB (n - 1) γ = Pi.single i (boolSign s) ∧
      ∀ p, minusXS n hirr γ p = twShortRoot n hirr i s (.ofAdd p) := by
  refine ⟨_, _, hγ.choose_spec, fun p => ?_⟩
  rw [minusXS, dite_eq_left hγ]

theorem minusXL_eq [CharP F 2] {γ : Fin (n - 1) → ℤ} {i j : Fin (n - 1)} (hij : i ≠ j)
    (s t : Bool) (h : toStdB (n - 1) γ = Pi.single i (boolSign s) + Pi.single j (boolSign t))
    (a : F) : minusXL n b c γ a = mlr n b c i j s t a := by
  obtain ⟨i', j', hij', s', t', e, he⟩ := minusXL_of_long (b := b) (c := c) (.of_eq hij s t h)
  rw [he, ← mlr_of_ne hij']
  rcases (single_add_single_eq_iff hij' hij (boolSign_ne_zero s') (boolSign_ne_zero t')).1
      (e.symm.trans h) with ⟨rfl, hs, rfl, ht⟩ | ⟨rfl, hs, rfl, ht⟩
  · rw [boolSign_injective hs, boolSign_injective ht]
  · rw [boolSign_injective hs, boolSign_injective ht, mlr_swap]

theorem minusXS_eq {γ : Fin (n - 1) → ℤ} (i : Fin (n - 1)) (s : Bool)
    (h : toStdB (n - 1) γ = Pi.single i (boolSign s)) (p : Fin 2 → F) :
    minusXS n hirr γ p = msr n hirr i s p := by
  obtain ⟨i', s', e, he⟩ := minusXS_of_short hirr (.of_eq i s h)
  rw [he]
  obtain ⟨rfl, hs⟩ := (single_eq_single_iff' (boolSign_ne_zero s')).1 (e.symm.trans h)
  rw [boolSign_injective hs]

theorem minusXL_mem {γ : Fin (n - 1) → ℤ} (hγ : MinusLong n γ) (a : F) :
    minusXL n b c γ a ∈ (minusDatum n hirr).rootGroup γ := by
  obtain ⟨i, j, hij, s, t, e, he⟩ := minusXL_of_long (b := b) (c := c) hγ
  rw [he]
  exact longRoot_mem_minusRootGroup n hirr hij s t e a

theorem minusXS_mem {γ : Fin (n - 1) → ℤ} (hγ : MinusShort n γ) (p : Fin 2 → F) :
    minusXS n hirr γ p ∈ (minusDatum n hirr).rootGroup γ := by
  obtain ⟨i, s, e, he⟩ := minusXS_of_short hirr hγ
  rw [he]
  exact twShortRoot_mem_minusRootGroup n hirr i s e p

theorem exists_minusXL_eq {γ : Fin (n - 1) → ℤ} (hγ : MinusLong n γ)
    {y : spinGroup (quadMinus n F b c)} (hy : y ∈ (minusDatum n hirr).rootGroup γ) :
    ∃ a, minusXL n b c γ a = y := by
  obtain ⟨i, j, hij, s, t, e, he⟩ := minusXL_of_long (b := b) (c := c) hγ
  obtain ⟨a, rfl⟩ := (mem_minusRootGroup_long_iff n hirr hij s t e).1 hy
  exact ⟨a, he a⟩

theorem exists_minusXS_eq {γ : Fin (n - 1) → ℤ} (hγ : MinusShort n γ)
    {y : spinGroup (quadMinus n F b c)} (hy : y ∈ (minusDatum n hirr).rootGroup γ) :
    ∃ p, minusXS n hirr γ p = y := by
  obtain ⟨i, s, e, he⟩ := minusXS_of_short hirr hγ
  obtain ⟨p, rfl⟩ := (mem_minusRootGroup_short_iff n hirr i s e).1 hy
  exact ⟨p, he p⟩

omit hirr in
theorem minusXL_add (γ : Fin (n - 1) → ℤ) (a a' : F) :
    minusXL n b c γ (a + a') = minusXL n b c γ a * minusXL n b c γ a' := by
  by_cases hγ : MinusLong n γ
  · obtain ⟨i, j, hij, s, t, e, he⟩ := minusXL_of_long (b := b) (c := c) hγ
    rw [he, he, he, ofAdd_add, map_mul]
  · simp only [minusXL, dite_eq_right hγ, mul_one]

theorem minusXS_add (γ : Fin (n - 1) → ℤ) (p q : Fin 2 → F) :
    minusXS n hirr γ (p + q) = minusXS n hirr γ p * minusXS n hirr γ q := by
  by_cases hγ : MinusShort n γ
  · obtain ⟨i, s, e, he⟩ := minusXS_of_short hirr hγ
    rw [he, he, he, ofAdd_add, map_mul]
  · simp only [minusXS, dite_eq_right hγ, mul_one]

omit hirr in
theorem minusXL_injective {γ : Fin (n - 1) → ℤ} (hγ : MinusLong n γ) :
    Function.Injective (minusXL n b c γ) := by
  obtain ⟨i, j, hij, s, t, e, he⟩ := minusXL_of_long (b := b) (c := c) hγ
  intro a a' h
  rw [he, he] at h
  exact Multiplicative.ofAdd.injective ((minusFrame n b c).longRoot_injective hij s t h)

theorem minusXS_injective {γ : Fin (n - 1) → ℤ} (hγ : MinusShort n γ) :
    Function.Injective (minusXS n hirr γ) := by
  obtain ⟨i, s, e, he⟩ := minusXS_of_short hirr hγ
  intro p q h
  rw [he, he] at h
  exact Multiplicative.ofAdd.injective (twShortRoot_injective n hirr i s h)

omit hirr in
theorem minusXL_zero (γ : Fin (n - 1) → ℤ) : minusXL n b c γ 0 = 1 := by
  have h := minusXL_add (b := b) (c := c) γ 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

theorem minusXS_zero (γ : Fin (n - 1) → ℤ) : minusXS n hirr γ 0 = 1 := by
  have h := minusXS_add hirr γ 0 0
  rw [add_zero] at h
  exact left_eq_mul.1 h

omit hirr in
theorem minusXL_mul_self [CharP F 2] (γ : Fin (n - 1) → ℤ) (a : F) :
    minusXL n b c γ a * minusXL n b c γ a = 1 := by
  rw [← minusXL_add, CharTwo.add_self_eq_zero, minusXL_zero]

theorem minusXS_mul_self [CharP F 2] (γ : Fin (n - 1) → ℤ) (p : Fin 2 → F) :
    minusXS n hirr γ p * minusXS n hirr γ p = 1 := by
  rw [← minusXS_add, show p + p = 0 from funext fun k => CharTwo.add_self_eq_zero (p k),
    minusXS_zero]

open Classical in
@[expose] noncomputable def minusPhiOf {G : Type*} [Group G] (ψL : (Fin (n - 1) → ℤ) → F → G)
    (ψS : (Fin (n - 1) → ℤ) → (Fin 2 → F) → G) : ∀ γ, (minusDatum n hirr).rootGroup γ → G :=
  fun γ y => if MinusLong n γ then
      (if h : ∃ a, minusXL n b c γ a = y then ψL γ h.choose else 1)
    else (if h : ∃ p, minusXS n hirr γ p = y then ψS γ h.choose else 1)

variable {G : Type*} [Group G] (ψL : (Fin (n - 1) → ℤ) → F → G)
  (ψS : (Fin (n - 1) → ℤ) → (Fin 2 → F) → G)

theorem minusPhiOf_long {γ : Fin (n - 1) → ℤ} (hγ : MinusLong n γ) (a : F) (hy) :
    minusPhiOf hirr ψL ψS γ ⟨minusXL n b c γ a, hy⟩ = ψL γ a := by
  classical
  have h' : ∃ a', minusXL n b c γ a' = minusXL n b c γ a := ⟨a, rfl⟩
  simp only [minusPhiOf, ite_eq_left hγ, dite_eq_left h']
  exact congrArg (ψL γ) (minusXL_injective hγ h'.choose_spec)

theorem minusPhiOf_short {γ : Fin (n - 1) → ℤ} (hγ : MinusShort n γ) (p : Fin 2 → F) (hy) :
    minusPhiOf hirr ψL ψS γ ⟨minusXS n hirr γ p, hy⟩ = ψS γ p := by
  classical
  have h' : ∃ p', minusXS n hirr γ p' = minusXS n hirr γ p := ⟨p, rfl⟩
  simp only [minusPhiOf, ite_eq_right hγ.not_long, dite_eq_left h']
  exact congrArg (ψS γ) (minusXS_injective hirr hγ h'.choose_spec)

theorem range_minusPhiOf_long {γ : Fin (n - 1) → ℤ} (hγ : MinusLong n γ) :
    Set.range (minusPhiOf hirr ψL ψS γ) = Set.range (ψL γ) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨a, rfl⟩ := exists_minusXL_eq hirr hγ hy
    exact ⟨a, (minusPhiOf_long hirr ψL ψS hγ a hy).symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨_, minusXL_mem hirr hγ a⟩, minusPhiOf_long hirr ψL ψS hγ a _⟩

theorem range_minusPhiOf_short {γ : Fin (n - 1) → ℤ} (hγ : MinusShort n γ) :
    Set.range (minusPhiOf hirr ψL ψS γ) = Set.range (ψS γ) := by
  ext x
  constructor
  · rintro ⟨⟨y, hy⟩, rfl⟩
    obtain ⟨p, rfl⟩ := exists_minusXS_eq hirr hγ hy
    exact ⟨p, (minusPhiOf_short hirr ψL ψS hγ p hy).symm⟩
  · rintro ⟨p, rfl⟩
    exact ⟨⟨_, minusXS_mem hirr hγ p⟩, minusPhiOf_short hirr ψL ψS hγ p _⟩

end Elements

section Weyl

variable {n : ℕ} {F : Type} [Field F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

theorem minusWeyl_conj_minusXL (k : Fin (n - 1)) {γ : Fin (n - 1) → ℤ} (hγ : MinusLong n γ)
    (a : F) :
    minusWeyl n hirr k * minusXL n b c γ a * (minusWeyl n hirr k)⁻¹ =
      minusXL n b c (RootSystem.reflection (cartanB (n - 1)) k γ) a := by
  obtain ⟨⟨i, j, s, t⟩, hij, h⟩ := hγ
  rw [minusXL_eq hij s t h]
  by_cases hk : k.val + 1 < n - 1
  · rw [minusWeyl_of_lt n hirr hk, longWeyl_conj_mlr (succ_ne_of_lt n hk) true false hij s t a,
      minusXL_eq ((Equiv.swap k ⟨k.val + 1, hk⟩).injective.ne hij) _ _
        (toStdB_reflection_long_of_lt n hk h)]
  · rw [minusWeyl_of_not_lt n hirr hk, shortWeyl_conj_mlr hirr k hij s t a,
      minusXL_eq hij _ _ (toStdB_reflection_long_of_not_lt n hk h)]

theorem minusWeyl_conj_minusXS (k : Fin (n - 1)) {γ : Fin (n - 1) → ℤ} (hγ : MinusShort n γ)
    (p : Fin 2 → F) :
    minusWeyl n hirr k * minusXS n hirr γ p * (minusWeyl n hirr k)⁻¹ =
      minusXS n hirr (RootSystem.reflection (cartanB (n - 1)) k γ)
        (if k.val + 2 = n then planeRefl b c planeOne p else p) := by
  obtain ⟨⟨i, s⟩, h⟩ := hγ
  have hk' := k.isLt
  rw [minusXS_eq hirr i s h]
  by_cases hk : k.val + 1 < n - 1
  · rw [ite_eq_right (by omega), minusWeyl_of_lt n hirr hk,
      longWeyl_conj_msr hirr (succ_ne_of_lt n hk) true false i s p,
      minusXS_eq hirr _ _ (toStdB_reflection_short_of_lt n hk h)]
  · rw [ite_eq_left (by omega), minusWeyl_of_not_lt n hirr hk, shortWeyl_conj_msr hirr k i s p,
      minusXS_eq hirr _ _ (toStdB_reflection_short_of_not_lt n hk h)]

end Weyl

section Coordinates

variable {n : ℕ}

theorem toStdB_A2sum {i : Fin (n - 1)} (h : i.val + 3 < n) :
    toStdB (n - 1) (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) =
      Pi.single i (boolSign true) +
        Pi.single (⟨i.val + 2, by omega⟩ : Fin (n - 1)) (boolSign false) := by
  funext a
  simp only [toStdB, Pi.add_apply, Pi.single_apply, Fin.ext_iff, boolSign_true, boolSign_false]
  split_ifs <;> omega

theorem toStdB_B2sum {i : Fin (n - 1)} (h : i.val + 3 = n) :
    toStdB (n - 1) (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) =
      Pi.single i (boolSign true) := by
  funext a
  simp only [toStdB, Pi.add_apply, Pi.single_apply, Fin.ext_iff, boolSign_true]
  split_ifs <;> omega

theorem toStdB_B2long {i : Fin (n - 1)} (h : i.val + 3 = n) :
    toStdB (n - 1) (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) =
      Pi.single i (boolSign true) +
        Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) (boolSign true) := by
  rw [two_nsmul]
  funext a
  simp only [toStdB, Pi.add_apply, Pi.single_apply, Fin.ext_iff, boolSign_true]
  split_ifs <;> omega

theorem minusLong_single {k : Fin (n - 1)} (hk : k.val + 2 < n) :
    MinusLong n (Pi.single k 1) :=
  .of_eq (succ_ne_of_lt n (by omega)) true false (toStdB_single_of_lt' n (by omega))

theorem minusLong_neg_single {k : Fin (n - 1)} (hk : k.val + 2 < n) :
    MinusLong n (-Pi.single k 1) :=
  .of_eq (succ_ne_of_lt n (by omega)).symm true false (toStdB_neg_single_of_lt' n (by omega))

theorem minusShort_single {k : Fin (n - 1)} (hk : k.val + 2 = n) :
    MinusShort n (Pi.single k 1) :=
  .of_eq k true (toStdB_single_of_not_lt' n (by omega))

theorem minusShort_neg_single {k : Fin (n - 1)} (hk : k.val + 2 = n) :
    MinusShort n (-Pi.single k 1) :=
  .of_eq k false (toStdB_neg_single_of_not_lt' n (by omega))

theorem minusLong_A2sum {i : Fin (n - 1)} (h : i.val + 3 < n) :
    MinusLong n (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) :=
  .of_eq (Fin.ne_of_val_ne (by simp)) true false (toStdB_A2sum h)

theorem minusShort_B2sum {i : Fin (n - 1)} (h : i.val + 3 = n) :
    MinusShort n (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) :=
  .of_eq i true (toStdB_B2sum h)

theorem minusLong_B2long {i : Fin (n - 1)} (h : i.val + 3 = n) :
    MinusLong n (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) :=
  .of_eq (Fin.ne_of_val_ne (by simp)) true true (toStdB_B2long h)

end Coordinates

section Relations

variable {n : ℕ} {F : Type} [Field F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

section Long

theorem minusXL_single {k : Fin (n - 1)} (hk : k.val + 2 < n) (a : F) :
    minusXL n b c (Pi.single k 1) a =
      mlr n b c k (⟨k.val + 1, by omega⟩ : Fin (n - 1)) true false a :=
  minusXL_eq (succ_ne_of_lt n (by omega)) true false (toStdB_single_of_lt' n (by omega)) a

theorem minus_comm_A2 {i : Fin (n - 1)} (h : i.val + 3 < n) (s t : F) :
    ⁅minusXL n b c (Pi.single i 1) s,
        minusXL n b c (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) t⁆ =
      minusXL n b c (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
        (s * t) := by
  have h01 : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  have h12 : (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ≠ ⟨i.val + 2, by omega⟩ :=
    Fin.ne_of_val_ne (by simp)
  have h02 : i ≠ (⟨i.val + 2, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXL_single (by omega), minusXL_single (k := ⟨i.val + 1, by omega⟩) (by simp; omega),
    minusXL_eq h02 true false (toStdB_A2sum h), mlr_of_ne h01, mlr_of_ne h12, mlr_of_ne h02]
  exact HypFrame.commutator_longRoot_longRoot _ h01 h12 h02 true false false s t

theorem minus_commute_A2_left {i : Fin (n - 1)} (h : i.val + 3 < n) (s t : F) :
    Commute (minusXL n b c (Pi.single i 1) s)
      (minusXL n b c (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) t) := by
  have h01 : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  have h02 : i ≠ (⟨i.val + 2, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXL_single (by omega), minusXL_eq h02 true false (toStdB_A2sum h), mlr_of_ne h01,
    mlr_of_ne h02]
  exact HypFrame.commute_longRoot_longRoot_left _ h01 h02 true false false s t

theorem minus_commute_A2_right {i : Fin (n - 1)} (h : i.val + 3 < n) (s t : F) :
    Commute
      (minusXL n b c (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) s)
      (minusXL n b c (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) t) := by
  have h12 : (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ≠ ⟨i.val + 2, by omega⟩ :=
    Fin.ne_of_val_ne (by simp)
  have h02 : i ≠ (⟨i.val + 2, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXL_single (k := ⟨i.val + 1, by omega⟩) (by simp; omega),
    minusXL_eq h02 true false (toStdB_A2sum h), mlr_of_ne h12, mlr_of_ne h02]
  exact HypFrame.commute_longRoot_longRoot_right _ h02 h12 true false true s t

theorem minus_commute_A1A1_long {i j : Fin (n - 1)} (hij : i.val + 2 ≤ j.val) (hj : j.val + 2 < n)
    (s t : F) :
    Commute (minusXL n b c (Pi.single i 1) s) (minusXL n b c (Pi.single j 1) t) := by
  have hi : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  have hj' : j ≠ (⟨j.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXL_single (by omega), minusXL_single hj, mlr_of_ne hi, mlr_of_ne hj']
  exact HypFrame.commute_longRoot_longRoot_of_disjoint _ hi hj' (Fin.ne_of_val_ne (by omega))
    (Fin.ne_of_val_ne (by simp; omega)) (Fin.ne_of_val_ne (by simp; omega))
    (Fin.ne_of_val_ne (by simp; omega)) true false true false s t

end Long

theorem minus_commute_A1A1_short {i k : Fin (n - 1)} (hik : i.val + 2 ≤ k.val)
    (hk : k.val + 2 = n) (s : F) (p : Fin 2 → F) :
    Commute (minusXL n b c (Pi.single i 1) s) (minusXS n hirr (Pi.single k 1) p) := by
  have hi : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXL_single (by omega), minusXS_eq hirr k true (toStdB_single_of_not_lt' n (by omega)),
    mlr_of_ne hi]
  exact commute_longRoot_twShortRoot_of_ne n hirr hi (Fin.ne_of_val_ne (by omega))
    (Fin.ne_of_val_ne (by simp; omega)) true false true s p

section B2

variable {i : Fin (n - 1)} (h : i.val + 3 = n)
include h

omit [CharP F 2] in
theorem minusXS_B2short (p : Fin 2 → F) :
    minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p =
      msr n hirr ⟨i.val + 1, by omega⟩ true p :=
  minusXS_eq hirr _ true (toStdB_single_of_not_lt' n (by simp; omega)) p

omit [CharP F 2] in
theorem minusXS_B2sum (p : Fin 2 → F) :
    minusXS n hirr (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p =
      msr n hirr i true p :=
  minusXS_eq hirr i true (toStdB_B2sum h) p

omit hirr in
theorem minusXL_B2long (a : F) :
    minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) a =
      mlr n b c i ⟨i.val + 1, by omega⟩ true true a :=
  minusXL_eq (Fin.ne_of_val_ne (by simp)) true true (toStdB_B2long h) a

theorem minus_comm_B2 (p : Fin 2 → F) (s : F) :
    ⁅minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p,
        minusXL n b c (Pi.single i 1) s⁆ =
      minusXS n hirr (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) (s • p) *
        minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
          (s * planeNorm b c p) := by
  have h01 : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  have e : ⁅minusXL n b c (Pi.single i 1) s,
      minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p⁆ =
      minusXS n hirr (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) (s • p) *
        minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
          (s * planeNorm b c p) := by
    rw [minusXL_single (by omega), minusXS_B2short hirr h, minusXS_B2sum hirr h,
      minusXL_B2long h, mlr_of_ne h01, mlr_of_ne h01]
    exact commutator_longRoot_twShortRoot n hirr h01 true false s p
  have hc : Commute
      (minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
        (s * planeNorm b c p))
      (minusXS n hirr (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
        (s • p)) := by
    rw [minusXS_B2sum hirr h, minusXL_B2long h, mlr_of_ne h01]
    exact commute_longRoot_twShortRoot_left n hirr h01 true true _ _
  rw [← commutatorElement_inv, e, _root_.mul_inv_rev,
    inv_eq_of_mul_eq_one_left (minusXL_mul_self _ _), inv_eq_of_mul_eq_one_left
      (minusXS_mul_self hirr _ _)]
  exact hc.eq

theorem minus_comm_B2' (p q : Fin 2 → F) :
    ⁅minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p,
        minusXS n hirr (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) q⁆ =
      minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
        (polarPlane b c p q) := by
  have h10 : (⟨i.val + 1, by omega⟩ : Fin (n - 1)) ≠ i := Fin.ne_of_val_ne (by simp)
  rw [minusXS_B2short hirr h, minusXS_B2sum hirr h, minusXL_B2long h, mlr_swap,
    ← CharTwo.neg_eq (polarPlane b c p q), mlr_of_ne h10]
  exact commutator_twShortRoot_twShortRoot n hirr h10 true true p q

theorem minus_commute_B2_b_2ab (p : Fin 2 → F) (s : F) :
    Commute (minusXS n hirr (Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p)
      (minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
        s) := by
  have h01 : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXS_B2short hirr h, minusXL_B2long h, mlr_of_ne h01]
  exact (commute_longRoot_twShortRoot_right n hirr h01 true true s p).symm

theorem minus_commute_B2_ab_2ab (p : Fin 2 → F) (s : F) :
    Commute (minusXS n hirr (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p)
      (minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1)
        s) := by
  have h01 : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXS_B2sum hirr h, minusXL_B2long h, mlr_of_ne h01]
  exact (commute_longRoot_twShortRoot_left n hirr h01 true true s p).symm

theorem minus_commute_B2_ab_a (p : Fin 2 → F) (s : F) :
    Commute (minusXS n hirr (Pi.single i 1 + Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) p)
      (minusXL n b c (Pi.single i 1) s) := by
  have h01 : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXS_B2sum hirr h, minusXL_single (by omega), mlr_of_ne h01]
  exact (commute_longRoot_twShortRoot_left n hirr h01 true false s p).symm

omit hirr in
theorem minus_commute_B2_2ab_a (s t : F) :
    Commute
      (minusXL n b c (Pi.single i 1 + 2 • Pi.single (⟨i.val + 1, by omega⟩ : Fin (n - 1)) 1) s)
      (minusXL n b c (Pi.single i 1) t) := by
  have h01 : i ≠ (⟨i.val + 1, by omega⟩ : Fin (n - 1)) := Fin.ne_of_val_ne (by simp)
  rw [minusXL_B2long h, minusXL_single (by omega), mlr_of_ne h01, mlr_of_ne h01]
  exact HypFrame.commute_longRoot_longRoot_left _ h01 h01 true true false s t

end B2

end Relations

section RankOne

variable {n : ℕ} {F : Type} [Field F] [CharP F 2] {b c : F}
  (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)

omit hirr in
theorem exists_sl2_minusXL {k : Fin (n - 1)} (hk : k.val + 2 < n) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 2) F →* spinGroup (quadMinus n F b c),
      Function.Injective φ ∧ (∀ x, φ (sl2Upper x) = minusXL n b c (Pi.single k 1) x) ∧
        ∀ x, φ (sl2Lower x) = minusXL n b c (-Pi.single k 1) x := by
  have hk' : k.val + 1 < n - 1 := by omega
  refine ⟨(minusFrame n b c).longSL2 (succ_ne_of_lt n hk') true false,
    SpinFrame.longSL2_injective _ _ _ _, fun x => ?_, fun x => ?_⟩
  · rw [minusXL_single hk, mlr_of_ne (succ_ne_of_lt n hk')]
    exact HypFrame.longSL2_upperSL2 _ _ _ _ x
  · rw [minusXL_eq (succ_ne_of_lt n hk').symm true false (toStdB_neg_single_of_lt' n hk'),
      mlr_of_ne (succ_ne_of_lt n hk').symm]
    exact HypFrame.longSL2_lowerSL2 _ _ _ _ x

theorem exists_sl2_minusXS [Finite F] [Fact (∀ r : F, r ^ 2 ≠ -c + b * r)] {k : Fin (n - 1)}
    (hk : k.val + 2 = n) :
    ∃ φ : SL2E b c →* spinGroup (quadMinus n F b c),
      Function.Injective φ ∧
        (∀ t, φ (sl2Upper t) = minusXS n hirr (Pi.single k 1) (fieldCoord t)) ∧
        ∀ t, φ (sl2Lower t) = minusXS n hirr (-Pi.single k 1) (starCoord t) := by
  have := finite_shortField (b := b) (c := c)
  have : CharP (ShortField b c) 2 :=
    charP_of_injective_algebraMap QuadraticAlgebra.algebraMap_injective 2
  obtain ⟨Θ, hU, hL⟩ := exists_hom_of_rankOneRels (shortRels n hirr k)
  have hk' : ¬ k.val + 1 < n - 1 := by omega
  have ex : ∀ t, (shortRels n hirr k).x t = minusXS n hirr (Pi.single k 1) (fieldCoord t) :=
    fun t => by
      rw [shortRels_x, minusXS_eq hirr k true (toStdB_single_of_not_lt' n hk'), msr]
      rfl
  have ey : ∀ t, (shortRels n hirr k).y t = minusXS n hirr (-Pi.single k 1) (starCoord t) :=
    fun t => by
      rw [shortRels_y, minusXS_eq hirr k false (toStdB_neg_single_of_not_lt' n hk'), msr]
      rfl
  refine ⟨Θ, injective_of_sl2_charTwo four_le_card_shortField Θ ?_, fun t => (hU t).trans (ex t),
    fun t => (hL t).trans (ey t)⟩
  rw [hU, shortRels_x]
  intro h1
  have h2 := congrArg Multiplicative.toAdd (shortPosHom_injective n hirr k
    (h1.trans (map_one _).symm))
  rw [toAdd_ofAdd, toAdd_one, fieldCoord_one] at h2
  exact planeOne_ne_zero h2

end RankOne

end CFSG.Timmesfeld.RankTwo
