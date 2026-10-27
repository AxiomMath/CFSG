module

public import CFSG.RankThree.PartOne.CTP.StrongPNoncentral

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthGraph

open Matrix CFSG.RankThree.PartOne.StrongP

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]

private theorem mul_apply_of_ne (a b : GL ι K) {i j : ι} (hij : i ≠ j) :
    ((a * b : GL ι K) : Matrix ι ι K) i j = (a : Matrix ι ι K) i j + (b : Matrix ι ι K) i j +
      (((a : Matrix ι ι K) - 1) * ((b : Matrix ι ι K) - 1)) i j := by
  have e : ((a * b : GL ι K) : Matrix ι ι K) =
      ((a : Matrix ι ι K) - 1) * ((b : Matrix ι ι K) - 1) + ((a : Matrix ι ι K) - 1) +
        ((b : Matrix ι ι K) - 1) + 1 := by
    rw [Units.val_mul]; noncomm_ring
  rw [e]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.one_apply_ne hij]
  ring

private theorem mul_apply_of_vanish {r : ι → ℕ} {a b : GL ι K} (ha : IsUnitri r a)
    (hb : IsUnitri r b) {i j : ι} (hij : r i < r j)
    (h : ∀ l, r i < r l → r l < r j → (a : Matrix ι ι K) i l = 0) :
    ((a * b : GL ι K) : Matrix ι ι K) i j = (a : Matrix ι ι K) i j + (b : Matrix ι ι K) i j := by
  rw [mul_apply_of_ne a b (ne_of_apply_ne r hij.ne)]
  have hs : (((a : Matrix ι ι K) - 1) * ((b : Matrix ι ι K) - 1)) i j = 0 := by
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun l _ => ?_
    by_cases h1 : ((a : Matrix ι ι K) - 1) i l = 0
    · rw [h1, zero_mul]
    by_cases h2 : ((b : Matrix ι ι K) - 1) l j = 0
    · rw [h2, mul_zero]
    have hil := ha i l h1
    have hlj := hb l j h2
    exact absurd (by rw [Matrix.sub_apply, h l hil hlj, Matrix.one_apply_ne
      (ne_of_apply_ne r hil.ne), sub_zero]) h1
  rw [hs, add_zero]

private def Good (r : ι → ℕ) (P : Finset (ι × ι)) : Prop :=
  ∀ p ∈ P, r p.1 < r p.2 ∧ ∀ q : ι × ι, r q.1 < r q.2 → r q.2 - r q.1 < r p.2 - r p.1 → q ∈ P

private def filtMon (r : ι → ℕ) (A : Subgroup (GL ι K)) (hAu : ∀ a ∈ A, IsUnitri r a)
    (P : Finset (ι × ι)) (hP : Good r P) : Submonoid (GL ι K) where
  carrier := {a | a ∈ A ∧ ∀ p ∈ P, (a : Matrix ι ι K) p.1 p.2 = 0}
  mul_mem' := by
    rintro a b ⟨haA, ha⟩ ⟨hbA, hb⟩
    refine ⟨A.mul_mem haA hbA, fun p hp => ?_⟩
    obtain ⟨hpos, hq⟩ := hP p hp
    rw [mul_apply_of_vanish (hAu a haA) (hAu b hbA) hpos, ha p hp, hb p hp, add_zero]
    intro l h1 h2
    exact ha (p.1, l) (hq (p.1, l) h1 (by show r l - r p.1 < r p.2 - r p.1; omega))
  one_mem' := by
    refine ⟨A.one_mem, fun p hp => ?_⟩
    rw [Units.val_one, Matrix.one_apply_ne (ne_of_apply_ne r (hP p hp).1.ne)]

private def filt (r : ι → ℕ) (A : Subgroup (GL ι K)) (hAu : ∀ a ∈ A, IsUnitri r a)
    (P : Finset (ι × ι)) (hP : Good r P) : Subgroup (GL ι K) :=
  { filtMon r A hAu P hP with
    inv_mem' := fun {a} ha => by
      have h : a ^ (orderOf a - 1) * a = 1 := by
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos a), pow_orderOf_eq_one]
      rw [← eq_inv_of_mul_eq_one_left h]
      exact (filtMon r A hAu P hP).pow_mem ha _ }

private theorem mem_filt {r : ι → ℕ} {A : Subgroup (GL ι K)} {hAu : ∀ a ∈ A, IsUnitri r a}
    {P : Finset (ι × ι)} {hP : Good r P} {a : GL ι K} :
    a ∈ filt r A hAu P hP ↔ a ∈ A ∧ ∀ p ∈ P, (a : Matrix ι ι K) p.1 p.2 = 0 :=
  Iff.rfl

private theorem exists_pow_of_ker {G : Type*} [Group G] (φ : G →* Multiplicative K)
    (hmul : ∀ (u : Kˣ) (g : G),
      ∃ g' : G, Multiplicative.toAdd (φ g') = (u : K) * Multiplicative.toAdd (φ g))
    (hker : ∃ m : ℕ, Nat.card φ.ker = Nat.card K ^ m) :
    ∃ m : ℕ, Nat.card G = Nat.card K ^ m := by
  obtain ⟨m, hm⟩ := hker
  rw [← Subgroup.card_ker_mul_card_range φ, hm]
  by_cases h : ∀ g, Multiplicative.toAdd (φ g) = 0
  · refine ⟨m, ?_⟩
    have hbot : φ.range = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨g, rfl⟩
      exact Subgroup.mem_bot.2 (toAdd_eq_zero.1 (h g))
    rw [hbot, Subgroup.card_bot, mul_one]
  · obtain ⟨g₀, hg₀⟩ := not_forall.1 h
    have hsurj : Function.Surjective φ := by
      intro x
      by_cases hx : Multiplicative.toAdd x = 0
      · exact ⟨1, by rw [map_one, toAdd_eq_zero.1 hx]⟩
      · obtain ⟨g', hg'⟩ := hmul (Units.mk0 (Multiplicative.toAdd x / Multiplicative.toAdd (φ g₀))
          (div_ne_zero hx hg₀)) g₀
        refine ⟨g', Multiplicative.toAdd.injective ?_⟩
        rw [hg', Units.val_mk0, div_mul_cancel₀ _ hg₀]
    refine ⟨m + 1, ?_⟩
    rw [MonoidHom.range_eq_top_of_surjective φ hsurj, Subgroup.card_top, pow_succ,
      Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K)]

private theorem conj_apply {T : Type*} (D : T → GL ι K) (χ : T → ι → Kˣ)
    (hD : ∀ t, (D t : Matrix ι ι K) = Matrix.diagonal fun i => ((χ t i : Kˣ) : K))
    (t : T) (a : GL ι K) (k l : ι) :
    ((D t * a * (D t)⁻¹ : GL ι K) : Matrix ι ι K) k l =
      (χ t k : K) * (a : Matrix ι ι K) k l * (((χ t l)⁻¹ : Kˣ) : K) := by
  have hX : (D t : Matrix ι ι K) * Matrix.diagonal (fun i => (((χ t i)⁻¹ : Kˣ) : K)) = 1 := by
    rw [hD, Matrix.diagonal_mul_diagonal]
    simp only [Units.mul_inv]
    exact Matrix.diagonal_one
  rw [Units.val_mul, Units.val_mul, Units.inv_eq_of_mul_eq_one_right hX, hD,
    Matrix.mul_diagonal, Matrix.diagonal_mul]

private theorem conj_mem {T : Type*} (D : T → GL ι K) (χ : T → ι → Kˣ)
    (hD : ∀ t, (D t : Matrix ι ι K) = Matrix.diagonal fun i => ((χ t i : Kˣ) : K))
    {r : ι → ℕ} {A : Subgroup (GL ι K)} {hAu : ∀ a ∈ A, IsUnitri r a}
    (hAT : ∀ t, ∀ a ∈ A, D t * a * (D t)⁻¹ ∈ A)
    {P : Finset (ι × ι)} {hP : Good r P} (t : T) {a : GL ι K} (ha : a ∈ filt r A hAu P hP) :
    D t * a * (D t)⁻¹ ∈ filt r A hAu P hP := by
  obtain ⟨haA, ha0⟩ := mem_filt.1 ha
  refine mem_filt.2 ⟨hAT t a haA, fun p hp => ?_⟩
  rw [conj_apply D χ hD, ha0 p hp, mul_zero, zero_mul]

private theorem good_insert {r : ι → ℕ} {P : Finset (ι × ι)} (hP : Good r P) {i j : ι}
    (hij : r i < r j)
    (hmin : ∀ q : ι × ι, r q.1 < r q.2 → r q.2 - r q.1 < r j - r i → q ∈ P) :
    Good r (insert (i, j) P) := by
  intro p hp
  rcases Finset.mem_insert.1 hp with rfl | hp
  · exact ⟨hij, fun q hq hlt => Finset.mem_insert_of_mem (hmin q hq hlt)⟩
  · obtain ⟨h1, h2⟩ := hP p hp
    exact ⟨h1, fun q hq hlt => Finset.mem_insert_of_mem (h2 q hq hlt)⟩

private theorem step_pow (r : ι → ℕ) {T : Type*} (D : T → GL ι K) (χ : T → ι → Kˣ)
    (hD : ∀ t, (D t : Matrix ι ι K) = Matrix.diagonal fun i => ((χ t i : Kˣ) : K))
    (A : Subgroup (GL ι K)) (hAu : ∀ a ∈ A, IsUnitri r a)
    (hAT : ∀ t, ∀ a ∈ A, D t * a * (D t)⁻¹ ∈ A)
    (hroot : ∀ i j, r i < r j → (∀ a ∈ A, (a : Matrix ι ι K) i j = 0) ∨
      Function.Surjective fun t => χ t i * (χ t j)⁻¹)
    {P : Finset (ι × ι)} (hP : Good r P) {i j : ι} (hij : r i < r j)
    (hmin : ∀ q : ι × ι, r q.1 < r q.2 → r q.2 - r q.1 < r j - r i → q ∈ P)
    (h : ∃ m : ℕ, Nat.card (filt r A hAu (insert (i, j) P) (good_insert hP hij hmin)) =
      Nat.card K ^ m) :
    ∃ m : ℕ, Nat.card (filt r A hAu P hP) = Nat.card K ^ m := by
  let φ : filt r A hAu P hP →* Multiplicative K := MonoidHom.mk' (fun a =>
      Multiplicative.ofAdd (((a : GL ι K) : Matrix ι ι K) i j)) (by
    intro a b
    have key := mul_apply_of_vanish (hAu a (mem_filt.1 a.2).1) (hAu b (mem_filt.1 b.2).1) hij
      (fun l h1 h2 => (mem_filt.1 a.2).2 (i, l)
        (hmin (i, l) h1 (by show r l - r i < r j - r i; omega)))
    exact congrArg Multiplicative.ofAdd key)
  have hφ : ∀ a : filt r A hAu P hP,
      Multiplicative.toAdd (φ a) = ((a : GL ι K) : Matrix ι ι K) i j := fun a => rfl
  have hmul : ∀ (u : Kˣ) (a : filt r A hAu P hP), ∃ a' : filt r A hAu P hP,
      Multiplicative.toAdd (φ a') = (u : K) * Multiplicative.toAdd (φ a) := by
    intro u a
    rcases hroot i j hij with hz | hs
    · refine ⟨a, ?_⟩
      rw [hφ, hz a (mem_filt.1 a.2).1, mul_zero]
    · obtain ⟨t, ht⟩ := hs u
      have ht' : χ t i * (χ t j)⁻¹ = u := ht
      refine ⟨⟨D t * a * (D t)⁻¹, conj_mem D χ hD hAT t a.2⟩, ?_⟩
      rw [hφ, hφ]
      show ((D t * (a : GL ι K) * (D t)⁻¹ : GL ι K) : Matrix ι ι K) i j = _
      rw [conj_apply D χ hD, ← ht', Units.val_mul]
      ring
  have hle : filt r A hAu (insert (i, j) P) (good_insert hP hij hmin) ≤ filt r A hAu P hP := by
    intro a ha
    obtain ⟨haA, ha0⟩ := mem_filt.1 ha
    exact mem_filt.2 ⟨haA, fun p hp => ha0 p (Finset.mem_insert_of_mem hp)⟩
  have hker : φ.ker = (filt r A hAu (insert (i, j) P) (good_insert hP hij hmin)).subgroupOf
      (filt r A hAu P hP) := by
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_filt]
    have ha := mem_filt.1 a.2
    constructor
    · intro h1
      refine ⟨ha.1, fun p hp => ?_⟩
      rcases Finset.mem_insert.1 hp with rfl | hp
      · exact toAdd_eq_zero.2 h1
      · exact ha.2 p hp
    · rintro ⟨-, h1⟩
      exact toAdd_eq_zero.1 (h1 (i, j) (Finset.mem_insert_self _ _))
  have hcard : Nat.card φ.ker =
      Nat.card (filt r A hAu (insert (i, j) P) (good_insert hP hij hmin)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  refine exists_pow_of_ker φ hmul ?_
  rw [hcard]
  exact h

private def positions (r : ι → ℕ) : Finset (ι × ι) :=
  Finset.univ.filter fun q => r q.1 < r q.2

private theorem mem_positions {r : ι → ℕ} {q : ι × ι} : q ∈ positions r ↔ r q.1 < r q.2 := by
  simp [positions]

private theorem card_filt_eq_pow (r : ι → ℕ) {T : Type*} (D : T → GL ι K) (χ : T → ι → Kˣ)
    (hD : ∀ t, (D t : Matrix ι ι K) = Matrix.diagonal fun i => ((χ t i : Kˣ) : K))
    (A : Subgroup (GL ι K)) (hAu : ∀ a ∈ A, IsUnitri r a)
    (hAT : ∀ t, ∀ a ∈ A, D t * a * (D t)⁻¹ ∈ A)
    (hroot : ∀ i j, r i < r j → (∀ a ∈ A, (a : Matrix ι ι K) i j = 0) ∨
      Function.Surjective fun t => χ t i * (χ t j)⁻¹) (n : ℕ) :
    ∀ (P : Finset (ι × ι)) (hP : Good r P), (positions r \ P).card = n →
      ∃ m : ℕ, Nat.card (filt r A hAu P hP) = Nat.card K ^ m := by
  induction n with
  | zero =>
    intro P hP hcard
    refine ⟨0, ?_⟩
    have hall : ∀ q : ι × ι, r q.1 < r q.2 → q ∈ P := by
      intro q hq
      by_contra hqP
      have hmem : q ∈ positions r \ P := Finset.mem_sdiff.2 ⟨mem_positions.2 hq, hqP⟩
      have := Finset.card_pos.2 ⟨q, hmem⟩
      omega
    have hbot : filt r A hAu P hP = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨haA, ha0⟩ := mem_filt.1 ha
      rw [Subgroup.mem_bot]
      apply Units.ext
      ext k l
      by_cases hkl : r k < r l
      · rw [Units.val_one, Matrix.one_apply_ne (ne_of_apply_ne r hkl.ne)]
        exact ha0 (k, l) (hall (k, l) hkl)
      · by_cases h0 : ((a : Matrix ι ι K) - 1) k l = 0
        · rw [Matrix.sub_apply, sub_eq_zero] at h0
          rw [Units.val_one]
          exact h0
        · exact absurd (hAu a haA k l h0) hkl
    rw [hbot, Subgroup.card_bot, pow_zero]
  | succ n ih =>
    intro P hP hcard
    have hne : (positions r \ P).Nonempty := Finset.card_pos.1 (by omega)
    obtain ⟨⟨i, j⟩, hp, hpmin⟩ :=
      Finset.exists_min_image (positions r \ P) (fun q => r q.2 - r q.1) hne
    obtain ⟨hpos, -⟩ := Finset.mem_sdiff.1 hp
    have hij : r i < r j := mem_positions.1 hpos
    have hmin : ∀ q : ι × ι, r q.1 < r q.2 → r q.2 - r q.1 < r j - r i → q ∈ P := by
      intro q hq hlt
      by_contra hqP
      have := hpmin q (Finset.mem_sdiff.2 ⟨mem_positions.2 hq, hqP⟩)
      simp only at this
      omega
    have hcard' : (positions r \ insert (i, j) P).card = n := by
      rw [Finset.sdiff_insert, Finset.card_erase_of_mem hp]
      omega
    exact step_pow r D χ hD A hAu hAT hroot hP hij hmin
      (ih _ (good_insert hP hij hmin) hcard')

theorem card_eq_pow_of_isUnitri (r : ι → ℕ) {T : Type*} (D : T → GL ι K) (χ : T → ι → Kˣ)
    (hD : ∀ t, (D t : Matrix ι ι K) = Matrix.diagonal fun i => ((χ t i : Kˣ) : K))
    (A : Subgroup (GL ι K)) (hAu : ∀ a ∈ A, IsUnitri r a)
    (hAT : ∀ t, ∀ a ∈ A, D t * a * (D t)⁻¹ ∈ A)
    (hroot : ∀ i j, r i < r j → (∀ a ∈ A, (a : Matrix ι ι K) i j = 0) ∨
      Function.Surjective fun t => χ t i * (χ t j)⁻¹) :
    ∃ m : ℕ, Nat.card A = Nat.card K ^ m := by
  have hP0 : Good r (∅ : Finset (ι × ι)) := fun p hp => by simp at hp
  obtain ⟨m, hm⟩ := card_filt_eq_pow r D χ hD A hAu hAT hroot _ ∅ hP0 rfl
  refine ⟨m, ?_⟩
  have hA : filt r A hAu ∅ hP0 = A := by
    ext a
    rw [mem_filt]
    simp
  rwa [hA] at hm

end CFSG.RankThree.GF2n.Smith81.OrthGraph
