module

public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin

namespace E9P2.Lines

variable {Y : Type*} [Group Y]

@[expose] def lines (K : Subgroup Y) : Set (Subgroup Y) := {A | A ≤ K ∧ Nat.card A = 3}

theorem eq_one_or_eq_or_eq_inv {A : Subgroup Y} (hA : Nat.card A = 3) {a x : Y} (ha : a ∈ A)
    (ha1 : a ≠ 1) (hx : x ∈ A) : x = 1 ∨ x = a ∨ x = a⁻¹ := by
  have hord : orderOf a = 3 := by
    have h1 : orderOf a ∣ 3 := hA ▸ Subgroup.orderOf_dvd_natCard A ha
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) ha1
    · exact h
  have hfin : Finite A := Nat.finite_of_card_ne_zero (by omega)
  have hz : Subgroup.zpowers a = A :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr ha) (by rw [Nat.card_zpowers, hord, hA])
  rw [← hz] at hx
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  have ha3 : a ^ 3 = 1 := hord ▸ pow_orderOf_eq_one a
  have hmod : a ^ n = a ^ (n % 3) := by
    have := zpow_mod_orderOf a n
    rw [hord, Nat.cast_ofNat] at this
    exact this.symm
  rw [hmod]
  have hcases : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2 := by omega
  rcases hcases with h | h | h
  · left; rw [h, zpow_zero]
  · right; left; rw [h, zpow_one]
  · right; right; rw [h]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← zpow_add_one]
    simpa using ha3

theorem exists_ne_one_of_card_eq_three {A : Subgroup Y} (hA : Nat.card A = 3) :
    ∃ a ∈ A, a ≠ 1 := by
  by_contra h
  have h1 : ∀ a ∈ A, a = 1 := fun a ha => by_contra fun h1 => h ⟨a, ha, h1⟩
  rw [(Subgroup.eq_bot_iff_forall A).mpr h1, Subgroup.card_bot] at hA
  omega

theorem eq_one_of_eq_inv {k : Y} (hk3 : k ^ 3 = 1) (h : k = k⁻¹) : k = 1 := by
  have h2 : k ^ 2 = 1 := by
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h
  calc k = k ^ 3 * (k ^ 2)⁻¹ := by group
    _ = 1 := by rw [hk3, h2]; simp

theorem zpowers_mem_lines {K : Subgroup Y} {k : Y} (hk : k ∈ K) (hk3 : k ^ 3 = 1) (hk1 : k ≠ 1) :
    Subgroup.zpowers k ∈ lines K :=
  ⟨Subgroup.zpowers_le.mpr hk, by rw [Nat.card_zpowers]; exact orderOf_eq_prime hk3 hk1⟩

theorem card_lines {K : Subgroup Y} (h9 : Nat.card K = 9) (hexp : ∀ k ∈ K, k ^ 3 = 1) :
    Nat.card (lines K) = 4 := by
  classical
  have : Finite K := Nat.finite_of_card_ne_zero (by omega)
  have : Fintype K := Fintype.ofFinite K
  let S : Finset K := Finset.univ.erase 1
  let f : K → Subgroup Y := fun k => Subgroup.zpowers (k : Y)
  have hS : S.card = 8 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, h9]
  have hmemS : ∀ k : K, k ∈ S ↔ (k : Y) ≠ 1 := fun k => by
    simp only [S, Finset.mem_erase, Finset.mem_univ, and_true, ne_eq]
    exact ⟨fun h h1 => h (Subtype.ext h1), fun h h1 => h (by rw [h1]; rfl)⟩
  have himage : lines K = ↑(S.image f) := by
    ext A
    constructor
    · intro hA
      obtain ⟨a, haA, ha1⟩ := exists_ne_one_of_card_eq_three hA.2
      refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨⟨a, hA.1 haA⟩, (hmemS _).mpr ha1, ?_⟩)
      have hfin : Finite A := Nat.finite_of_card_ne_zero (by rw [hA.2]; omega)
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr haA) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime ((hexp a (hA.1 haA))) ha1, hA.2]
    · intro hA
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hA)
      exact zpowers_mem_lines k.2 (hexp k k.2) ((hmemS k).mp hk)
  have hfiber : ∀ A ∈ S.image f, (S.filter fun k => f k = A).card = 2 := by
    intro A hA
    obtain ⟨a, haS, rfl⟩ := Finset.mem_image.mp hA
    have ha1 : (a : Y) ≠ 1 := (hmemS a).mp haS
    have hline := zpowers_mem_lines a.2 (hexp a a.2) ha1
    have hinv : a⁻¹ ≠ a := fun h => ha1 (eq_one_of_eq_inv (hexp a a.2) (by
      have := congrArg Subtype.val h
      exact this.symm))
    have hfil : S.filter (fun k => f k = f a) = {a, a⁻¹} := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hk, hfk⟩
        have hfk' : Subgroup.zpowers (k : Y) = Subgroup.zpowers (a : Y) := hfk
        have hmem : (k : Y) ∈ Subgroup.zpowers (a : Y) := hfk' ▸ Subgroup.mem_zpowers (k : Y)
        rcases eq_one_or_eq_or_eq_inv hline.2 (Subgroup.mem_zpowers _) ha1 hmem with h | h | h
        · exact absurd h ((hmemS k).mp hk)
        · exact Or.inl (Subtype.ext h)
        · exact Or.inr (Subtype.ext h)
      · rintro (rfl | rfl)
        · exact ⟨haS, rfl⟩
        · refine ⟨(hmemS _).mpr ?_, ?_⟩
          · intro h
            exact ha1 (by simpa using h)
          · show Subgroup.zpowers (((a⁻¹ : K)) : Y) = _
            rw [Subgroup.coe_inv]
            exact Subgroup.zpowers_inv
    rw [hfil, Finset.card_pair hinv.symm]
  have hsum := Finset.card_eq_sum_card_image f S
  rw [Finset.sum_congr rfl hfiber, Finset.sum_const, smul_eq_mul, hS] at hsum
  have h4 : (S.image f).card = 4 := by omega
  rw [himage, ← h4]
  exact Nat.card_eq_finsetCard _

theorem moves_line_of_sq_inverts {K : Subgroup Y} (hexp : ∀ k ∈ K, k ^ 3 = 1) {σ : Y}
    (hσ2 : ∀ k ∈ K, σ ^ 2 * k * σ⁻¹ ^ 2 = k⁻¹) {A : Subgroup Y} (hA : A ∈ lines K) :
    conjSub σ A ≠ A := by
  intro hfix
  obtain ⟨a, haA, ha1⟩ := exists_ne_one_of_card_eq_three hA.2
  have haK : a ∈ K := hA.1 haA
  have hconj : σ * a * σ⁻¹ ∈ A := hfix ▸ mul_mem_conjSub haA
  have hs2 : σ ^ 2 * a * σ⁻¹ ^ 2 = a := by
    rcases eq_one_or_eq_or_eq_inv hA.2 haA ha1 hconj with h | h | h
    · exact absurd (by simpa using h) ha1
    · calc σ ^ 2 * a * σ⁻¹ ^ 2 = σ * (σ * a * σ⁻¹) * σ⁻¹ := by simp only [pow_two, mul_assoc]
        _ = a := by rw [h]; exact h
    · calc σ ^ 2 * a * σ⁻¹ ^ 2 = σ * (σ * a * σ⁻¹) * σ⁻¹ := by simp only [pow_two, mul_assoc]
        _ = σ * a⁻¹ * σ⁻¹ := by rw [h]
        _ = (σ * a * σ⁻¹)⁻¹ := by group
        _ = a := by rw [h, inv_inv]
  exact ha1 (eq_one_of_eq_inv (hexp a haK) (hs2.symm.trans (hσ2 a haK)))

theorem centralizes_of_fixes_lines {K : Subgroup Y} (hexp : ∀ k ∈ K, k ^ 3 = 1) {g : Y}
    (hodd : ¬ 2 ∣ orderOf g) (hfix : ∀ A ∈ lines K, conjSub g A = A) :
    ∀ k ∈ K, g * k * g⁻¹ = k := by
  intro k hk
  by_contra hne
  have hk1 : k ≠ 1 := by
    rintro rfl
    exact hne (by simp)
  have hline := zpowers_mem_lines hk (hexp k hk) hk1
  have hmem : g * k * g⁻¹ ∈ Subgroup.zpowers k :=
    hfix _ hline ▸ mul_mem_conjSub (Subgroup.mem_zpowers k)
  have hinv : g * k * g⁻¹ = k⁻¹ := by
    rcases eq_one_or_eq_or_eq_inv hline.2 (Subgroup.mem_zpowers k) hk1 hmem with h | h | h
    · exact absurd (by simpa using h) hk1
    · exact absurd h hne
    · exact h
  have hg2 : g ^ 2 * k * (g ^ 2)⁻¹ = k := by
    calc g ^ 2 * k * (g ^ 2)⁻¹ = g * (g * k * g⁻¹) * g⁻¹ := by
          simp only [pow_two, mul_inv_rev, mul_assoc]
      _ = g * k⁻¹ * g⁻¹ := by rw [hinv]
      _ = (g * k * g⁻¹)⁻¹ := by group
      _ = k := by rw [hinv, inv_inv]
  have heven : ∀ m : ℕ, g ^ (2 * m) * k * (g ^ (2 * m))⁻¹ = k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc g ^ (2 * (m + 1)) * k * (g ^ (2 * (m + 1)))⁻¹
          = g ^ (2 * m) * (g ^ 2 * k * (g ^ 2)⁻¹) * (g ^ (2 * m))⁻¹ := by group
        _ = k := by rw [hg2, ih]
  obtain ⟨m, hm⟩ : ∃ m, orderOf g = 2 * m + 1 := ⟨orderOf g / 2, by omega⟩
  have h1 : g ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one g
  have hkk : k = k⁻¹ := by
    calc k = g ^ (2 * m + 1) * k * (g ^ (2 * m + 1))⁻¹ := by rw [h1]; simp
      _ = g ^ (2 * m) * (g * k * g⁻¹) * (g ^ (2 * m))⁻¹ := by group
      _ = g ^ (2 * m) * k⁻¹ * (g ^ (2 * m))⁻¹ := by rw [hinv]
      _ = (g ^ (2 * m) * k * (g ^ (2 * m))⁻¹)⁻¹ := by group
      _ = k⁻¹ := by rw [heven m]
  exact hk1 (eq_one_of_eq_inv (hexp k hk) hkk)

section Action

theorem conjSub_mem_lines {K : Subgroup Y} {n : Y} (hn : n ∈ Subgroup.normalizer (K : Set Y))
    {A : Subgroup Y} (hA : A ∈ lines K) : conjSub n A ∈ lines K := by
  refine ⟨fun x hx => ?_, ?_⟩
  · exact (Subgroup.mem_normalizer_iff''.mp hn x).mpr (hA.1 (mem_conjSub.mp hx))
  · rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    exact hA.2

@[expose] def linePerm (K : Subgroup Y) (n : Subgroup.normalizer (K : Set Y)) :
    Equiv.Perm (lines K) where
  toFun A := ⟨conjSub (n : Y) A, conjSub_mem_lines n.2 A.2⟩
  invFun A := ⟨conjSub (n : Y)⁻¹ A, conjSub_mem_lines (Subgroup.inv_mem _ n.2) A.2⟩
  left_inv _ := Subtype.ext (conjSub_conjSub_inv _ _)
  right_inv _ := Subtype.ext (conjSub_inv_conjSub _ _)

@[expose] def linePermHom (K : Subgroup Y) :
    Subgroup.normalizer (K : Set Y) →* Equiv.Perm (lines K) where
  toFun := linePerm K
  map_one' := Equiv.ext fun _ => Subtype.ext (conjSub_one _)
  map_mul' _ _ := Equiv.ext fun _ => Subtype.ext (conjSub_mul _ _ _)

end Action

end E9P2.Lines

end CFSG.Quasithin
