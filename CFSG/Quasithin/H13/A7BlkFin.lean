module

public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.Quasithin.H13.A7Blk

open Equiv Equiv.Perm

@[expose] def t01 : Perm (Fin 7) := swap 0 1

@[expose] def t23 : Perm (Fin 7) := swap 2 3

@[expose] def t45 : Perm (Fin 7) := swap 4 5

@[expose] def n1 : Perm (Fin 7) := swap 0 1 * swap 2 3

@[expose] def n2 : Perm (Fin 7) := swap 0 2 * swap 1 3

@[expose] def n3 : Perm (Fin 7) := swap 0 1 * swap 4 5

@[expose] def pi3 : Perm (Fin 7) := swap 0 4 * swap 0 2 * (swap 1 5 * swap 1 3)

@[expose] def pstdL : List (Perm (Fin 7)) :=
  [1, n1, n2, n1 * n2, n3, n1 * n3, n2 * n3, n1 * n2 * n3]

@[expose] def tL : List (Perm (Fin 7)) := [t01, t23, t45]

@[expose] def dstdL : List (Perm (Fin 7)) :=
  [1, t01, t23, t45, t01 * t23, t01 * t45, t23 * t45, t01 * t23 * t45]

theorem all_true {α : Type*} {l : List α} {f : α → Bool} (h : l.all f = true) {a : α}
    (ha : a ∈ l) : f a = true :=
  List.all_eq_true.mp h a ha

theorem all_imp {α : Type*} {l : List α} {c f : α → Bool} (h : (l.all fun a => !c a || f a) = true)
    {a : α} (ha : a ∈ l) (hc : c a = true) : f a = true := by
  have := all_true h ha
  rw [hc, Bool.not_true, Bool.false_or] at this
  exact this

theorem chk_pstdL_mul : (pstdL.all fun a => pstdL.all fun b => pstdL.contains (a * b)) = true := by
  decide +kernel

theorem chk_pstdL_inv : (pstdL.all fun a => pstdL.contains a⁻¹) = true := by decide +kernel

theorem chk_dstdL_mul : (dstdL.all fun a => dstdL.all fun b => dstdL.contains (a * b)) = true := by
  decide +kernel

theorem chk_dstdL_inv : (dstdL.all fun a => dstdL.contains a⁻¹) = true := by decide +kernel

@[expose] def pstd : Subgroup (Perm (Fin 7)) where
  carrier := {σ | σ ∈ pstdL}
  one_mem' := by decide +kernel
  mul_mem' {a b} ha hb := List.contains_iff_mem.mp (all_true (all_true chk_pstdL_mul ha) hb)
  inv_mem' {a} ha := List.contains_iff_mem.mp (all_true chk_pstdL_inv ha)

@[expose] def dstd : Subgroup (Perm (Fin 7)) where
  carrier := {σ | σ ∈ dstdL}
  one_mem' := by decide +kernel
  mul_mem' {a b} ha hb := List.contains_iff_mem.mp (all_true (all_true chk_dstdL_mul ha) hb)
  inv_mem' {a} ha := List.contains_iff_mem.mp (all_true chk_dstdL_inv ha)

theorem mem_pstd {σ : Perm (Fin 7)} : σ ∈ pstd ↔ σ ∈ pstdL := Iff.rfl

theorem mem_dstd {σ : Perm (Fin 7)} : σ ∈ dstd ↔ σ ∈ dstdL := Iff.rfl

theorem n1_mem : n1 ∈ pstd := by
  show n1 ∈ pstdL
  decide +kernel

theorem n2_mem : n2 ∈ pstd := by
  show n2 ∈ pstdL
  decide +kernel

theorem n3_mem : n3 ∈ pstd := by
  show n3 ∈ pstdL
  decide +kernel

theorem chk_tL_sub : (tL.all fun τ => dstdL.contains τ) = true := by decide +kernel

theorem tL_sub {τ : Perm (Fin 7)} (h : τ ∈ tL) : τ ∈ dstd :=
  List.contains_iff_mem.mp (all_true chk_tL_sub h)

theorem chk_pstdL_sign : (pstdL.all fun p => Perm.sign p == 1) = true := by decide +kernel

theorem pstd_le_alternatingGroup : pstd ≤ alternatingGroup (Fin 7) := fun _ hp =>
  Perm.mem_alternatingGroup.mpr (beq_iff_eq.mp (all_true chk_pstdL_sign hp))

theorem chk_fix : ((List.finRange 7).all fun i => !(pstdL.all fun p => p i == i) || i == 6) =
    true := by
  decide +kernel

theorem eq_six_of_fix {i : Fin 7} (h : ∀ p ∈ pstd, p i = i) : i = 6 := by
  have h1 : (pstdL.all fun p => p i == i) = true :=
    List.all_eq_true.mpr fun p hp => beq_iff_eq.mpr (h p hp)
  exact beq_iff_eq.mp (all_imp (c := fun i => pstdL.all fun p => p i == i) chk_fix
    (List.mem_finRange i) h1)

theorem pstdL_card : pstdL.toFinset.card = 8 := by decide +kernel

theorem card_pstd : Nat.card pstd = 8 := by
  have h : (pstd : Set (Perm (Fin 7))) = ↑pstdL.toFinset := by
    ext σ
    simp [mem_pstd]
  rw [← SetLike.coe_sort_coe, h, Nat.card_coe_set_eq, Set.ncard_coe_finset, pstdL_card]

theorem chk_swap : ((List.finRange 7).all fun a => (List.finRange 7).all fun b =>
    !(!(a == b) && pstdL.all fun p => (swap a b * p) ^ 16 == 1) || tL.contains (swap a b)) =
    true := by
  decide +kernel

theorem swap_mem_tL {a b : Fin 7} (hab : a ≠ b) (h : ∀ p ∈ pstd, (swap a b * p) ^ 16 = 1) :
    swap a b ∈ tL := by
  have h1 := all_true chk_swap (List.mem_finRange a)
  have h2 := all_true h1 (List.mem_finRange b)
  have hc : (!(a == b) && pstdL.all fun p => (swap a b * p) ^ 16 == 1) = true := by
    rw [Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne]
    exact ⟨hab, List.all_eq_true.mpr fun p hp => beq_iff_eq.mpr (h p hp)⟩
  rw [hc, Bool.not_true, Bool.false_or] at h2
  exact List.contains_iff_mem.mp h2

theorem chk_pstd_mul : (tL.all fun τ => tL.all fun σ => pstdL.any fun p => pstdL.any fun q =>
    σ == p * τ * q) = true := by
  decide +kernel

theorem exists_mem_pstd_mul {τ σ : Perm (Fin 7)} (hτ : τ ∈ tL) (hσ : σ ∈ tL) :
    ∃ p ∈ pstd, ∃ q ∈ pstd, σ = p * τ * q := by
  have h := all_true (all_true chk_pstd_mul hτ) hσ
  obtain ⟨p, hp, h'⟩ := List.any_eq_true.mp h
  obtain ⟨q, hq, h''⟩ := List.any_eq_true.mp h'
  exact ⟨p, hp, q, hq, beq_iff_eq.mp h''⟩

theorem pi3_sign : Perm.sign pi3 = 1 := by decide +kernel

theorem pi3_mem : pi3 ∈ alternatingGroup (Fin 7) := Perm.mem_alternatingGroup.mpr pi3_sign

theorem pi3_six : pi3 6 = 6 := by decide +kernel

theorem chk_orbit : (tL.all fun τ => tL.all fun σ =>
    σ == τ || σ == pi3 * τ * pi3⁻¹ || σ == pi3 * pi3 * τ * (pi3 * pi3)⁻¹) = true := by
  decide +kernel

theorem tL_orbit {τ σ : Perm (Fin 7)} (hτ : τ ∈ tL) (hσ : σ ∈ tL) :
    σ = τ ∨ σ = pi3 * τ * pi3⁻¹ ∨ σ = pi3 * pi3 * τ * (pi3 * pi3)⁻¹ := by
  have h := all_true (all_true chk_orbit hτ) hσ
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem chk_pi3_dstd : (dstdL.all fun d => dstdL.contains (pi3 * d * pi3⁻¹) &&
    dstdL.contains (pi3⁻¹ * d * pi3)) = true := by
  decide +kernel

theorem pi3_mem_normalizer_dstd : pi3 ∈ Subgroup.normalizer (dstd : Set (Perm (Fin 7))) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  constructor
  · intro hd
    have h := all_true chk_pi3_dstd hd
    rw [Bool.and_eq_true] at h
    exact List.contains_iff_mem.mp h.1
  · intro hd
    have h := all_true chk_pi3_dstd hd
    rw [Bool.and_eq_true] at h
    have h2 := List.contains_iff_mem.mp h.2
    show d ∈ dstdL
    simpa [mul_assoc] using h2

theorem n1_six : n1 6 = 6 := by decide +kernel

theorem n2_six : n2 6 = 6 := by decide +kernel

theorem n3_six : n3 6 = 6 := by decide +kernel

theorem chk_pairs : ((List.finRange 7).all fun a0 => !((a0 : ℕ) / 2 == 0) ||
    (List.finRange 7).all fun a1 => !((a1 : ℕ) / 2 == 0 && a1 != a0) ||
    (List.finRange 7).all fun a2 => !((a2 : ℕ) / 2 == 1) ||
    (List.finRange 7).all fun a3 => !((a3 : ℕ) / 2 == 1 && a3 != a2) ||
    (List.finRange 7).all fun a4 => !((a4 : ℕ) / 2 == 2) ||
    (List.finRange 7).all fun a5 => !((a5 : ℕ) / 2 == 2 && a5 != a4) ||
    (List.finRange 7).all fun a6 => !((a6 : ℕ) / 2 == 3) ||
    dstdL.any fun d => d 0 == a0 && d 1 == a1 && d 2 == a2 && d 3 == a3 && d 4 == a4 &&
      d 5 == a5 && d 6 == a6) = true := by
  decide +kernel

theorem mem_dstd_of_pairs (ρ : Perm (Fin 7)) (h : ∀ i, ((ρ i : Fin 7) : ℕ) / 2 = (i : ℕ) / 2) :
    ρ ∈ dstd := by
  have hne : ∀ i j, i ≠ j → (ρ j != ρ i) = true := fun i j hij => by
    rw [bne_iff_ne]
    exact fun e => hij (ρ.injective e).symm
  have e : ∀ (i : Fin 7) (k : ℕ), (i : ℕ) / 2 = k → (((ρ i : Fin 7) : ℕ) / 2 == k) = true :=
      fun i k hk => by
    rw [beq_iff_eq, h i, hk]
  have h0 := all_imp chk_pairs (List.mem_finRange (ρ 0)) (e 0 0 rfl)
  have h1 := all_imp h0 (List.mem_finRange (ρ 1))
    (by rw [Bool.and_eq_true]; exact ⟨e 1 0 rfl, hne 0 1 (by decide)⟩)
  have h2 := all_imp h1 (List.mem_finRange (ρ 2)) (e 2 1 rfl)
  have h3 := all_imp h2 (List.mem_finRange (ρ 3))
    (by rw [Bool.and_eq_true]; exact ⟨e 3 1 rfl, hne 2 3 (by decide)⟩)
  have h4 := all_imp h3 (List.mem_finRange (ρ 4)) (e 4 2 rfl)
  have h5 := all_imp h4 (List.mem_finRange (ρ 5))
    (by rw [Bool.and_eq_true]; exact ⟨e 5 2 rfl, hne 4 5 (by decide)⟩)
  have h6 := all_imp h5 (List.mem_finRange (ρ 6)) (e 6 3 rfl)
  obtain ⟨d, hd, hdv⟩ := List.any_eq_true.mp h6
  simp only [Bool.and_eq_true, beq_iff_eq] at hdv
  obtain ⟨⟨⟨⟨⟨⟨v0, v1⟩, v2⟩, v3⟩, v4⟩, v5⟩, v6⟩ := hdv
  have hρ : ρ = d := by
    refine Equiv.ext fun i => ?_
    fin_cases i
    · exact v0.symm
    · exact v1.symm
    · exact v2.symm
    · exact v3.symm
    · exact v4.symm
    · exact v5.symm
    · exact v6.symm
  rw [hρ]
  exact hd

theorem eq_univ_of_closed : ∀ s : Finset (Fin 7), 6 ∈ s → (∃ j ∈ s, j ≠ 6) →
    (∀ x ∈ s, n1 x ∈ s) → (∀ x ∈ s, n2 x ∈ s) → (∀ x ∈ s, n3 x ∈ s) →
    (∀ x ∈ s, pi3 x ∈ s) → s = Finset.univ := by
  decide +kernel

theorem card_alternatingGroup_seven : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
  decide

theorem card_le_eight {H : Subgroup (Perm (Fin 7))} (hH : H ≤ alternatingGroup (Fin 7))
    (h2 : IsPGroup 2 H) : Nat.card H ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h2
  have hdvd : Nat.card H ∣ 2520 := by
    rw [← card_alternatingGroup_seven]
    exact Subgroup.card_dvd_of_le hH
  rw [hk] at hdvd ⊢
  have hk3 : k ≤ 3 := by
    by_contra hk3
    have h16 : 2 ^ 4 ∣ 2520 := dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdvd
    exact absurd h16 (by decide)
  calc 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk3
    _ = 8 := by norm_num

theorem pow_sixteen {R : Subgroup (Perm (Fin 7))} (h2 : IsPGroup 2 R) {g : Perm (Fin 7)}
    (hg : g ∈ R) : g ^ 16 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h2 ⟨g, hg⟩
  rw [Subgroup.orderOf_mk] at hk
  have hdvd : orderOf g ∣ 5040 := by
    have := orderOf_dvd_card (G := Perm (Fin 7)) (x := g)
    rwa [Fintype.card_perm, Fintype.card_fin] at this
  rw [hk] at hdvd
  have hk4 : k ≤ 4 := by
    by_contra hk4
    have h32 : 2 ^ 5 ∣ 5040 := dvd_trans (Nat.pow_dvd_pow 2 (by omega)) hdvd
    exact absurd h32 (by decide)
  rw [← orderOf_dvd_iff_pow_eq_one, hk]
  exact Nat.pow_dvd_pow 2 hk4

end CFSG.Quasithin.H13.A7Blk

end
