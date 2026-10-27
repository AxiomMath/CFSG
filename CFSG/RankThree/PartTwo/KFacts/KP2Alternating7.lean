module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.RankThree.LocalRank.SolvablePrimeComplementCore
public import CFSG.RankThree.PartTwo.KFacts.KP2Alternating7K

public section

namespace CFSG.RankThree.PartTwo.KFacts.KP2

open Equiv Subgroup

abbrev sw (a b : Fin 7) : Perm (Fin 7) := swap a b

@[expose] def cOne : Perm (Fin 7) := sw 0 1 * sw 1 2

@[expose] def cTwo : Perm (Fin 7) := sw 3 4 * sw 4 5

@[expose] def tInv : Perm (Fin 7) := sw 1 2 * sw 4 5

@[expose] def rFour : Perm (Fin 7) := sw 0 3 * sw 1 4 * sw 2 5 * sw 4 5

@[expose] def tauOne : Perm (Fin 7) := sw 0 3 * sw 1 4 * sw 2 5

@[expose] def tauTwo : Perm (Fin 7) := sw 0 3 * sw 1 5 * sw 2 4

@[expose] def vOneF : Fin 4 → Perm (Fin 7) :=
  ![1, sw 3 4 * sw 5 6, sw 3 5 * sw 4 6, sw 3 6 * sw 4 5]

@[expose] def vTwoF : Fin 4 → Perm (Fin 7) :=
  ![1, sw 0 1 * sw 2 6, sw 0 2 * sw 1 6, sw 0 6 * sw 1 2]

@[expose] def eNineF (i j : Fin 3) : Perm (Fin 7) := cOne ^ (i : ℕ) * cTwo ^ (j : ℕ)

@[expose] def symA : Fin 24 → Perm (Fin 7) :=
  ![1,
    sw 5 6,
    sw 4 5,
    sw 4 5 * sw 5 6,
    sw 4 6 * sw 5 6,
    sw 4 6,
    sw 3 4,
    sw 3 4 * sw 5 6,
    sw 3 4 * sw 4 5,
    sw 3 4 * sw 4 5 * sw 5 6,
    sw 3 4 * sw 4 6 * sw 5 6,
    sw 3 4 * sw 4 6,
    sw 3 5 * sw 4 5,
    sw 3 5 * sw 4 5 * sw 5 6,
    sw 3 5,
    sw 3 5 * sw 5 6,
    sw 3 5 * sw 4 6,
    sw 3 5 * sw 4 6 * sw 5 6,
    sw 3 6 * sw 4 6 * sw 5 6,
    sw 3 6 * sw 4 6,
    sw 3 6 * sw 5 6,
    sw 3 6,
    sw 3 6 * sw 4 5 * sw 5 6,
    sw 3 6 * sw 4 5]

@[expose] def symB : Fin 24 → Perm (Fin 7) :=
  ![1,
    sw 2 6,
    sw 1 2,
    sw 1 2 * sw 2 6,
    sw 1 6 * sw 2 6,
    sw 1 6,
    sw 0 1,
    sw 0 1 * sw 2 6,
    sw 0 1 * sw 1 2,
    sw 0 1 * sw 1 2 * sw 2 6,
    sw 0 1 * sw 1 6 * sw 2 6,
    sw 0 1 * sw 1 6,
    sw 0 2 * sw 1 2,
    sw 0 2 * sw 1 2 * sw 2 6,
    sw 0 2,
    sw 0 2 * sw 2 6,
    sw 0 2 * sw 1 6,
    sw 0 2 * sw 1 6 * sw 2 6,
    sw 0 6 * sw 1 6 * sw 2 6,
    sw 0 6 * sw 1 6,
    sw 0 6 * sw 2 6,
    sw 0 6,
    sw 0 6 * sw 1 2 * sw 2 6,
    sw 0 6 * sw 1 2]


theorem eNineF_mul : ∀ i j k l : Fin 3, ∃ m n : Fin 3, eNineF i j * eNineF k l = eNineF m n := by
  decide +kernel

theorem eNineF_inv : ∀ i j : Fin 3, ∃ m n : Fin 3, (eNineF i j)⁻¹ = eNineF m n := by
  decide +kernel

theorem vOneF_mul : ∀ i j : Fin 4, ∃ k : Fin 4, vOneF i * vOneF j = vOneF k := by
  decide +kernel

theorem vOneF_inv : ∀ i : Fin 4, ∃ k : Fin 4, (vOneF i)⁻¹ = vOneF k := by
  decide +kernel

theorem vTwoF_mul : ∀ i j : Fin 4, ∃ k : Fin 4, vTwoF i * vTwoF j = vTwoF k := by
  decide +kernel

theorem vTwoF_inv : ∀ i : Fin 4, ∃ k : Fin 4, (vTwoF i)⁻¹ = vTwoF k := by
  decide +kernel

@[expose] def eNine : Subgroup (Perm (Fin 7)) where
  carrier := {x | ∃ i j, x = eNineF i j}
  mul_mem' := by
    rintro _ _ ⟨i, j, rfl⟩ ⟨k, l, rfl⟩
    exact eNineF_mul i j k l
  one_mem' := ⟨0, 0, by decide +kernel⟩
  inv_mem' := by
    rintro _ ⟨i, j, rfl⟩
    exact eNineF_inv i j

@[expose] def vOne : Subgroup (Perm (Fin 7)) where
  carrier := {x | ∃ i, x = vOneF i}
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact vOneF_mul i j
  one_mem' := ⟨0, by decide +kernel⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact vOneF_inv i

@[expose] def vTwo : Subgroup (Perm (Fin 7)) where
  carrier := {x | ∃ i, x = vTwoF i}
  mul_mem' := by
    rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
    exact vTwoF_mul i j
  one_mem' := ⟨0, by decide +kernel⟩
  inv_mem' := by
    rintro _ ⟨i, rfl⟩
    exact vTwoF_inv i

theorem mem_eNine {x : Perm (Fin 7)} : x ∈ eNine ↔ ∃ i j, x = eNineF i j := Iff.rfl

theorem mem_vOne {x : Perm (Fin 7)} : x ∈ vOne ↔ ∃ i, x = vOneF i := Iff.rfl

theorem mem_vTwo {x : Perm (Fin 7)} : x ∈ vTwo ↔ ∃ i, x = vTwoF i := Iff.rfl

theorem cOne_mem_eNine : cOne ∈ eNine := ⟨1, 0, by decide +kernel⟩

theorem cTwo_mem_eNine : cTwo ∈ eNine := ⟨0, 1, by decide +kernel⟩

theorem forall_not_of_card_filter_eq_zero {P : Perm (Fin 7) → Prop} [DecidablePred P]
    (h : (Finset.univ.filter P).card = 0) (x : Perm (Fin 7)) : ¬ P x :=
  Finset.filter_eq_empty_iff.1 (Finset.card_eq_zero.1 h) (Finset.mem_univ x)

theorem card_filter_centralizer_cOne : (Finset.univ.filter (fun x : Perm (Fin 7) =>
    x * cOne = cOne * x ∧ ¬ ∃ i : Fin 3, ∃ k : Fin 24, x = cOne ^ (i : ℕ) * symA k)).card = 0 := by
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ ⟨hc, hn⟩ => hn ?_)
  obtain ⟨t, -, ht⟩ := KP2K.cent_of (fun p : Fin 3 × Fin 24 => cOne ^ (p.1 : ℕ) * symA p.2)
    KP2K.TA (g₂ := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) KP2K.walkA x hc
    (by rw [one_mul, mul_one])
  exact ⟨t.1.1, t.1.2, ht⟩

theorem card_filter_centralizer_cTwo : (Finset.univ.filter (fun x : Perm (Fin 7) =>
    x * cTwo = cTwo * x ∧ ¬ ∃ i : Fin 3, ∃ k : Fin 24, x = cTwo ^ (i : ℕ) * symB k)).card = 0 := by
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ ⟨hc, hn⟩ => hn ?_)
  obtain ⟨t, -, ht⟩ := KP2K.cent_of (fun p : Fin 3 × Fin 24 => cTwo ^ (p.1 : ℕ) * symB p.2)
    KP2K.TB (g₂ := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) KP2K.walkB x hc
    (by rw [one_mul, mul_one])
  exact ⟨t.1.1, t.1.2, ht⟩

theorem card_filter_centralizer_cOne_cTwo : (Finset.univ.filter (fun x : Perm (Fin 7) =>
    x * (cOne * cTwo) = cOne * cTwo * x ∧
      ¬ ∃ i j : Fin 3, ∃ b : Bool, x = eNineF i j * (if b then tauOne else 1))).card = 0 := by
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ ⟨hc, hn⟩ => hn ?_)
  obtain ⟨t, -, ht⟩ := KP2K.cent_of
    (fun p : Fin 3 × Fin 3 × Bool => eNineF p.1 p.2.1 * (if p.2.2 then tauOne else 1))
    KP2K.T1 (g₂ := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) KP2K.walk1 x hc
    (by rw [one_mul, mul_one])
  exact ⟨t.1.1, t.1.2.1, t.1.2.2, ht⟩

theorem card_filter_centralizer_cOne_cTwo_sq : (Finset.univ.filter (fun x : Perm (Fin 7) =>
    x * (cOne * cTwo ^ 2) = cOne * cTwo ^ 2 * x ∧
      ¬ ∃ i j : Fin 3, ∃ b : Bool, x = eNineF i j * (if b then tauTwo else 1))).card = 0 := by
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ ⟨hc, hn⟩ => hn ?_)
  obtain ⟨t, -, ht⟩ := KP2K.cent_of
    (fun p : Fin 3 × Fin 3 × Bool => eNineF p.1 p.2.1 * (if p.2.2 then tauTwo else 1))
    KP2K.T2 (g₂ := 1) (by decide +kernel) (by decide +kernel) (by decide +kernel) KP2K.walk2 x hc
    (by rw [one_mul, mul_one])
  exact ⟨t.1.1, t.1.2.1, t.1.2.2, ht⟩

theorem card_filter_centralizer_eNine : (Finset.univ.filter (fun x : Perm (Fin 7) =>
    x * cOne = cOne * x ∧ x * cTwo = cTwo * x ∧ ¬ ∃ i j : Fin 3, x = eNineF i j)).card = 0 := by
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun x _ ⟨hc₁, hc₂, hn⟩ => hn ?_)
  obtain ⟨t, -, ht⟩ := KP2K.cent_of (fun p : Fin 3 × Fin 3 => eNineF p.1 p.2) KP2K.T9
    (by decide +kernel) (by decide +kernel) (by decide +kernel) KP2K.walk9 x hc₁ hc₂
  exact ⟨t.1.1, t.1.2, ht⟩

theorem check_cOne : ∀ (i : Fin 3) (k : Fin 24), (cOne ^ (i : ℕ) * symA k) ^ 12 = 1 ∧
    ((cOne ^ (i : ℕ) * symA k) ^ 4 = 1 → (∃ m, cOne ^ (i : ℕ) * symA k = vOneF m) ∨
      ((cOne ^ (i : ℕ) * symA k * (cTwo * (cOne ^ (i : ℕ) * symA k) * cTwo⁻¹)) ^ 3 = 1 ∧
        cOne ^ (i : ℕ) * symA k * (cTwo * (cOne ^ (i : ℕ) * symA k) * cTwo⁻¹) ≠ 1)) := by
  decide +kernel

theorem check_cTwo : ∀ (i : Fin 3) (k : Fin 24), (cTwo ^ (i : ℕ) * symB k) ^ 12 = 1 ∧
    ((cTwo ^ (i : ℕ) * symB k) ^ 4 = 1 → (∃ m, cTwo ^ (i : ℕ) * symB k = vTwoF m) ∨
      ((cTwo ^ (i : ℕ) * symB k * (cOne * (cTwo ^ (i : ℕ) * symB k) * cOne⁻¹)) ^ 3 = 1 ∧
        cTwo ^ (i : ℕ) * symB k * (cOne * (cTwo ^ (i : ℕ) * symB k) * cOne⁻¹) ≠ 1)) := by
  decide +kernel

theorem check_tauOne : ∀ (i j : Fin 3) (b : Bool),
    (eNineF i j * (if b then tauOne else 1)) ^ 6 = 1 ∧
    ((eNineF i j * (if b then tauOne else 1)) ^ 2 = 1 →
      eNineF i j * (if b then tauOne else 1) = 1 ∨
      ((eNineF i j * (if b then tauOne else 1) *
          (cOne * (eNineF i j * (if b then tauOne else 1)) * cOne⁻¹)) ^ 3 = 1 ∧
        eNineF i j * (if b then tauOne else 1) *
          (cOne * (eNineF i j * (if b then tauOne else 1)) * cOne⁻¹) ≠ 1)) := by
  decide +kernel

theorem check_tauTwo : ∀ (i j : Fin 3) (b : Bool),
    (eNineF i j * (if b then tauTwo else 1)) ^ 6 = 1 ∧
    ((eNineF i j * (if b then tauTwo else 1)) ^ 2 = 1 →
      eNineF i j * (if b then tauTwo else 1) = 1 ∨
      ((eNineF i j * (if b then tauTwo else 1) *
          (cOne * (eNineF i j * (if b then tauTwo else 1)) * cOne⁻¹)) ^ 3 = 1 ∧
        eNineF i j * (if b then tauTwo else 1) *
          (cOne * (eNineF i j * (if b then tauTwo else 1)) * cOne⁻¹) ≠ 1)) := by
  decide +kernel

theorem check_vOne_vTwo : ∀ m n : Fin 4, m ≠ 0 → n ≠ 0 → (vOneF m * vTwoF n) ^ 6 = 1 ∧
    (vOneF m * vTwoF n) ^ 2 ≠ 1 := by
  decide +kernel


theorem eNineF_comm : ∀ i j k l : Fin 3, eNineF i j * eNineF k l = eNineF k l * eNineF i j := by
  decide +kernel

theorem eNineF_pow_three : ∀ i j : Fin 3, eNineF i j ^ 3 = 1 := by
  decide +kernel

theorem eNineF_injective : ∀ p q : Fin 3 × Fin 3, eNineF p.1 p.2 = eNineF q.1 q.2 → p = q := by
  decide +kernel

theorem card_eNine : Nat.card eNine = 9 := by
  have : (eNine : Set (Perm (Fin 7))) = Set.range (fun p : Fin 3 × Fin 3 => eNineF p.1 p.2) := by
    ext x
    exact ⟨fun ⟨i, j, h⟩ => ⟨(i, j), h.symm⟩, fun ⟨p, h⟩ => ⟨p.1, p.2, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, this,
    Nat.card_range_of_injective (fun p q h => eNineF_injective p q h)]
  simp

theorem eNineF_cases : ∀ i j : Fin 3, (i, j) ≠ (0, 0) →
    (eNineF i j = cOne ∨ eNineF i j ^ 2 = cOne) ∨ (eNineF i j = cTwo ∨ eNineF i j ^ 2 = cTwo) ∨
    (eNineF i j = cOne * cTwo ∨ eNineF i j ^ 2 = cOne * cTwo) ∨
    (eNineF i j = cOne * cTwo ^ 2 ∨ eNineF i j ^ 2 = cOne * cTwo ^ 2) := by
  decide +kernel

variable {Q : Subgroup (Perm (Fin 7))}

theorem three_dvd_orderOf_of_pow {G : Type*} [Group G] {x : G} {m : ℕ} (h1 : x ^ (3 * m) = 1)
    (h2 : x ^ m ≠ 1) : 3 ∣ orderOf x := by
  by_contra h
  apply h2
  rw [← orderOf_dvd_iff_pow_eq_one] at h1 ⊢
  exact ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h).symm.dvd_of_dvd_mul_left h1

theorem not_three_dvd_orderOf_of_mem (h3 : ¬ 3 ∣ Nat.card Q) {x : Perm (Fin 7)} (hx : x ∈ Q) :
    ¬ 3 ∣ orderOf x :=
  fun h => h3 (h.trans (Subgroup.orderOf_dvd_natCard Q hx))

theorem pow_eq_one_of_mem {m : ℕ} (h3 : ¬ 3 ∣ Nat.card Q) {x : Perm (Fin 7)} (hx : x ∈ Q)
    (h : x ^ (3 * m) = 1) : x ^ m = 1 := by
  by_contra hne
  exact not_three_dvd_orderOf_of_mem h3 hx (three_dvd_orderOf_of_pow h hne)

theorem conj_mem {g : Perm (Fin 7)}
    (h : g ∈ normalizer (Q : Set (Perm (Fin 7)))) {x : Perm (Fin 7)} (hx : x ∈ Q) :
    g * x * g⁻¹ ∈ Q :=
  (mem_normalizer_iff.1 h x).1 hx

theorem mem_vOne_of_commute (h3 : ¬ 3 ∣ Nat.card Q)
    (h2 : cTwo ∈ normalizer (Q : Set (Perm (Fin 7)))) {x : Perm (Fin 7)} (hx : x ∈ Q)
    (hc : x * cOne = cOne * x) : x ∈ vOne := by
  obtain ⟨i, k, rfl⟩ : ∃ i : Fin 3, ∃ k : Fin 24, x = cOne ^ (i : ℕ) * symA k := by
    by_contra hne
    exact forall_not_of_card_filter_eq_zero card_filter_centralizer_cOne x ⟨hc, hne⟩
  obtain ⟨h12, h4⟩ := check_cOne i k
  rcases h4 (pow_eq_one_of_mem h3 hx (by simpa using h12)) with ⟨m, hm⟩ | ⟨hy3, hy1⟩
  · exact ⟨m, hm⟩
  · exfalso
    have h1 := pow_eq_one_of_mem (m := 1) h3 (Q.mul_mem hx (conj_mem h2 hx)) (by simpa using hy3)
    exact hy1 (by simpa using h1)


theorem mem_vTwo_of_commute (h3 : ¬ 3 ∣ Nat.card Q)
    (h1 : cOne ∈ normalizer (Q : Set (Perm (Fin 7)))) {x : Perm (Fin 7)} (hx : x ∈ Q)
    (hc : x * cTwo = cTwo * x) : x ∈ vTwo := by
  obtain ⟨i, k, rfl⟩ : ∃ i : Fin 3, ∃ k : Fin 24, x = cTwo ^ (i : ℕ) * symB k := by
    by_contra hne
    exact forall_not_of_card_filter_eq_zero card_filter_centralizer_cTwo x ⟨hc, hne⟩
  obtain ⟨h12, h4⟩ := check_cTwo i k
  rcases h4 (pow_eq_one_of_mem h3 hx (by simpa using h12)) with ⟨m, hm⟩ | ⟨hy3, hy1⟩
  · exact ⟨m, hm⟩
  · exfalso
    have h1' := pow_eq_one_of_mem (m := 1) h3 (Q.mul_mem hx (conj_mem h1 hx)) (by simpa using hy3)
    exact hy1 (by simpa using h1')

theorem eq_one_of_commute_cOne_cTwo (h3 : ¬ 3 ∣ Nat.card Q)
    (h1 : cOne ∈ normalizer (Q : Set (Perm (Fin 7)))) {x : Perm (Fin 7)} (hx : x ∈ Q)
    (hc : x * (cOne * cTwo) = cOne * cTwo * x) : x = 1 := by
  obtain ⟨i, j, b, rfl⟩ :
      ∃ i j : Fin 3, ∃ b : Bool, x = eNineF i j * (if b then tauOne else 1) := by
    by_contra hne
    exact forall_not_of_card_filter_eq_zero card_filter_centralizer_cOne_cTwo x ⟨hc, hne⟩
  obtain ⟨h6, h2⟩ := check_tauOne i j b
  rcases h2 (pow_eq_one_of_mem h3 hx (by simpa using h6)) with h | ⟨hy3, hy1⟩
  · exact h
  · exfalso
    have h1' := pow_eq_one_of_mem (m := 1) h3 (Q.mul_mem hx (conj_mem h1 hx)) (by simpa using hy3)
    exact hy1 (by simpa using h1')

theorem eq_one_of_commute_cOne_cTwo_sq (h3 : ¬ 3 ∣ Nat.card Q)
    (h1 : cOne ∈ normalizer (Q : Set (Perm (Fin 7)))) {x : Perm (Fin 7)} (hx : x ∈ Q)
    (hc : x * (cOne * cTwo ^ 2) = cOne * cTwo ^ 2 * x) : x = 1 := by
  obtain ⟨i, j, b, rfl⟩ :
      ∃ i j : Fin 3, ∃ b : Bool, x = eNineF i j * (if b then tauTwo else 1) := by
    by_contra hne
    exact forall_not_of_card_filter_eq_zero card_filter_centralizer_cOne_cTwo_sq x ⟨hc, hne⟩
  obtain ⟨h6, h2⟩ := check_tauTwo i j b
  rcases h2 (pow_eq_one_of_mem h3 hx (by simpa using h6)) with h | ⟨hy3, hy1⟩
  · exact h
  · exfalso
    have h1' := pow_eq_one_of_mem (m := 1) h3 (Q.mul_mem hx (conj_mem h1 hx)) (by simpa using hy3)
    exact hy1 (by simpa using h1')

theorem eq_one_or_eq_one_of_mem_vOne_vTwo (h3 : ¬ 3 ∣ Nat.card Q) {x z : Perm (Fin 7)}
    (hxQ : x ∈ Q) (hzQ : z ∈ Q) (hx : x ∈ vOne) (hz : z ∈ vTwo) : x = 1 ∨ z = 1 := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, rfl⟩ := hz
  by_cases hm : m = 0
  · exact Or.inl (by rw [hm]; rfl)
  by_cases hn : n = 0
  · exact Or.inr (by rw [hn]; rfl)
  exfalso
  obtain ⟨h6, h2⟩ := check_vOne_vTwo m n hm hn
  exact h2 (pow_eq_one_of_mem (m := 2) h3 (Q.mul_mem hxQ hzQ) (by simpa using h6))

theorem mem_vOne_or_mem_vTwo_of_commute (h3 : ¬ 3 ∣ Nat.card Q)
    (h1 : cOne ∈ normalizer (Q : Set (Perm (Fin 7))))
    (h2 : cTwo ∈ normalizer (Q : Set (Perm (Fin 7)))) {x : Perm (Fin 7)} (hx : x ∈ Q) {i j : Fin 3}
    (hij : (i, j) ≠ (0, 0)) (hc : x * eNineF i j = eNineF i j * x) : x ∈ vOne ∨ x ∈ vTwo := by
  have hc1 : Commute x (eNineF i j) := hc
  have hc2 : Commute x (eNineF i j ^ 2) := hc1.pow_right 2
  rcases eNineF_cases i j hij with (h | h) | (h | h) | (h | h) | (h | h)
  · exact Or.inl (mem_vOne_of_commute h3 h2 hx (h ▸ hc1).eq)
  · exact Or.inl (mem_vOne_of_commute h3 h2 hx (h ▸ hc2).eq)
  · exact Or.inr (mem_vTwo_of_commute h3 h1 hx (h ▸ hc1).eq)
  · exact Or.inr (mem_vTwo_of_commute h3 h1 hx (h ▸ hc2).eq)
  · exact Or.inl ((eq_one_of_commute_cOne_cTwo h3 h1 hx (h ▸ hc1).eq) ▸ vOne.one_mem)
  · exact Or.inl ((eq_one_of_commute_cOne_cTwo h3 h1 hx (h ▸ hc2).eq) ▸ vOne.one_mem)
  · exact Or.inl ((eq_one_of_commute_cOne_cTwo_sq h3 h1 hx (h ▸ hc1).eq) ▸ vOne.one_mem)
  · exact Or.inl ((eq_one_of_commute_cOne_cTwo_sq h3 h1 hx (h ▸ hc2).eq) ▸ vOne.one_mem)

instance : CFSG.IsElementaryAbelian 3 eNine where
  is_comm := ⟨fun ⟨x, hx⟩ ⟨y, hy⟩ => by
    obtain ⟨i, j, rfl⟩ := hx
    obtain ⟨k, l, rfl⟩ := hy
    exact Subtype.ext (eNineF_comm i j k l)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨x, hx⟩ => by
    obtain ⟨i, j, rfl⟩ := hx
    exact Subtype.ext (eNineF_pow_three i j)

theorem le_vOne_or_le_vTwo (h3 : ¬ 3 ∣ Nat.card Q)
    (h1 : cOne ∈ normalizer (Q : Set (Perm (Fin 7))))
    (h2 : cTwo ∈ normalizer (Q : Set (Perm (Fin 7)))) : Q ≤ vOne ∨ Q ≤ vTwo := by
  classical
  have hE : eNine ≤ normalizer (Q : Set (Perm (Fin 7))) := by
    rintro _ ⟨i, j, rfl⟩
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ h1 _) (Subgroup.pow_mem _ h2 _)
  let φ : eNine →* MulAut Q := Q.normalizerMonoidHom.comp (Subgroup.inclusion hE)
  let _ : MulDistribMulAction eNine Q := MulDistribMulAction.compHom Q φ
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgen := CFSG.SolvableHall.coprime_centralizer_generation (A := eNine) (H := Q) (p := 3)
    (by rw [card_eNine]; norm_num) h3
  have hfix : ∀ (a : eNine) (x : Q), x ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) Q →
      (x : Perm (Fin 7)) * a = a * x := by
    intro a x hx
    rw [CFSG.SolvableHall.mem_fixedPointSubgroup_zpowers_iff] at hx
    have h := congrArg Subtype.val hx
    change (a : Perm (Fin 7)) * x * (a : Perm (Fin 7))⁻¹ = x at h
    nth_rewrite 1 [← h]
    group
  have hcases : ∀ (a : eNine), a ≠ 1 → ∀ x : Q,
      x ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) Q → (x : Perm (Fin 7)) ∈ vOne ∨
        (x : Perm (Fin 7)) ∈ vTwo := by
    rintro ⟨_, i, j, rfl⟩ ha x hx
    have hij : (i, j) ≠ (0, 0) := by
      rintro h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h
      exact ha (Subtype.ext (by decide +kernel))
    exact mem_vOne_or_mem_vTwo_of_commute h3 h1 h2 x.2 hij (hfix _ x hx)
  have hle : ∀ W : Subgroup (Perm (Fin 7)), (∀ (a : eNine), a ≠ 1 → ∀ x : Q,
      x ∈ CFSG.fixedPointSubgroup (Subgroup.zpowers a) Q → (x : Perm (Fin 7)) ∈ W) → Q ≤ W := by
    intro W hW y hy
    have htop : (⊤ : Subgroup Q) ≤ W.comap Q.subtype := by
      rw [← hgen]
      exact iSup₂_le fun a ha x hx => hW a ha x hx
    exact htop (Subgroup.mem_top ⟨y, hy⟩)
  by_cases hV : ∃ z ∈ Q, z ∈ vTwo ∧ z ≠ 1
  · obtain ⟨z, hzQ, hz, hz1⟩ := hV
    refine Or.inr (hle vTwo fun a ha x hx => ?_)
    rcases hcases a ha x hx with hx1 | hx2
    · rcases eq_one_or_eq_one_of_mem_vOne_vTwo h3 x.2 hzQ hx1 hz with h | h
      · exact h ▸ vTwo.one_mem
      · exact absurd h hz1
    · exact hx2
  · refine Or.inl (hle vOne fun a ha x hx => ?_)
    rcases hcases a ha x hx with hx1 | hx2
    · exact hx1
    · by_cases h : (x : Perm (Fin 7)) = 1
      · exact h ▸ vOne.one_mem
      · exact absurd ⟨x, x.2, hx2, h⟩ hV


@[expose] def centOne : Subgroup (Perm (Fin 7)) :=
  centralizer {cOne} ⊓ alternatingGroup (Fin 7)

@[expose] def centTwo : Subgroup (Perm (Fin 7)) :=
  centralizer {cTwo} ⊓ alternatingGroup (Fin 7)

theorem vOneF_spec : ∀ m : Fin 4, vOneF m * cOne = cOne * vOneF m ∧ Perm.sign (vOneF m) = 1 := by
  decide +kernel

theorem vTwoF_spec : ∀ m : Fin 4, vTwoF m * cTwo = cTwo * vTwoF m ∧ Perm.sign (vTwoF m) = 1 := by
  decide +kernel

theorem eNineF_sign : ∀ i j : Fin 3, Perm.sign (eNineF i j) = 1 := by
  decide +kernel

theorem eNine_le_alternatingGroup : eNine ≤ alternatingGroup (Fin 7) := by
  rintro _ ⟨i, j, rfl⟩
  exact eNineF_sign i j

theorem vOne_le_centOne : vOne ≤ centOne := by
  rintro _ ⟨m, rfl⟩
  refine ⟨mem_centralizer_singleton_iff.2 (vOneF_spec m).1, (vOneF_spec m).2⟩

theorem vTwo_le_centTwo : vTwo ≤ centTwo := by
  rintro _ ⟨m, rfl⟩
  refine ⟨mem_centralizer_singleton_iff.2 (vTwoF_spec m).1, (vTwoF_spec m).2⟩

theorem cOne_mem_centOne : cOne ∈ centOne :=
  ⟨mem_centralizer_singleton_iff.2 rfl, eNine_le_alternatingGroup cOne_mem_eNine⟩

theorem cTwo_mem_centOne : cTwo ∈ centOne :=
  ⟨mem_centralizer_singleton_iff.2 (by decide +kernel), eNine_le_alternatingGroup cTwo_mem_eNine⟩

theorem cOne_mem_centTwo : cOne ∈ centTwo :=
  ⟨mem_centralizer_singleton_iff.2 (by decide +kernel), eNine_le_alternatingGroup cOne_mem_eNine⟩

theorem cTwo_mem_centTwo : cTwo ∈ centTwo :=
  ⟨mem_centralizer_singleton_iff.2 rfl, eNine_le_alternatingGroup cTwo_mem_eNine⟩

theorem vTwoF_not_commute : ∀ m : Fin 4, m ≠ 0 → vTwoF m * cOne ≠ cOne * vTwoF m := by
  decide +kernel

theorem vOneF_not_commute : ∀ m : Fin 4, m ≠ 0 → vOneF m * cTwo ≠ cTwo * vOneF m := by
  decide +kernel

theorem vOne_conj : ∀ (i : Fin 3) (k : Fin 24) (m : Fin 4), ∃ m' : Fin 4,
    cOne ^ (i : ℕ) * symA k * vOneF m * (cOne ^ (i : ℕ) * symA k)⁻¹ = vOneF m' := by
  decide +kernel

theorem vTwo_conj : ∀ (i : Fin 3) (k : Fin 24) (m : Fin 4), ∃ m' : Fin 4,
    cTwo ^ (i : ℕ) * symB k * vTwoF m * (cTwo ^ (i : ℕ) * symB k)⁻¹ = vTwoF m' := by
  decide +kernel


theorem vOneF_injective : ∀ m n : Fin 4, vOneF m = vOneF n → m = n := by
  decide +kernel

theorem vTwoF_injective : ∀ m n : Fin 4, vTwoF m = vTwoF n → m = n := by
  decide +kernel

theorem card_vOne : Nat.card vOne = 4 := by
  have : (vOne : Set (Perm (Fin 7))) = Set.range vOneF := by
    ext x
    exact ⟨fun ⟨m, h⟩ => ⟨m, h.symm⟩, fun ⟨m, h⟩ => ⟨m, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, this,
    Nat.card_range_of_injective (fun m n h => vOneF_injective m n h)]
  simp

theorem card_vTwo : Nat.card vTwo = 4 := by
  have : (vTwo : Set (Perm (Fin 7))) = Set.range vTwoF := by
    ext x
    exact ⟨fun ⟨m, h⟩ => ⟨m, h.symm⟩, fun ⟨m, h⟩ => ⟨m, h.symm⟩⟩
  rw [← SetLike.coe_sort_coe, this,
    Nat.card_range_of_injective (fun m n h => vTwoF_injective m n h)]
  simp

theorem vOneF_comm : ∀ m n : Fin 4, vOneF m * vOneF n = vOneF n * vOneF m := by
  decide +kernel

theorem vTwoF_comm : ∀ m n : Fin 4, vTwoF m * vTwoF n = vTwoF n * vTwoF m := by
  decide +kernel

theorem mem_normalizer_map {X : Subgroup (Perm (Fin 7))} (N : Subgroup X) [N.Normal]
    {g : Perm (Fin 7)} (hg : g ∈ X) :
    g ∈ normalizer ((N.map X.subtype : Subgroup (Perm (Fin 7))) : Set (Perm (Fin 7))) :=
  le_normalizer_map X.subtype ⟨⟨g, hg⟩, by rw [normalizer_eq_top_iff.2 inferInstance]; trivial, rfl⟩

theorem map_le_vOne_of_normal (N : Subgroup centOne) [N.Normal] (h3 : ¬ 3 ∣ Nat.card N) :
    N.map centOne.subtype ≤ vOne := by
  have hT : ¬ 3 ∣ Nat.card (N.map centOne.subtype) := by
    rwa [Subgroup.card_map_of_injective centOne.subtype_injective]
  rcases le_vOne_or_le_vTwo hT (mem_normalizer_map N cOne_mem_centOne)
      (mem_normalizer_map N cTwo_mem_centOne) with h | h
  · exact h
  · intro x hx
    obtain ⟨⟨y, hy⟩, hyN, rfl⟩ := hx
    obtain ⟨m, hm⟩ := h ⟨⟨y, hy⟩, hyN, rfl⟩
    change y = vTwoF m at hm
    show y ∈ vOne
    by_cases hm0 : m = 0
    · rw [hm, hm0]
      exact vOne.one_mem
    · exact absurd (hm ▸ mem_centralizer_singleton_iff.1 hy.1) (vTwoF_not_commute m hm0)

instance vOne_normal : (vOne.subgroupOf centOne).Normal where
  conj_mem := by
    rintro ⟨v, hv⟩ hvV ⟨g, hg⟩
    obtain ⟨m, rfl⟩ : ∃ m, v = vOneF m := hvV
    obtain ⟨i, k, rfl⟩ : ∃ i : Fin 3, ∃ k : Fin 24, g = cOne ^ (i : ℕ) * symA k := by
      by_contra hne
      exact forall_not_of_card_filter_eq_zero card_filter_centralizer_cOne g
        ⟨mem_centralizer_singleton_iff.1 hg.1, hne⟩
    exact vOne_conj i k m

theorem theta_centOne :
    (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 centOne).map centOne.subtype = vOne := by
  obtain ⟨-, hchar, h3, hmax, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := centOne)
      Nat.prime_three
  apply le_antisymm
  · have := hchar
    exact map_le_vOne_of_normal _ h3
  · have hs : Group.IsSolvable (vOne.subgroupOf centOne) := Group.isSolvable_of_comm fun x y => by
      obtain ⟨m, hm⟩ : ∃ m, ((x : centOne) : Perm (Fin 7)) = vOneF m := x.2
      obtain ⟨n, hn⟩ : ∃ n, ((y : centOne) : Perm (Fin 7)) = vOneF n := y.2
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hm, hn]
      exact vOneF_comm m n
    have hc : ¬ 3 ∣ Nat.card (vOne.subgroupOf centOne) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe vOne_le_centOne).toEquiv, card_vOne]
      norm_num
    have hle := hmax _ inferInstance hs hc
    intro x hx
    exact ⟨⟨x, vOne_le_centOne hx⟩, hle hx, rfl⟩


theorem map_le_vTwo_of_normal (N : Subgroup centTwo) [N.Normal] (h3 : ¬ 3 ∣ Nat.card N) :
    N.map centTwo.subtype ≤ vTwo := by
  have hT : ¬ 3 ∣ Nat.card (N.map centTwo.subtype) := by
    rwa [Subgroup.card_map_of_injective centTwo.subtype_injective]
  rcases le_vOne_or_le_vTwo hT (mem_normalizer_map N cOne_mem_centTwo)
      (mem_normalizer_map N cTwo_mem_centTwo) with h | h
  · intro x hx
    obtain ⟨⟨y, hy⟩, hyN, rfl⟩ := hx
    obtain ⟨m, hm⟩ := h ⟨⟨y, hy⟩, hyN, rfl⟩
    change y = vOneF m at hm
    show y ∈ vTwo
    by_cases hm0 : m = 0
    · rw [hm, hm0]
      exact vTwo.one_mem
    · exact absurd (hm ▸ mem_centralizer_singleton_iff.1 hy.1) (vOneF_not_commute m hm0)
  · exact h

instance vTwo_normal : (vTwo.subgroupOf centTwo).Normal where
  conj_mem := by
    rintro ⟨v, hv⟩ hvV ⟨g, hg⟩
    obtain ⟨m, rfl⟩ : ∃ m, v = vTwoF m := hvV
    obtain ⟨i, k, rfl⟩ : ∃ i : Fin 3, ∃ k : Fin 24, g = cTwo ^ (i : ℕ) * symB k := by
      by_contra hne
      exact forall_not_of_card_filter_eq_zero card_filter_centralizer_cTwo g
        ⟨mem_centralizer_singleton_iff.1 hg.1, hne⟩
    exact vTwo_conj i k m

theorem theta_centTwo :
    (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 centTwo).map centTwo.subtype = vTwo := by
  obtain ⟨-, hchar, h3, hmax, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := centTwo)
      Nat.prime_three
  apply le_antisymm
  · have := hchar
    exact map_le_vTwo_of_normal _ h3
  · have hs : Group.IsSolvable (vTwo.subgroupOf centTwo) := Group.isSolvable_of_comm fun x y => by
      obtain ⟨m, hm⟩ : ∃ m, ((x : centTwo) : Perm (Fin 7)) = vTwoF m := x.2
      obtain ⟨n, hn⟩ : ∃ n, ((y : centTwo) : Perm (Fin 7)) = vTwoF n := y.2
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, hm, hn]
      exact vTwoF_comm m n
    have hc : ¬ 3 ∣ Nat.card (vTwo.subgroupOf centTwo) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe vTwo_le_centTwo).toEquiv, card_vTwo]
      norm_num
    have hle := hmax _ inferInstance hs hc
    intro x hx
    exact ⟨⟨x, vTwo_le_centTwo hx⟩, hle hx, rfl⟩

theorem vOneF_sq : ∀ m : Fin 4, vOneF m ^ 2 = 1 := by
  decide +kernel

theorem vTwoF_sq : ∀ m : Fin 4, vTwoF m ^ 2 = 1 := by
  decide +kernel

theorem pCore_two_centOne : (CFSG.pCore 2 centOne).map centOne.subtype = vOne := by
  apply le_antisymm
  · have : (CFSG.pCore 2 centOne).Normal := CFSG.pCore_normal
    refine map_le_vOne_of_normal _ fun h => ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := centOne))
    rw [hk] at h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  · have hle : vOne.subgroupOf centOne ≤ CFSG.pCore 2 centOne := le_sSup ⟨inferInstance, by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe vOne_le_centOne).toEquiv, card_vOne]
      norm_num⟩
    intro x hx
    exact ⟨⟨x, vOne_le_centOne hx⟩, hle hx, rfl⟩

theorem pCore_two_centTwo : (CFSG.pCore 2 centTwo).map centTwo.subtype = vTwo := by
  apply le_antisymm
  · have : (CFSG.pCore 2 centTwo).Normal := CFSG.pCore_normal
    refine map_le_vTwo_of_normal _ fun h => ?_
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := centTwo))
    rw [hk] at h
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h) (by norm_num)
  · have hle : vTwo.subgroupOf centTwo ≤ CFSG.pCore 2 centTwo := le_sSup ⟨inferInstance, by
      refine IsPGroup.of_card (n := 2) ?_
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe vTwo_le_centTwo).toEquiv, card_vTwo]
      norm_num⟩
    intro x hx
    exact ⟨⟨x, vTwo_le_centTwo hx⟩, hle hx, rfl⟩

theorem eNineF_commute_vOne : ∀ i j : Fin 3,
    (∀ m : Fin 4, eNineF i j * vOneF m = vOneF m * eNineF i j) ↔ j = 0 := by
  decide +kernel

theorem eNineF_commute_vTwo : ∀ i j : Fin 3,
    (∀ m : Fin 4, eNineF i j * vTwoF m = vTwoF m * eNineF i j) ↔ i = 0 := by
  decide +kernel

theorem commute_vOne_iff {x : Perm (Fin 7)} (hx : x ∈ eNine) :
    (∀ v ∈ vOne, x * v = v * x) ↔ ∃ i : Fin 3, x = cOne ^ (i : ℕ) := by
  obtain ⟨i, j, rfl⟩ := hx
  constructor
  · intro h
    have hj := (eNineF_commute_vOne i j).1 fun m => h _ ⟨m, rfl⟩
    exact ⟨i, by rw [hj]; simp [eNineF]⟩
  · rintro ⟨k, hk⟩ _ ⟨m, rfl⟩
    have hj : j = 0 := by
      have := eNineF_injective (i, j) (k, 0) (by rw [hk]; simp [eNineF])
      exact (Prod.mk.inj this).2
    exact (eNineF_commute_vOne i j).2 hj m

theorem commute_vTwo_iff {x : Perm (Fin 7)} (hx : x ∈ eNine) :
    (∀ v ∈ vTwo, x * v = v * x) ↔ ∃ j : Fin 3, x = cTwo ^ (j : ℕ) := by
  obtain ⟨i, j, rfl⟩ := hx
  constructor
  · intro h
    have hi := (eNineF_commute_vTwo i j).1 fun m => h _ ⟨m, rfl⟩
    exact ⟨j, by rw [hi]; simp [eNineF]⟩
  · rintro ⟨k, hk⟩ _ ⟨m, rfl⟩
    have hi : i = 0 := by
      have := eNineF_injective (i, j) (0, k) (by rw [hk]; simp [eNineF])
      exact (Prod.mk.inj this).1
    exact (eNineF_commute_vTwo i j).2 hi m

theorem tInv_spec : Perm.sign tInv = 1 ∧
    (∀ i j : Fin 3, tInv * eNineF i j * tInv⁻¹ = (eNineF i j)⁻¹) ∧
    (∀ m : Fin 4, ∃ n : Fin 4, tInv * vOneF m * tInv⁻¹ = vOneF n) ∧
    (∀ m : Fin 4, ∃ n : Fin 4, tInv * vTwoF m * tInv⁻¹ = vTwoF n) := by
  decide +kernel

theorem tInv_mem_alternatingGroup : tInv ∈ alternatingGroup (Fin 7) := tInv_spec.1

theorem tInv_conj_eq_inv {x : Perm (Fin 7)} (hx : x ∈ eNine) : tInv * x * tInv⁻¹ = x⁻¹ := by
  obtain ⟨i, j, rfl⟩ := hx
  exact tInv_spec.2.1 i j

theorem tInv_conj_mem_vOne {x : Perm (Fin 7)} (hx : x ∈ vOne) : tInv * x * tInv⁻¹ ∈ vOne := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, hn⟩ := tInv_spec.2.2.1 m
  exact ⟨n, hn⟩

theorem tInv_conj_mem_vTwo {x : Perm (Fin 7)} (hx : x ∈ vTwo) : tInv * x * tInv⁻¹ ∈ vTwo := by
  obtain ⟨m, rfl⟩ := hx
  obtain ⟨n, hn⟩ := tInv_spec.2.2.2 m
  exact ⟨n, hn⟩


@[expose] def autRep : Fin 8 → Perm (Fin 7) :=
  ![1, sw 0 3 * sw 1 4 * sw 2 5 * sw 4 5, sw 1 2 * sw 4 5, sw 0 3 * sw 1 5 * sw 2 4 * sw 4 5,
    sw 0 1,
    sw 0 4 * sw 1 3 * sw 2 5 * sw 3 4 * sw 4 5, sw 0 2 * sw 1 2 * sw 4 5,
    sw 0 5 * sw 1 3 * sw 2 4 * sw 3 5 * sw 4 5]

theorem card_filter_normalizer_eNine : (Finset.univ.filter (fun g : Perm (Fin 7) =>
    g 6 = 6 ∧ (∃ i j : Fin 3, g * cOne = eNineF i j * g) ∧
      (∃ i j : Fin 3, g * cTwo = eNineF i j * g) ∧
      ¬ ∃ d : Fin 8, ∃ i j : Fin 3, g = autRep d * eNineF i j)).card = 0 := by
  refine Finset.card_eq_zero.2 (Finset.filter_eq_empty_iff.2 fun g _ ⟨h6, h₁, h₂, hn⟩ => hn ?_)
  obtain ⟨t, -, ht⟩ := KP2K.norm_of
    (fun p : Fin 8 × Fin 3 × Fin 3 => autRep p.1 * eNineF p.2.1 p.2.2) KP2K.TN
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) KP2K.walkN g
    h6 h₁ h₂
  exact ⟨t.1.1, t.1.2.1, t.1.2.2, ht⟩

theorem eNineF_apply_six : ∀ i j : Fin 3, eNineF i j 6 = 6 := by
  decide +kernel

theorem eq_six_of_fixed : ∀ y : Fin 7, cOne y = y → cTwo y = y → y = 6 := by
  decide +kernel

theorem apply_six_of_mem_normalizer {g : Perm (Fin 7)}
    (hg : g ∈ normalizer (eNine : Set (Perm (Fin 7)))) : g 6 = 6 := by
  have hfix : ∀ e ∈ eNine, e (g⁻¹ 6) = g⁻¹ 6 := by
    intro e he
    obtain ⟨i, j, hij⟩ := (mem_normalizer_iff.1 hg e).1 he
    have h := congrArg (fun σ : Perm (Fin 7) => σ 6) hij
    simp only [Perm.mul_apply, eNineF_apply_six] at h
    have h' := congrArg (⇑(g⁻¹ : Perm (Fin 7))) h
    simpa using h'
  have h6 := congrArg (⇑g) (eq_six_of_fixed _ (hfix _ cOne_mem_eNine) (hfix _ cTwo_mem_eNine))
  simp only [Perm.coe_inv, Equiv.apply_symm_apply] at h6
  exact h6.symm

theorem exists_mul_eq_of_mem_normalizer {g e : Perm (Fin 7)}
    (hg : g ∈ normalizer (eNine : Set (Perm (Fin 7)))) (he : e ∈ eNine) :
    ∃ i j : Fin 3, g * e = eNineF i j * g := by
  obtain ⟨i, j, hij⟩ := (mem_normalizer_iff.1 hg e).1 he
  exact ⟨i, j, by rw [← hij]; group⟩

theorem autRep_spec : (∀ d : Fin 4, autRep (Fin.castLE (by norm_num) d) = rFour ^ (d : ℕ)) ∧
    (∀ d : Fin 8, 4 ≤ (d : ℕ) → Perm.sign (autRep d) = -1) ∧
    (∀ (d : Fin 8) (i j : Fin 3), ∃ i' j' : Fin 3, (autRep d * eNineF i j) ^ 4 = eNineF i' j') := by
  decide +kernel

theorem rFour_spec : Perm.sign rFour = 1 ∧ rFour * cOne * rFour⁻¹ = cTwo ∧
    rFour * cTwo * rFour⁻¹ = cOne⁻¹ ∧ rFour ^ 2 = tInv ∧ rFour ^ 4 = 1 := by
  decide +kernel

theorem exists_autRep_of_mem_normalizer {g : Perm (Fin 7)}
    (hg : g ∈ normalizer (eNine : Set (Perm (Fin 7)))) :
    ∃ d : Fin 8, ∃ i j : Fin 3, g = autRep d * eNineF i j := by
  by_contra hne
  exact forall_not_of_card_filter_eq_zero card_filter_normalizer_eNine g
    ⟨apply_six_of_mem_normalizer hg, exists_mul_eq_of_mem_normalizer hg cOne_mem_eNine,
      exists_mul_eq_of_mem_normalizer hg cTwo_mem_eNine, hne⟩

theorem exists_rFour_pow_of_mem_normalizer {g : Perm (Fin 7)}
    (hg : g ∈ normalizer (eNine : Set (Perm (Fin 7)))) (hA : g ∈ alternatingGroup (Fin 7)) :
    ∃ k : Fin 4, ∃ i j : Fin 3, g = rFour ^ (k : ℕ) * eNineF i j := by
  obtain ⟨d, i, j, rfl⟩ := exists_autRep_of_mem_normalizer hg
  rcases Nat.lt_or_ge (d : ℕ) 4 with hd | hd
  · refine ⟨⟨d, hd⟩, i, j, ?_⟩
    have := autRep_spec.1 ⟨d, hd⟩
    rw [← this]
    rfl
  · exfalso
    have h1 : Perm.sign (autRep d * eNineF i j) = 1 := hA
    rw [map_mul, autRep_spec.2.1 d hd, eNineF_sign] at h1
    exact absurd h1 (by decide)

theorem pow_four_mem_eNine_of_mem_normalizer {g : Perm (Fin 7)}
    (hg : g ∈ normalizer (eNine : Set (Perm (Fin 7)))) : g ^ 4 ∈ eNine := by
  obtain ⟨d, i, j, rfl⟩ := exists_autRep_of_mem_normalizer hg
  obtain ⟨i', j', h⟩ := autRep_spec.2.2 d i j
  exact ⟨i', j', h⟩

theorem swap_zero_one_spec :
    sw 0 1 * cOne * (sw 0 1)⁻¹ = cOne⁻¹ ∧ sw 0 1 * cTwo * (sw 0 1)⁻¹ = cTwo := by
  decide +kernel

theorem cycleType_of_orderOf_eq_three {σ : Perm (Fin 7)} (h : orderOf σ = 3) :
    σ.cycleType = {3} ∨ σ.cycleType = {3, 3} := by
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (h ▸ Nat.prime_three)
  rw [h] at hn
  have hsum : σ.cycleType.sum ≤ 7 := by
    rw [Perm.sum_cycleType]
    simpa using σ.support.card_le_univ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  rcases Nat.lt_or_ge n 1 with h1 | h1
  · left
    rw [hn, show n = 0 by omega]
    rfl
  · right
    rw [hn, show n = 1 by omega]
    rfl

theorem cycleType_of_pow_three {σ : Perm (Fin 7)} (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    σ.cycleType = Multiset.replicate (σ.support.card / 3) 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have ho : orderOf σ = 3 := orderOf_eq_prime h3 h1
  obtain ⟨n, hn⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_three)
  rw [ho] at hn
  have hsum := Perm.sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  rw [hn, ← hsum, Nat.mul_div_cancel _ (by norm_num)]

theorem eNineF_support_card : ∀ i j : Fin 3, (i, j) ≠ (0, 0) →
    ((eNineF i j).support.card = 3 ↔ (i = 0 ∨ j = 0)) ∧
      ((eNineF i j).support.card = 6 ↔ (i ≠ 0 ∧ j ≠ 0)) := by
  decide +kernel

theorem eNineF_cycleType (i j : Fin 3) (hij : (i, j) ≠ (0, 0)) :
    (((eNineF i j).cycleType = {3}) ↔ (i = 0 ∨ j = 0)) ∧
      (((eNineF i j).cycleType = {3, 3}) ↔ (i ≠ 0 ∧ j ≠ 0)) := by
  have h1 : eNineF i j ≠ 1 := fun h =>
    hij (eNineF_injective (i, j) (0, 0) (by rw [h]; rfl))
  rw [cycleType_of_pow_three (eNineF_pow_three i j) h1]
  obtain ⟨h3, h6⟩ := eNineF_support_card i j hij
  rw [← h3, ← h6]
  have hle : (eNineF i j).support.card ≤ 7 := by simpa using (eNineF i j).support.card_le_univ
  have hdvd : 3 ∣ (eNineF i j).support.card := by
    rw [← Perm.sum_cycleType, cycleType_of_pow_three (eNineF_pow_three i j) h1,
      Multiset.sum_replicate, smul_eq_mul]
    exact dvd_mul_left 3 _
  constructor
  · constructor
    · intro h
      have := congrArg Multiset.card h
      simp at this
      omega
    · intro h
      rw [h]
      rfl
  · constructor
    · intro h
      have := congrArg Multiset.card h
      simp at this
      omega
    · intro h
      rw [h]
      rfl

@[expose] def zSeven : Perm (Fin 7) := sw 0 1 * sw 1 2 * sw 2 3 * sw 3 4 * sw 4 5 * sw 5 6

@[expose] def gSeven : Perm (Fin 7) := sw 1 2 * sw 2 4 * sw 3 6 * sw 5 6

theorem seven_spec_aux : gSeven ^ 3 = 1 ∧ gSeven ≠ 1 ∧ gSeven.support.card = 6 ∧
    gSeven * zSeven * gSeven⁻¹ = zSeven ^ 2 ∧ zSeven ^ 7 = 1 ∧ zSeven ≠ 1 ∧
      Perm.sign zSeven = 1 := by
  decide +kernel

theorem seven_spec : gSeven.cycleType = {3, 3} ∧ gSeven * zSeven * gSeven⁻¹ = zSeven ^ 2 ∧
    zSeven ^ 7 = 1 ∧ zSeven ≠ 1 ∧ Perm.sign zSeven = 1 := by
  obtain ⟨h3, h1, h6, h⟩ := seven_spec_aux
  refine ⟨?_, h⟩
  rw [cycleType_of_pow_three h3 h1, h6]
  rfl

theorem exists_orderOf_seven_of_cycleType {x : Perm (Fin 7)} (hx : x.cycleType = {3, 3}) :
    ∃ y ∈ alternatingGroup (Fin 7), orderOf y = 7 ∧ x * y * x⁻¹ = y ^ 2 := by
  obtain ⟨hg, hgz, hz7, hz1, hzs⟩ := seven_spec
  obtain ⟨c, hc⟩ := Perm.isConj_iff_cycleType_eq.2 (hx.trans hg.symm)
  set k : Perm (Fin 7) := (c : Perm (Fin 7))
  have hcx : x = k⁻¹ * gSeven * k := by
    have h : k * x = gSeven * k := hc.eq
    rw [show x = k⁻¹ * (k * x) by group, h]
    group
  have hconj : k⁻¹ * zSeven * k = MulAut.conj k⁻¹ zSeven := by
    rw [MulAut.conj_apply, inv_inv]
  refine ⟨k⁻¹ * zSeven * k, ?_, ?_, ?_⟩
  · change Perm.sign _ = 1
    rw [map_mul, map_mul, map_inv, hzs, mul_one, inv_mul_cancel]
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    rw [hconj, MulEquiv.orderOf_eq]
    exact orderOf_eq_prime hz7 hz1
  · have h2 : (k⁻¹ * zSeven * k) ^ 2 = k⁻¹ * zSeven ^ 2 * k := by
      rw [hconj, ← map_pow, MulAut.conj_apply, inv_inv]
    rw [h2, hcx, ← hgz]
    group

end CFSG.RankThree.PartTwo.KFacts.KP2
