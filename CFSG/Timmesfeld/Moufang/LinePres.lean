module

public import CFSG.Timmesfeld.Moufang.Endgame
public import CFSG.Certificates.WordPresentation

public section

namespace CFSG.Timmesfeld.Moufang

open CFSG.Certificates
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem isConj_of_mul_pow_three {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 3 = 1) : IsConj a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [isConj_iff]
  refine ⟨a * b, ?_⟩
  calc a * b * a * (a * b)⁻¹ = (a * b) * (a * b) * (a * b) * b⁻¹ := by
        conv_lhs => rw [mul_inv_rev, ha', hb']
        group
    _ = b := by rw [← pow_three', h, one_mul, hb']

theorem isConj_of_mul_pow_five {a b : G} (ha : a * a = 1) (hb : b * b = 1)
    (h : (a * b) ^ 5 = 1) : IsConj a b := by
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  rw [isConj_iff]
  refine ⟨(a * b) * (a * b), ?_⟩
  calc a * b * (a * b) * a * (a * b * (a * b))⁻¹ =
        (a * b) * (a * b) * (a * b) * (a * b) * (a * b) * b⁻¹ := by
        conv_lhs => rw [mul_inv_rev, mul_inv_rev, ha', hb']
        group
    _ = b := by
      rw [show (a * b) * (a * b) * (a * b) * (a * b) * (a * b) = (a * b) ^ 5 by
        simp only [pow_succ, pow_zero, one_mul], h, one_mul, hb']

theorem LineConfig.isConj {n : ℕ} {d c : G} {x : Fin n → G} (h : LineConfig d c x) (i : Fin n) :
    IsConj d (x i) ∧ IsConj d (d * x i) := by
  have hdc := isConj_of_mul_pow_five h.d_sq h.c_sq h.dc_pow
  have hdx : d * x i * (d * x i) = 1 := by
    rw [show d * x i * (d * x i) = d * (x i * d) * x i by group, ← (h.d_comm i).eq,
      show d * (d * x i) * x i = (d * d) * (x i * x i) by group, h.d_sq, h.x_sq i, one_mul]
  exact ⟨hdc.trans (isConj_of_mul_pow_three h.c_sq (h.x_sq i) (h.cx_pow i)),
    hdc.trans (isConj_of_mul_pow_five h.c_sq hdx (h.cdx_pow i))⟩

@[expose] def letterD {n : ℕ} : Fin (n + 2) × Bool := (0, true)

@[expose] def letterC {n : ℕ} : Fin (n + 2) × Bool := (1, true)

@[expose] def letterX {n : ℕ} (i : Fin n) : Fin (n + 2) × Bool := (i.addNat 2, true)

@[expose] def lineRels (n : ℕ) (ovoid : Bool) : List (List (Fin (n + 2) × Bool)) :=
  [[letterD, letterD], [letterC, letterC], (List.replicate 5 [letterD, letterC]).flatten] ++
    (List.finRange n).flatMap (fun i => [[letterX i, letterX i],
      [letterD, letterX i, letterD, letterX i], (List.replicate 3 [letterC, letterX i]).flatten,
      (List.replicate 5 [letterC, letterD, letterX i]).flatten]) ++
    (List.finRange n).flatMap (fun i => (List.finRange n).filterMap fun j =>
      if i < j then some [letterX i, letterX j, letterX i, letterX j, letterD] else none) ++
    (if ovoid then [(List.finRange n).map letterX] else [])

@[expose] def lineGens {α : Type*} {n : ℕ} (d c : α) (x : Fin n → α) (j : Fin (n + 2)) : α :=
  if _h : j.val < 2 then (if j.val = 0 then d else c) else x ⟨j.val - 2, by have := j.isLt; omega⟩

section Gens

variable {α : Type*} {n : ℕ} (d c : α) (x : Fin n → α)

@[simp] theorem lineGens_zero : lineGens d c x 0 = d := by
  simp [lineGens]

@[simp] theorem lineGens_one : lineGens d c x 1 = c := by
  simp [lineGens]

@[simp] theorem lineGens_addNat (i : Fin n) : lineGens d c x (i.addNat 2) = x i := by
  simp [lineGens]

theorem range_lineGens : Set.range (lineGens d c x) = insert d (insert c (Set.range x)) := by
  ext y
  simp only [Set.mem_range, Set.mem_insert_iff]
  constructor
  · rintro ⟨j, rfl⟩
    unfold lineGens
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr ⟨_, rfl⟩)
  · rintro (rfl | rfl | ⟨i, rfl⟩)
    · exact ⟨0, lineGens_zero _ _ _⟩
    · exact ⟨1, lineGens_one _ _ _⟩
    · exact ⟨i.addNat 2, lineGens_addNat _ _ _ i⟩

end Gens

section Words

variable {n : ℕ} (d c : G) (x : Fin n → G)

@[simp] theorem signedProd_letterD (w : List (Fin (n + 2) × Bool)) :
    signedProd (lineGens d c x) (letterD :: w) = d * signedProd (lineGens d c x) w := by
  simp [signedProd_cons, letterD]

@[simp] theorem signedProd_letterC (w : List (Fin (n + 2) × Bool)) :
    signedProd (lineGens d c x) (letterC :: w) = c * signedProd (lineGens d c x) w := by
  simp [signedProd_cons, letterC]

@[simp] theorem signedProd_letterX (i : Fin n) (w : List (Fin (n + 2) × Bool)) :
    signedProd (lineGens d c x) (letterX i :: w) = x i * signedProd (lineGens d c x) w := by
  simp [signedProd_cons, letterX]

end Words

theorem LineConfig.signedProd_lineRels {n : ℕ} {d c : G} {x : Fin n → G} (h : LineConfig d c x)
    {ovoid : Bool}
    (hov : ovoid = true → signedProd (lineGens d c x) ((List.finRange n).map letterX) = 1) :
    ∀ w ∈ lineRels n ovoid, signedProd (lineGens d c x) w = 1 := by
  intro w hw
  simp only [lineRels, List.mem_append, List.mem_cons, List.mem_flatMap, List.mem_finRange,
    true_and, List.mem_filterMap, List.not_mem_nil, or_false] at hw
  rcases hw with (((rfl | rfl | rfl) | ⟨i, rfl | rfl | rfl | rfl⟩) | ⟨i, j, hw⟩) | hw
  · simpa using h.d_sq
  · simpa using h.c_sq
  · rw [signedProd_replicate]; simpa using h.dc_pow
  · simpa using h.x_sq i
  · simp only [signedProd_letterD, signedProd_letterX, signedProd_nil, mul_one]
    rw [show d * (x i * (d * x i)) = d * (x i * d) * x i by group, ← (h.d_comm i).eq,
      show d * (d * x i) * x i = (d * d) * (x i * x i) by group, h.d_sq, h.x_sq i, one_mul]
  · rw [signedProd_replicate]; simpa using h.cx_pow i
  · rw [signedProd_replicate]; simpa using h.cdx_pow i
  · split_ifs at hw with hij
    · obtain rfl := Option.some.inj hw
      simp only [signedProd_letterD, signedProd_letterX, signedProd_nil, mul_one]
      have h2 := h.sq_eq i j (ne_of_lt hij)
      rw [show x i * (x j * (x i * (x j * d))) = (x i * x j) ^ 2 * d by rw [sq]; group, h2,
        h.d_sq]
  · split_ifs at hw with hov'
    · rw [List.mem_singleton] at hw
      rw [hw]
      exact hov hov'
    · simp at hw

private theorem mul_eq_one_of_pow_three {A : Type*} [CommGroup A] {a b : A} (ha : a * a = 1)
    (hb : b * b = 1) (h : (a * b) ^ 3 = 1) : a * b = 1 := by
  have h2 : (a * b) ^ 2 = 1 := by rw [mul_pow, sq, sq, ha, hb, one_mul]
  rwa [pow_succ, h2, one_mul] at h

private theorem mul_eq_one_of_pow_five {A : Type*} [CommGroup A] {a b : A} (ha : a * a = 1)
    (hb : b * b = 1) (h : (a * b) ^ 5 = 1) : a * b = 1 := by
  have h2 : (a * b) ^ 2 = 1 := by rw [mul_pow, sq, sq, ha, hb, one_mul]
  rwa [show (5 : ℕ) = 2 * 2 + 1 from rfl, pow_succ, pow_mul, h2, one_pow, one_mul] at h

theorem LineConfig.commutator_eq_top {n : ℕ} (hn : 2 ≤ n) {d c : G} {x : Fin n → G}
    (h : LineConfig d c x) (hgen : Subgroup.closure (insert d (insert c (Set.range x))) = ⊤) :
    commutator G = ⊤ := by
  set f : G →* Abelianization G := Abelianization.of
  have hD : f d * f d = 1 := by rw [← map_mul, h.d_sq, map_one]
  have hC : f c * f c = 1 := by rw [← map_mul, h.c_sq, map_one]
  have hX : ∀ i, f (x i) * f (x i) = 1 := fun i => by rw [← map_mul, h.x_sq i, map_one]
  have hDC : f d * f c = 1 :=
    mul_eq_one_of_pow_five hD hC (by rw [← map_mul, ← map_pow, h.dc_pow, map_one])
  have hCX : ∀ i, f c * f (x i) = 1 := fun i =>
    mul_eq_one_of_pow_three hC (hX i) (by rw [← map_mul, ← map_pow, h.cx_pow i, map_one])
  have hd1 : f d = 1 := by
    have h01 := congrArg f (h.sq_eq ⟨0, by omega⟩ ⟨1, by omega⟩ (Fin.ne_of_val_ne (by norm_num)))
    rw [map_pow, map_mul, mul_pow, sq, sq, hX, hX, one_mul] at h01
    exact h01.symm
  have hc1 : f c = 1 := by rwa [hd1, one_mul] at hDC
  have hx1 : ∀ i, f (x i) = 1 := fun i => by
    have := hCX i
    rwa [hc1, one_mul] at this
  rw [eq_top_iff, ← hgen, ← Abelianization.ker_of, Subgroup.closure_le]
  rintro y (rfl | rfl | ⟨i, rfl⟩)
  · exact hd1
  · exact hc1
  · exact hx1 i

theorem commute_of_mem_normal_of_prime (hperf : commutator G = ⊤) {Q : Subgroup G} [hQ : Q.Normal]
    {p : ℕ} (hp : p.Prime) (hQp : Nat.card Q = p) {z : G} (hzQ : z ∈ Q) (g : G) :
    g * z = z * g := by
  by_cases hz1 : z = 1
  · rw [hz1, mul_one, one_mul]
  have hQz : Q = Subgroup.zpowers z := by
    have : Finite Q := Nat.finite_of_card_ne_zero (by rw [hQp]; exact hp.ne_zero)
    have hdvd : orderOf z ∣ p := hQp ▸ Subgroup.orderOf_dvd_natCard Q hzQ
    have hne1 : orderOf z ≠ 1 := fun h1 => hz1 (orderOf_eq_one_iff.mp h1)
    have hord : orderOf z = p := ((Nat.dvd_prime hp).mp hdvd).resolve_left hne1
    refine (Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hzQ) ?_).symm
    rw [Nat.card_zpowers, hord, hQp]
  have hpow : ∀ a : G, ∃ k : ℤ, a * z * a⁻¹ = z ^ k := by
    intro a
    have : a * z * a⁻¹ ∈ Q := hQ.conj_mem z hzQ a
    rw [hQz] at this
    obtain ⟨k, hk⟩ := this
    exact ⟨k, hk.symm⟩
  have hcomm : ∀ a b : G, ⁅a, b⁆ * z = z * ⁅a, b⁆ := by
    intro a b
    obtain ⟨i, hi⟩ := hpow a⁻¹
    obtain ⟨j, hj⟩ := hpow b⁻¹
    have hab : (a⁻¹ * b⁻¹) * z * (a⁻¹ * b⁻¹)⁻¹ = (b⁻¹ * a⁻¹) * z * (b⁻¹ * a⁻¹)⁻¹ := by
      calc (a⁻¹ * b⁻¹) * z * (a⁻¹ * b⁻¹)⁻¹ = a⁻¹ * (b⁻¹ * z * b⁻¹⁻¹) * a⁻¹⁻¹ := by group
        _ = z ^ (j * i) := by rw [hj, ← conj_zpow, hi, ← zpow_mul, mul_comm]
        _ = b⁻¹ * (a⁻¹ * z * a⁻¹⁻¹) * b⁻¹⁻¹ := by rw [hi, ← conj_zpow, hj, ← zpow_mul]
        _ = (b⁻¹ * a⁻¹) * z * (b⁻¹ * a⁻¹)⁻¹ := by group
    rw [commutatorElement_def]
    calc a * b * a⁻¹ * b⁻¹ * z = (b⁻¹ * a⁻¹)⁻¹ * ((a⁻¹ * b⁻¹) * z * (a⁻¹ * b⁻¹)⁻¹) *
        (a⁻¹ * b⁻¹) := by group
      _ = (b⁻¹ * a⁻¹)⁻¹ * ((b⁻¹ * a⁻¹) * z * (b⁻¹ * a⁻¹)⁻¹) * (a⁻¹ * b⁻¹) := by rw [hab]
      _ = z * (a * b * a⁻¹ * b⁻¹) := by group
  have hle : commutator G ≤ Subgroup.centralizer {z} := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm a b)
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hperf ▸ Subgroup.mem_top g))

theorem le_center_of_card_le_three (hperf : commutator G = ⊤) {N : Subgroup G} [N.Normal]
    [Finite N] (hN : Nat.card N ≤ 3) : N ≤ Subgroup.center G := by
  intro z hz
  rw [Subgroup.mem_center_iff]
  have hpos : 0 < Nat.card N := Nat.card_pos
  obtain h | h | h : Nat.card N = 1 ∨ Nat.card N = 2 ∨ Nat.card N = 3 := by omega
  · have hb := Subgroup.eq_bot_of_card_eq N h
    rw [hb, Subgroup.mem_bot] at hz
    intro g
    rw [hz, mul_one, one_mul]
  · exact commute_of_mem_normal_of_prime hperf Nat.prime_two h hz
  · exact commute_of_mem_normal_of_prime hperf Nat.prime_three h hz

end CFSG.Timmesfeld.Moufang
