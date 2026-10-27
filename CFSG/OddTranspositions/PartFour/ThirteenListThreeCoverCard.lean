module

public import CFSG.OddTranspositions.PartFour.ThirteenListThreeCover
public import Certificates.Certificate704101
import CFSG.OddTranspositions.PartFour.ThirteenListThreeCoverOrder
import CFSG.Timmesfeld.Bridge.Asc72YCount

public section

namespace CFSG.OddTranspositions.PartFour.CoverCard

open CFSG.CosetTable CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

section Order

theorem card_coverPG_le :
    Finite (PG 6 coverWords) ∧ Nat.card (PG 6 coverWords) ≤ 19595520 :=
  Certificates.certificate704101

end Order

@[expose] def form0 (x y : Fin 6 → ZMod 3) : ZMod 3 :=
  -(x 0 * y 2 + x 2 * y 0 + x 1 * y 3 + x 3 * y 1) + x 4 * y 4 + x 5 * y 5

@[expose] def rf0 (v x : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 := x + form0 x v • v

@[expose] def gvec : Fin 6 → Fin 6 → ZMod 3 :=
  ![![1, 0, 2, 1, 2, 2], ![0, 0, 0, 1, 0, 2], ![0, 0, 1, 2, 0, 2], ![1, 0, 1, 0, 0, 0],
    ![0, 0, 1, 2, 2, 0], ![1, 2, 2, 0, 1, 2]]

@[expose] def iterRefl (u : List (Fin 6)) (x : Fin 6 → ZMod 3) : Fin 6 → ZMod 3 :=
  u.foldl (fun y k => rf0 (gvec k) y) x

@[expose] def code (x : Fin 6 → ZMod 3) : ℕ :=
  (x 0).val + 3 * (x 1).val + 9 * (x 2).val + 27 * (x 3).val + 81 * (x 4).val + 243 * (x 5).val

theorem code_injective : Function.Injective code := by
  intro x y h
  have hx : ∀ i, (x i).val < 3 := fun i => ZMod.val_lt (x i)
  have hy : ∀ i, (y i).val < 3 := fun i => ZMod.val_lt (y i)
  have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3; have h4 := hx 4
  have h5 := hx 5; have k0 := hy 0; have k1 := hy 1; have k2 := hy 2; have k3 := hy 3
  have k4 := hy 4; have k5 := hy 5
  unfold code at h
  funext i
  apply ZMod.val_injective
  fin_cases i <;> simp <;> omega

theorem eta6 (c : Fin 6 → ZMod 3) : ![c 0, c 1, c 2, c 3, c 4, c 5] = c := by
  funext i
  fin_cases i <;> rfl

theorem gvec_norm : ∀ i, form0 (gvec i) (gvec i) = 1 := by decide +kernel

@[expose] def PairOK (r : PairRel) : Prop :=
  form0 (iterRefl r.u (gvec r.i)) (iterRefl r.u (gvec r.i)) = 1 ∧
    form0 (iterRefl r.v (gvec r.j)) (iterRefl r.v (gvec r.j)) = 1 ∧
    ((r.m = 1 ∧ (iterRefl r.v (gvec r.j) = iterRefl r.u (gvec r.i) ∨
        iterRefl r.v (gvec r.j) = -iterRefl r.u (gvec r.i))) ∨
      (r.m = 2 ∧ form0 (iterRefl r.u (gvec r.i)) (iterRefl r.v (gvec r.j)) = 0) ∨
      (r.m = 3 ∧ form0 (iterRefl r.u (gvec r.i)) (iterRefl r.v (gvec r.j)) ≠ 0))

instance (r : PairRel) : Decidable (PairOK r) := by
  unfold PairOK
  infer_instance

theorem pairOK_all : ∀ r ∈ coxRels ++ consRels, PairOK r := by decide +kernel

@[expose] def killVecs : List (Fin 6 → ZMod 3) := killConj.map fun p => iterRefl p.1 (gvec p.2)

theorem killVecs_norm : ∀ a ∈ killVecs, form0 a a = 1 := by decide +kernel

theorem killVecs_orth : killVecs.Pairwise fun a b => form0 a b = 0 := by decide +kernel

private theorem killVecs_prod_code : ∀ a₀ a₁ a₂ a₃ a₄ a₅ : ZMod 3,
    code (killVecs.foldr rf0 ![a₀, a₁, a₂, a₃, a₄, a₅]) = code (-![a₀, a₁, a₂, a₃, a₄, a₅]) := by
  decide +kernel

theorem killVecs_prod (y : Fin 6 → ZMod 3) : killVecs.foldr rf0 y = -y := by
  have h := killVecs_prod_code (y 0) (y 1) (y 2) (y 3) (y 4) (y 5)
  rw [eta6] at h
  exact code_injective h

@[expose] def orbitData : List (Fin 6 × List (Fin 6) × ℕ) :=
  [(3, [], 10),
    (1, [], 513),
    (0, [], 694),
    (2, [], 549),
    (4, [], 225),
    (5, [], 592),
    (1, [2], 252),
    (0, [1], 478),
    (1, [5], 203),
    (2, [5], 239),
    (3, [4], 109),
    (2, [3], 542),
    (1, [2, 3], 245),
    (2, [5, 1], 455),
    (1, [5, 2], 464),
    (1, [2, 5], 88),
    (2, [3, 5], 229),
    (2, [3, 4], 686),
    (0, [1, 2], 190),
    (0, [1, 5], 624),
    (0, [1, 2, 3], 207),
    (2, [5, 1, 0], 490),
    (1, [5, 2, 3], 471),
    (2, [3, 4, 5], 130),
    (2, [3, 5, 1], 445),
    (1, [2, 3, 4], 470),
    (0, [1, 2, 5], 539),
    (0, [1, 5, 2], 102),
    (1, [2, 3, 5], 105),
    (2, [3, 5, 1, 2], 706),
    (1, [2, 3, 4, 5], 60),
    (0, [1, 2, 5, 1], 26),
    (2, [3, 5, 1, 0], 507),
    (1, [5, 2, 3, 4], 246),
    (0, [1, 5, 2, 3], 85),
    (0, [1, 5, 2, 1], 399),
    (2, [3, 4, 5, 1], 346),
    (1, [2, 3, 5, 2], 366),
    (0, [1, 2, 3, 4], 81),
    (0, [1, 2, 3, 5], 529),
    (1, [2, 3, 4, 5, 2], 267),
    (2, [3, 5, 1, 0, 2], 39),
    (0, [1, 5, 2, 1, 3], 382),
    (2, [3, 4, 5, 1, 0], 705),
    (0, [1, 2, 3, 5, 1], 16),
    (2, [3, 4, 5, 1, 2], 607),
    (0, [1, 2, 3, 4, 5], 673),
    (0, [1, 5, 2, 3, 4], 211),
    (0, [1, 2, 3, 5, 2], 61),
    (0, [1, 2, 3, 4, 5, 1], 241),
    (2, [3, 4, 5, 1, 0, 2], 183),
    (0, [1, 2, 3, 4, 5, 2], 205),
    (0, [1, 2, 3, 5, 2, 1], 493),
    (2, [3, 5, 1, 0, 2, 1], 255),
    (2, [3, 4, 5, 1, 2, 3], 617),
    (1, [2, 3, 4, 5, 2, 3], 250),
    (0, [1, 2, 3, 5, 1, 2], 565),
    (0, [1, 5, 2, 1, 3, 2], 589),
    (0, [1, 5, 2, 1, 3, 4], 427),
    (2, [3, 5, 1, 0, 2, 1, 5], 82),
    (0, [1, 2, 3, 5, 1, 2, 5], 216),
    (0, [1, 5, 2, 1, 3, 2, 5], 416),
    (0, [1, 2, 3, 5, 2, 1, 5], 171),
    (0, [1, 2, 3, 4, 5, 2, 3], 215),
    (0, [1, 2, 3, 5, 1, 2, 1], 52),
    (0, [1, 2, 3, 4, 5, 1, 2], 682),
    (0, [1, 5, 2, 1, 3, 2, 4], 688),
    (2, [3, 4, 5, 1, 0, 2, 1], 480),
    (0, [1, 2, 3, 4, 5, 2, 1], 718),
    (2, [3, 4, 5, 1, 0, 2, 3], 166),
    (0, [1, 5, 2, 1, 3, 2, 5, 1], 713),
    (0, [1, 2, 3, 4, 5, 1, 2, 5], 117),
    (0, [1, 5, 2, 1, 3, 2, 4, 5], 272),
    (0, [1, 2, 3, 4, 5, 2, 1, 5], 153),
    (0, [1, 2, 3, 4, 5, 1, 2, 1], 169),
    (0, [1, 2, 3, 4, 5, 2, 1, 3], 728),
    (0, [1, 5, 2, 1, 3, 2, 4, 3], 698),
    (2, [3, 4, 5, 1, 0, 2, 1, 5], 64),
    (2, [3, 4, 5, 1, 0, 2, 1, 3], 463),
    (0, [1, 2, 3, 4, 5, 1, 2, 3], 699),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 2], 440),
    (0, [1, 2, 3, 4, 5, 1, 2, 1, 3], 186),
    (0, [1, 5, 2, 1, 3, 2, 4, 5, 1], 488),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 5], 136),
    (0, [1, 2, 3, 4, 5, 1, 2, 3, 5], 110),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 5], 74),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5], 279),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 2], 670),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 2, 5], 87),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 2, 5], 48),
    (0, [1, 2, 3, 4, 5, 1, 2, 1, 3, 2], 447),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 5, 2], 515),
    (0, [1, 2, 3, 4, 5, 1, 2, 3, 5, 2], 578),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 1], 495),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 5, 2], 343),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2], 540),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1], 243),
    (0, [1, 2, 3, 4, 5, 1, 2, 1, 3, 2, 5], 31),
    (0, [1, 2, 3, 4, 5, 1, 2, 3, 5, 2, 1], 362),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 5, 2, 1], 640),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 5, 2, 1], 299),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 1, 2], 315),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 2, 5, 1], 264),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 2, 5, 2], 375),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 2, 5, 1], 600),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 2, 5, 2], 489),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 5, 2, 1, 0], 189),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 5, 2, 1, 0], 180),
    (2, [3, 4, 5, 1, 0, 2, 1, 3, 2, 5, 1, 0], 322),
    (0, [1, 2, 3, 4, 5, 1, 2, 1, 3, 2, 5, 1], 247),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 1, 2, 5], 707),
    (0, [1, 2, 3, 4, 5, 2, 1, 3, 2, 5, 1, 0], 626),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1, 0], 632),
    (0, [1, 2, 3, 4, 5, 1, 2, 3, 5, 2, 1, 0], 667),
    (0, [1, 2, 3, 4, 5, 1, 2, 3, 5, 2, 1, 5], 535),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 1, 2, 1], 531),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1, 5], 662),
    (0, [1, 2, 3, 4, 5, 1, 2, 3, 5, 2, 1, 0, 5], 84),
    (0, [1, 2, 3, 4, 5, 1, 2, 1, 3, 2, 5, 1, 0], 633),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1, 0, 5], 76),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 1, 2, 1, 0], 83),
    (0, [1, 2, 3, 4, 5, 1, 2, 3, 5, 2, 1, 0, 5, 1], 381),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1, 0, 5, 1], 292),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1, 0, 5, 1, 2], 553),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1, 0, 5, 1, 2, 3], 563),
    (0, [1, 5, 2, 1, 3, 2, 4, 3, 5, 2, 1, 0, 5, 1, 2, 3, 4], 581)]

theorem orbitData_code : ∀ e ∈ orbitData, code (iterRefl e.2.1 (gvec e.1)) = e.2.2 := by
  decide +kernel

private theorem orbitData_covers : ∀ a₀ a₁ a₂ a₃ a₄ a₅ : ZMod 3,
    form0 ![a₀, a₁, a₂, a₃, a₄, a₅] ![a₀, a₁, a₂, a₃, a₄, a₅] = 1 →
      ∃ e ∈ orbitData, e.2.2 = code ![a₀, a₁, a₂, a₃, a₄, a₅] ∨
        e.2.2 = code (-![a₀, a₁, a₂, a₃, a₄, a₅]) := by
  decide +kernel

theorem exists_orbit {c : Fin 6 → ZMod 3} (hc : form0 c c = 1) :
    ∃ j u, iterRefl u (gvec j) = c ∨ iterRefl u (gvec j) = -c := by
  have h := orbitData_covers (c 0) (c 1) (c 2) (c 3) (c 4) (c 5) (by rw [eta6]; exact hc)
  rw [eta6] at h
  obtain ⟨e, he, h⟩ := h
  refine ⟨e.1, e.2.1, ?_⟩
  rw [← orbitData_code e he] at h
  rcases h with h | h
  · exact Or.inl (code_injective h)
  · exact Or.inr (code_injective h)

theorem form0_add_add (x y : Fin 6 → ZMod 3) :
    form0 (x + y) (x + y) = form0 x x + 2 * form0 x y + form0 y y := by
  simp only [form0, Pi.add_apply]
  ring

section Involutions

variable {G : Type*} [Group G]

private theorem eq_of_mul_eq_one_of_sq {x y : G} (hy : y * y = 1) (h : x * y = 1) : x = y :=
  calc x = x * (y * y) := by rw [hy, mul_one]
    _ = x * y * y := by rw [mul_assoc]
    _ = y := by rw [h, one_mul]

private theorem conj_mul_self {x y : G} (hx : x * x = 1) (hy : y * y = 1) :
    y * x * y * (y * x * y) = 1 :=
  calc y * x * y * (y * x * y) = y * x * (y * y) * x * y := by group
    _ = y * (x * x) * y := by rw [hy, mul_one]; group
    _ = 1 := by rw [hx, mul_one, hy]

private theorem conj_eq_of_sq {x y : G} (hx : x * x = 1) (h : (x * y) ^ 2 = 1) :
    y * x * y = x := by
  have h' : x * y * x * y = 1 := by rw [← h, pow_two, ← mul_assoc]
  calc y * x * y = x * x * (y * x * y) := by rw [hx, one_mul]
    _ = x * (x * y * x * y) := by group
    _ = x := by rw [h', mul_one]

private theorem braid_of_cube {x y : G} (hx : x * x = 1) (hy : y * y = 1) (h : (x * y) ^ 3 = 1) :
    x * y * x = y * x * y := by
  have h' : x * y * x * (y * x * y) = 1 := by
    rw [← h]
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  calc x * y * x = x * y * x * (y * x * y * (y * x * y)) := by rw [conj_mul_self hx hy, mul_one]
    _ = x * y * x * (y * x * y) * (y * x * y) := by group
    _ = y * x * y := by rw [h', one_mul]

private theorem commute_of_sq {x y : G} (hx : x * x = 1) (hy : y * y = 1) (h : (x * y) ^ 2 = 1) :
    x * y = y * x := by
  have h1 : x * y * (x * y) = 1 := by rw [← h, pow_two]
  rw [eq_inv_of_mul_eq_one_left h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hx,
    inv_eq_of_mul_eq_one_right hy]

end Involutions

section OddCentre

variable {X : Type} [Group X]

theorem eq_of_mk_eq_of_odd (hZ : Odd (Nat.card (Subgroup.center X))) {a b : X} (ha : a * a = 1)
    (hb : b * b = 1) (h : (a : X ⧸ Subgroup.center X) = b) : a = b := by
  rw [QuotientGroup.eq] at h
  set z := a⁻¹ * b with hz
  have hb' : b = a * z := by rw [hz, mul_inv_cancel_left]
  have hza : a * z = z * a := Subgroup.mem_center_iff.mp h a
  have hz2 : z * z = 1 := by
    have : b * b = a * a * (z * z) := by
      rw [hb', show a * z * (a * z) = a * (z * a) * z by group, ← hza]
      group
    rw [hb, ha, one_mul] at this
    exact this.symm
  have hdvd2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two, hz2])
  have hdvdZ : orderOf z ∣ Nat.card (Subgroup.center X) := by
    rw [← Subgroup.orderOf_mk z h]
    exact orderOf_dvd_natCard _
  have h1 : orderOf z = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h1
    · exact h1
    · rw [h1] at hdvdZ
      exact absurd (even_iff_two_dvd.mpr hdvdZ) (Nat.not_even_iff_odd.mpr hZ)
  rw [hb', orderOf_eq_one_iff.mp h1, mul_one]

theorem mul_pow_eq_one_of_mk (hZ : Odd (Nat.card (Subgroup.center X))) {a b : X}
    (ha : a * a = 1) (hb : b * b = 1) {m : ℕ} (hm : m = 1 ∨ m = 2 ∨ m = 3)
    (h : ((a : X ⧸ Subgroup.center X) * b) ^ m = 1) : (a * b) ^ m = 1 := by
  have ha' : (a : X ⧸ Subgroup.center X) * a = 1 := by rw [← QuotientGroup.mk_mul, ha]; rfl
  have hb' : (b : X ⧸ Subgroup.center X) * b = 1 := by rw [← QuotientGroup.mk_mul, hb]; rfl
  rcases hm with rfl | rfl | rfl
  · rw [pow_one] at h ⊢
    rw [eq_of_mk_eq_of_odd hZ ha hb (eq_of_mul_eq_one_of_sq hb' h), hb]
  · have hc : ((b * a * b : X) : X ⧸ Subgroup.center X) = a := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact conj_eq_of_sq ha' h
    have heq := eq_of_mk_eq_of_odd hZ (conj_mul_self ha hb) ha hc
    calc (a * b) ^ 2 = a * (b * a * b) := by rw [pow_two]; simp only [mul_assoc]
      _ = 1 := by rw [heq, ha]
  · have hc : ((a * b * a : X) : X ⧸ Subgroup.center X) = (b * a * b : X) := by
      simp only [QuotientGroup.mk_mul]
      exact braid_of_cube ha' hb' h
    have heq := eq_of_mk_eq_of_odd hZ (conj_mul_self hb ha) (conj_mul_self ha hb) hc
    calc (a * b) ^ 3 = a * b * a * (b * a * b) := by
          simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [← heq]; exact conj_mul_self hb ha

theorem list_prod_eq_one_of_mk (hZ : Odd (Nat.card (Subgroup.center X))) (l : List X)
    (hinv : ∀ a ∈ l, a * a = 1) (hcomm : l.Pairwise fun a b => a * b = b * a)
    (h : (l.map (QuotientGroup.mk' (Subgroup.center X))).prod = 1) : l.prod = 1 := by
  have hsq : ∀ l : List X, (∀ a ∈ l, a * a = 1) → (l.Pairwise fun a b => a * b = b * a) →
      l.prod * l.prod = 1 := by
    intro l
    induction l with
    | nil => intro _ _; simp
    | cons a l ih =>
      intro hinv hcomm
      rw [List.pairwise_cons] at hcomm
      have hal : Commute a l.prod := Commute.list_prod_right _ _ fun b hb => hcomm.1 b hb
      rw [List.prod_cons, show a * l.prod * (a * l.prod) = a * (l.prod * a) * l.prod by group,
        ← hal.eq, show a * (a * l.prod) * l.prod = a * a * (l.prod * l.prod) by group,
        hinv a List.mem_cons_self, ih (fun b hb => hinv b (List.mem_cons_of_mem a hb)) hcomm.2,
        one_mul]
  rw [← map_list_prod] at h
  exact eq_of_mk_eq_of_odd hZ (hsq l hinv hcomm) (one_mul 1) h

end OddCentre

section Transport

variable {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}

structure ModelIso (f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)) where
  ι : (Fin 6 → ZMod 3) ≃ₗ[ZMod 3] (Fin 6 → ZMod 3)
  form : ∀ x y, f (ι x) (ι y) = form0 x y

theorem nonempty_modelIso (hf : IsF3Form f)
    (hT : ¬ ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, f x x = 0) :
    Nonempty (ModelIso f) := by
  classical
  have h2 : (2 : ZMod 3) ≠ 0 := by decide
  have h3 : (3 : ZMod 3) = 0 := by decide
  have hQ : (LinearMap.BilinMap.toQuadraticMap f).polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => hf.nondeg v
      fun w => by
        have := hv w
        rw [LinearMap.BilinMap.polar_toQuadraticMap, hf.symm w v, ← two_mul] at this
        exact (mul_eq_zero.mp this).resolve_left h2
  obtain ⟨b, c, hbc, ⟨e⟩⟩ : ∃ b c : ZMod 3, (∀ t : ZMod 3, t ^ 2 + b * t + c ≠ 0) ∧
      Nonempty ((LinearMap.BilinMap.toQuadraticMap f).IsometryEquiv
        (CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 3) b c)) := by
    rcases CFSG.GroupTheory.WeirSylow.exists_isometry_quadPlus_or_quadMinus
        (LinearMap.BilinMap.toQuadraticMap f) hQ (n := 3) (by norm_num)
        (by rw [Module.finrank_fin_fun]) with he | h
    · exfalso
      obtain ⟨e⟩ := he
      obtain ⟨-, T, hT3, hTQ⟩ :=
        CFSG.ClassicalGroups.Orthogonal.regular_quadPlus (K := ZMod 3) (n := 3) le_rfl
      refine hT ⟨T.map e.symm.toLinearEquiv.toLinearMap, ?_, ?_⟩
      · rw [LinearEquiv.finrank_map_eq]
        exact hT3
      · rintro _ ⟨y, hy, rfl⟩
        have := e.symm.map_app y
        rw [LinearMap.BilinMap.toQuadraticMap_apply] at this
        rw [show (e.symm.toLinearEquiv.toLinearMap y) = e.symm y from rfl, this]
        exact hTQ y hy
    · exact h
  have hc : c = b ^ 2 + 1 := by
    have key : ∀ b c : ZMod 3, (∀ t : ZMod 3, t ^ 2 + b * t + c ≠ 0) → c = b ^ 2 + 1 := by
      decide
    exact key b c hbc
  let pr : Fin 6 → (Fin 6 → ZMod 3) →ₗ[ZMod 3] ZMod 3 := fun i => LinearMap.proj i
  let τ : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → ZMod 3) :=
    LinearMap.pi (Sum.elim ![pr 0, pr 1] (Sum.elim ![pr 2, pr 3] ![pr 4 + b • pr 5, pr 5]))
  have hτ : ∀ m : Fin 6 → ZMod 3, τ m (.inl 0) = m 0 ∧ τ m (.inl 1) = m 1 ∧
      τ m (.inr (.inl 0)) = m 2 ∧ τ m (.inr (.inl 1)) = m 3 ∧
      τ m (.inr (.inr 0)) = m 4 + b * m 5 ∧ τ m (.inr (.inr 1)) = m 5 := fun m =>
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hτinj : Function.Injective τ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro m hm
    obtain ⟨t0, t1, t2, t3, t4, t5⟩ := hτ m
    have e0 := congrFun hm (.inl 0); have e1 := congrFun hm (.inl 1)
    have e2 := congrFun hm (.inr (.inl 0)); have e3 := congrFun hm (.inr (.inl 1))
    have e4 := congrFun hm (.inr (.inr 0)); have e5 := congrFun hm (.inr (.inr 1))
    simp only [Pi.zero_apply] at e0 e1 e2 e3 e4 e5
    rw [t0] at e0; rw [t1] at e1; rw [t2] at e2; rw [t3] at e3; rw [t4] at e4; rw [t5] at e5
    rw [e5, mul_zero, add_zero] at e4
    funext i
    fin_cases i
    exacts [e0, e1, e2, e3, e4, e5]
  let ι₀ : (Fin 6 → ZMod 3) →ₗ[ZMod 3] (Fin 6 → ZMod 3) :=
    e.symm.toLinearEquiv.toLinearMap.comp τ
  have hι₀ : Function.Injective ι₀ := e.symm.toLinearEquiv.injective.comp hτinj
  let ι := LinearEquiv.ofInjectiveEndo ι₀ hι₀
  have hnorm : ∀ x, f (ι x) (ι x) = form0 x x := by
    intro x
    have h1 : f (ι x) (ι x) = CFSG.LieType.Universal.Spin.quadMinus 3 (ZMod 3) b c (τ x) := by
      rw [← LinearMap.BilinMap.toQuadraticMap_apply, ← e.symm.map_app (τ x)]
      rfl
    rw [h1, CFSG.LieType.Universal.Spin.quadMinus_apply, Fin.sum_univ_two]
    change x 0 * x 2 + x 1 * x 3 + (x 4 + b * x 5) ^ 2 + b * (x 4 + b * x 5) * x 5 +
      c * x 5 ^ 2 = form0 x x
    rw [hc]
    unfold form0
    linear_combination (x 0 * x 2 + x 1 * x 3 + b * x 4 * x 5 + b ^ 2 * x 5 ^ 2) * h3
  refine ⟨⟨ι, fun x y => ?_⟩⟩
  have h := hnorm (x + y)
  rw [map_add, LinearMap.BilinForm.add_left, LinearMap.BilinForm.add_right,
    LinearMap.BilinForm.add_right, hnorm x, hnorm y, hf.symm (ι y) (ι x), form0_add_add] at h
  linear_combination (2 : ZMod 3) * h - (f (ι x) (ι y) - form0 x y) * h3

theorem ModelIso.norm (I : ModelIso f) {v : Fin 6 → ZMod 3} (hv : form0 v v = 1) :
    f (I.ι v) (I.ι v) = 1 := by
  rw [I.form, hv]

theorem ModelIso.act_refl (I : ModelIso f) {v : Fin 6 → ZMod 3} (hv : form0 v v = 1)
    (x : Fin 6 → ZMod 3) : F3.act (F3.refl f (I.ι v)) (I.ι x) = I.ι (rf0 v x) := by
  rw [F3.act_refl (I.norm hv), I.form, rf0, map_add, map_smul]

theorem ModelIso.reflBar_conj (hf : IsF3Form f) (I : ModelIso f) {v : Fin 6 → ZMod 3}
    (hv : form0 v v = 1) (w : Fin 6 → ZMod 3) :
    reflBar f (I.ι v) * reflBar f (I.ι w) * reflBar f (I.ι v) = reflBar f (I.ι (rf0 v w)) := by
  rw [Fischer.Classification.reflBar_conj hf, I.act_refl hv]

theorem ModelIso.act_list_prod (I : ModelIso f) :
    ∀ l : List (Fin 6 → ZMod 3), (∀ a ∈ l, form0 a a = 1) → ∀ y,
      F3.act (l.map fun k => F3.refl f (I.ι k)).prod (I.ι y) = I.ι (l.foldr rf0 y)
  | [], _, y => by simp [F3.act_one]
  | k :: l, hl, y => by
    rw [List.map_cons, List.prod_cons, F3.act_mul,
      I.act_list_prod l (fun a ha => hl a (List.mem_cons_of_mem k ha)) y,
      I.act_refl (hl k List.mem_cons_self), List.foldr_cons]

end Transport

section Lift

variable {X : Type} [Group X] {s : X}
  {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)}

theorem exists_lift (I : ModelIso f) (φ : X ⧸ Subgroup.center X ≃* R3 f)
    (hφ : ∀ g, g ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x} ↔ φ g ∈ D3 f)
    {c : Fin 6 → ZMod 3} (hc : form0 c c = 1) :
    ∃ d : X, IsConj s d ∧ (d : X ⧸ Subgroup.center X) = φ.symm (reflBar f (I.ι c)) := by
  have hD : φ.symm (reflBar f (I.ι c)) ∈
      {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x} := by
    rw [hφ, MulEquiv.apply_symm_apply]
    exact reflBar_mem_D3 (I.norm hc)
  obtain ⟨g, hg⟩ := isConj_iff.mp hD
  obtain ⟨g', rfl⟩ := QuotientGroup.mk_surjective g
  exact ⟨g' * s * g'⁻¹, isConj_iff.mpr ⟨g', rfl⟩, by rw [← hg]; rfl⟩

private theorem mul_self_of_isConj (hs : s * s = 1) {d : X} (hd : IsConj s d) : d * d = 1 := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp hd
  calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
    _ = 1 := by rw [hs, mul_one, mul_inv_cancel]

@[expose] def conjX (d : Fin 6 → X) (u : List (Fin 6)) (y : X) : X :=
  (u.reverse.map d).prod * y * (u.map d).prod

theorem conjX_cons (d : Fin 6 → X) (k : Fin 6) (u : List (Fin 6)) (y : X) :
    conjX d (k :: u) y = conjX d u (d k * y * d k) := by
  simp only [conjX, List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
    List.prod_append, List.prod_cons, List.prod_nil, mul_one]
  group

theorem prod_reverse_mul_prod (d : Fin 6 → X) (hd : ∀ i, d i * d i = 1) :
    ∀ u : List (Fin 6), (u.reverse.map d).prod * (u.map d).prod = 1
  | [] => by simp
  | k :: u => by
    simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.prod_append, List.prod_cons, List.prod_nil, mul_one]
    rw [show (u.reverse.map d).prod * d k * (d k * (u.map d).prod) =
        (u.reverse.map d).prod * (d k * d k) * (u.map d).prod by group, hd k, mul_one,
      prod_reverse_mul_prod d hd u]

theorem conjX_mul_self (d : Fin 6 → X) (hd : ∀ i, d i * d i = 1) (u : List (Fin 6)) {y : X}
    (hy : y * y = 1) : conjX d u y * conjX d u y = 1 := by
  have hP : (u.reverse.map d).prod = ((u.map d).prod)⁻¹ :=
    eq_inv_of_mul_eq_one_left (prod_reverse_mul_prod d hd u)
  unfold conjX
  rw [hP]
  calc ((u.map d).prod)⁻¹ * y * (u.map d).prod * (((u.map d).prod)⁻¹ * y * (u.map d).prod) =
        ((u.map d).prod)⁻¹ * (y * y) * (u.map d).prod := by group
    _ = 1 := by rw [hy, mul_one, inv_mul_cancel]

theorem conjWord_prod (d : Fin 6 → X) (u : List (Fin 6)) (i : Fin 6) :
    ((conjWord u i).map d).prod = conjX d u (d i) := by
  simp only [conjWord, conjX, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    mul_assoc]

theorem mk_conjX (hf : IsF3Form f) (I : ModelIso f) (φ : X ⧸ Subgroup.center X ≃* R3 f)
    {d : Fin 6 → X} (hd : ∀ i, (d i : X ⧸ Subgroup.center X) = φ.symm (reflBar f (I.ι (gvec i)))) :
    ∀ (u : List (Fin 6)) (y : X) (c : Fin 6 → ZMod 3),
      (y : X ⧸ Subgroup.center X) = φ.symm (reflBar f (I.ι c)) →
        ((conjX d u y : X) : X ⧸ Subgroup.center X) = φ.symm (reflBar f (I.ι (iterRefl u c)))
  | [], y, c, h => by simpa [conjX, iterRefl] using h
  | k :: u, y, c, h => by
    rw [conjX_cons]
    refine mk_conjX hf I φ hd u _ (rf0 (gvec k) c) ?_
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hd k, h, ← map_mul, ← map_mul,
      I.reflBar_conj hf (gvec_norm k)]

end Lift

theorem card_center_le_three {X : Type} [Group X] [Finite X]
    {s : X} (hs : orderOf s = 2) (hncl : Subgroup.normalClosure ({s} : Set X) = ⊤)
    (hZ : Odd (Nat.card (Subgroup.center X)))
    {f : LinearMap.BilinForm (ZMod 3) (Fin 6 → ZMod 3)} (hf : IsF3Form f)
    (hT : ¬ ∃ T : Submodule (ZMod 3) (Fin 6 → ZMod 3), Module.finrank (ZMod 3) T = 3 ∧
      ∀ x ∈ T, f x x = 0)
    (φ : X ⧸ Subgroup.center X ≃* R3 f)
    (hφ : ∀ g, g ∈ {x : X ⧸ Subgroup.center X | IsConj (QuotientGroup.mk s) x} ↔ φ g ∈ D3 f) :
    Nat.card (Subgroup.center X) ≤ 3 := by
  classical
  have hs2 : s * s = 1 := by rw [← pow_two, ← hs, pow_orderOf_eq_one]
  obtain ⟨I⟩ := nonempty_modelIso hf hT
  choose dg hdg using fun i : Fin 6 => exists_lift I φ hφ (gvec_norm i)
  have hdinv : ∀ i, dg i * dg i = 1 := fun i => mul_self_of_isConj hs2 (hdg i).1
  have hdmk : ∀ i, (dg i : X ⧸ Subgroup.center X) = φ.symm (reflBar f (I.ι (gvec i))) :=
    fun i => (hdg i).2
  have himg := mk_conjX hf I φ hdmk
  have hinvC : ∀ u i, conjX dg u (dg i) * conjX dg u (dg i) = 1 := fun u i =>
    conjX_mul_self dg hdinv u (hdinv i)
  have hrel : ∀ r ∈ {r : FreeGroup (Fin 6) | r ∈ coverWords.map FreeGroup.mk},
      FreeGroup.lift dg r = 1 := by
    rintro r hr
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hr
    simp only [coverWords, List.mem_map, List.mem_append, List.mem_singleton] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    rw [FreeGroup.lift_mk, List.map_map]
    have hw'' : ((fun x : Fin 6 × Bool => bif x.2 then dg x.1 else (dg x.1)⁻¹) ∘
        fun x : Fin 6 => (x, true)) = dg := rfl
    rw [hw'']
    rcases hw' with ⟨p, hp, rfl⟩ | rfl
    ·
      obtain ⟨hna, hnb, hcase⟩ := pairOK_all p (List.mem_append.mpr hp)
      have hword : (p.word.map dg).prod =
          (conjX dg p.u (dg p.i) * conjX dg p.v (dg p.j)) ^ p.m := by
        rw [PairRel.word, List.map_flatten, List.prod_flatten, List.map_replicate,
          List.map_replicate, List.prod_replicate, List.map_append, List.prod_append,
          conjWord_prod, conjWord_prod]
      rw [hword]
      have ha := himg p.u (dg p.i) (gvec p.i) (hdmk p.i)
      have hb := himg p.v (dg p.j) (gvec p.j) (hdmk p.j)
      have hm : p.m = 1 ∨ p.m = 2 ∨ p.m = 3 := by
        rcases hcase with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩ <;> simp [h]
      refine mul_pow_eq_one_of_mk hZ (hinvC _ _) (hinvC _ _) hm ?_
      rw [ha, hb, ← map_mul, ← map_pow]
      rw [MulEquiv.map_eq_one_iff]
      rcases hcase with ⟨h1, h⟩ | ⟨h1, h⟩ | ⟨h1, h⟩
      · rw [h1, pow_one]
        rcases h with h | h
        · rw [h, reflBar_mul_self]
        · rw [h, map_neg, reflBar_neg, reflBar_mul_self]
      · rw [h1]
        exact reflBar_mul_pow_two hf (I.norm hna) (I.norm hnb) (by rw [I.form]; exact h)
      · rw [h1]
        exact reflBar_mul_pow_three hf (I.norm hna) (I.norm hnb) (by rw [I.form]; exact h)
    ·
      have hword : (killWord.map dg).prod =
          (killConj.map fun p => conjX dg p.1 (dg p.2)).prod := by
        rw [killWord, List.map_flatten, List.prod_flatten, List.map_map, List.map_map]
        congr 1
        refine List.map_congr_left fun p _ => ?_
        exact conjWord_prod dg p.1 p.2
      rw [hword]
      refine list_prod_eq_one_of_mk hZ _ ?_ ?_ ?_
      · intro a ha
        obtain ⟨p, -, rfl⟩ := List.mem_map.mp ha
        exact hinvC _ _
      · rw [List.pairwise_map]
        have horth := killVecs_orth
        rw [killVecs, List.pairwise_map] at horth
        refine horth.imp_of_mem fun {p q} hp hq hpq => ?_
        refine commute_of_sq (hinvC _ _) (hinvC _ _) ?_
        refine mul_pow_eq_one_of_mk hZ (hinvC _ _) (hinvC _ _) (Or.inr (Or.inl rfl)) ?_
        have hnp := killVecs_norm _ (List.mem_map_of_mem hp)
        have hnq := killVecs_norm _ (List.mem_map_of_mem hq)
        rw [himg p.1 (dg p.2) (gvec p.2) (hdmk p.2), himg q.1 (dg q.2) (gvec q.2) (hdmk q.2),
          ← map_mul, ← map_pow, MulEquiv.map_eq_one_iff]
        exact reflBar_mul_pow_two hf (I.norm hnp) (I.norm hnq) (by rw [I.form]; exact hpq)
      · rw [List.map_map]
        have hmap : (QuotientGroup.mk' (Subgroup.center X) ∘ fun p : List (Fin 6) × Fin 6 =>
            conjX dg p.1 (dg p.2)) = fun p => φ.symm (reflBar f (I.ι (iterRefl p.1 (gvec p.2)))) := by
          funext p
          exact himg p.1 (dg p.2) (gvec p.2) (hdmk p.2)
        have hmap' : (killConj.map fun p => φ.symm (reflBar f (I.ι (iterRefl p.1 (gvec p.2))))) =
            (killConj.map fun p => reflBar f (I.ι (iterRefl p.1 (gvec p.2)))).map φ.symm := by
          rw [List.map_map]
          rfl
        rw [hmap, hmap', ← map_list_prod, MulEquiv.map_eq_one_iff]
        have hl : (killConj.map fun p => reflBar f (I.ι (iterRefl p.1 (gvec p.2)))) =
            (killVecs.map fun k => reflElt f (I.ι k)).map (QuotientGroup.mk' _) := by
          rw [killVecs, List.map_map, List.map_map]
          rfl
        rw [hl, ← map_list_prod, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        have hneg : (((killVecs.map fun k => reflElt f (I.ι k)).prod : F3.reflGroup f) :
            GL (Fin 6) (ZMod 3)) = -1 := by
          rw [Subgroup.val_list_prod, List.map_map]
          have hcoe : ((Subtype.val : F3.reflGroup f → GL (Fin 6) (ZMod 3)) ∘
              fun k => reflElt f (I.ι k)) = fun k => F3.refl f (I.ι k) := rfl
          rw [hcoe]
          refine F3.gl_ext fun x => ?_
          obtain ⟨y, rfl⟩ := I.ι.surjective x
          rw [I.act_list_prod killVecs killVecs_norm y, killVecs_prod, map_neg, F3.act_neg_one]
        rw [Subgroup.mem_center_iff]
        intro g
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul, hneg, mul_neg_one, neg_one_mul]
  let ψ : PG 6 coverWords →* X := PresentedGroup.toGroup hrel
  have hψ : ∀ i, ψ (PresentedGroup.of i) = dg i := fun i => PresentedGroup.toGroup.of hrel
  have hmemR : ∀ i, dg i ∈ ψ.range := fun i => ⟨_, hψ i⟩
  have hconjR : ∀ u i, conjX dg u (dg i) ∈ ψ.range := by
    intro u i
    refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.list_prod_mem _ ?_) (hmemR i))
      (Subgroup.list_prod_mem _ ?_) <;>
    · intro x hx
      obtain ⟨k, -, rfl⟩ := List.mem_map.mp hx
      exact hmemR k
  have hD : ∀ d : X, IsConj s d → d ∈ ψ.range := by
    intro d hd
    have hφd : φ (d : X ⧸ Subgroup.center X) ∈ D3 f :=
      (hφ _).mp ((QuotientGroup.mk' (Subgroup.center X)).map_isConj hd)
    obtain ⟨w, hw, hwd⟩ := mem_D3_iff.mp hφd
    have hcw : I.ι (I.ι.symm w) = w := I.ι.apply_symm_apply w
    have hc : form0 (I.ι.symm w) (I.ι.symm w) = 1 := by rw [← I.form, hcw, hw]
    obtain ⟨j, u, hju⟩ := exists_orbit hc
    have hrefl : reflBar f (I.ι (iterRefl u (gvec j))) = reflBar f w := by
      rcases hju with h | h
      · rw [h, hcw]
      · rw [h, map_neg, reflBar_neg, hcw]
    have hmk : ((conjX dg u (dg j) : X) : X ⧸ Subgroup.center X) = d := by
      rw [himg u (dg j) (gvec j) (hdmk j), hrefl, hwd, MulEquiv.symm_apply_apply]
    rw [← eq_of_mk_eq_of_odd hZ (hinvC u j) (mul_self_of_isConj hs2 hd) hmk]
    exact hconjR u j
  have hrange : ψ.range = ⊤ := by
    rw [eq_top_iff, ← hncl]
    change Subgroup.closure (Group.conjugatesOfSet {s}) ≤ _
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hD x hax
  obtain ⟨hfin, hcard⟩ := card_coverPG_le
  have hX : Nat.card X ≤ 19595520 :=
    (Nat.card_le_card_of_surjective ψ (MonoidHom.range_eq_top.mp hrange)).trans hcard
  have hXbar : 6531840 ≤ Nat.card (X ⧸ Subgroup.center X) := by
    rw [Nat.card_congr φ.toEquiv]
    exact natCard_R3_six_minus_ge hf hT
  have hmul := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X)
  nlinarith

end CFSG.OddTranspositions.PartFour.CoverCard

namespace CFSG.OddTranspositions.PartFour

open CFSG.LocalAnalysis.WeakClosure81 CFSG.Fischer.Classification

theorem oddTranspListThreeTranspReflSixCoverCard_holds :
    OddTranspListThreeTranspReflSixCoverCard := by
  intro X _ _ s hs _ hncl hO2 _ _ _ hZ f hsym hnd hT hM
  obtain ⟨φ, hφ⟩ := (fischerCentralQuotientModel_iff _).mp hM
  have hodd := CFSG.Timmesfeld.Bridge.Asc72.CentralQuot.odd_card_center hO2
  have hle := CoverCard.card_center_le_three hs hncl hodd ⟨hsym, hnd⟩ hT φ hφ
  have h1 : 1 < Nat.card (Subgroup.center X) := (Subgroup.one_lt_card_iff_ne_bot _).mpr hZ
  obtain ⟨k, hk⟩ := hodd
  omega

theorem oddTranspListThreeTranspReflSixCover_holds :
    OddTranspListThreeTranspReflSixCover :=
  oddTranspListThreeTranspReflSixCover_of_card oddTranspListThreeTranspReflSixCoverCard_holds

end CFSG.OddTranspositions.PartFour
