module

public import CFSG.Walter.Ree.Thompson1.Hyp

public section

namespace CFSG.Walter.Ree.Thompson1

open scoped IsMulCommutative

variable {N : Type*} [Group N]

@[expose] def tc (x y : N) : N := x⁻¹ * y⁻¹ * x * y

@[expose] def zc (P : Subgroup N) : Subgroup N := (Subgroup.center P).map P.subtype

theorem mem_zc {P : Subgroup N} {z : N} : z ∈ zc P ↔ z ∈ P ∧ ∀ x ∈ P, x * z = z * x := by
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨w.2, fun x hx => ?_⟩
    have := Subgroup.mem_center_iff.1 hw ⟨x, hx⟩
    exact congrArg Subtype.val this
  · rintro ⟨hz, h⟩
    refine ⟨⟨z, hz⟩, Subgroup.mem_center_iff.2 fun x => Subtype.ext (h x.1 x.2), rfl⟩

theorem zc_le (P : Subgroup N) : zc P ≤ P := fun _ hz => (mem_zc.1 hz).1

theorem tc_eq_one_iff {x y : N} : tc x y = 1 ↔ x * y = y * x := by
  unfold tc
  constructor
  · intro h
    have : x * y = y * x * (x⁻¹ * y⁻¹ * x * y) := by group
    rw [this, h, mul_one]
  · intro h
    calc x⁻¹ * y⁻¹ * x * y = x⁻¹ * y⁻¹ * (x * y) := by group
      _ = x⁻¹ * y⁻¹ * (y * x) := by rw [h]
      _ = 1 := by group

theorem tc_mem_commutator {P : Subgroup N} {x y : N} (hx : x ∈ P) (hy : y ∈ P) :
    tc x y ∈ ⁅P, P⁆ := by
  have := Subgroup.commutator_mem_commutator (P.inv_mem hx) (P.inv_mem hy)
  rwa [commutatorElement_def, inv_inv, inv_inv] at this

theorem tc_inv (x y : N) : (tc x y)⁻¹ = tc y x := by unfold tc; group

theorem tc_conj (r x y : N) : r⁻¹ * tc x y * r = tc (r⁻¹ * x * r) (r⁻¹ * y * r) := by
  unfold tc; group

theorem zc_normal (P : Subgroup N) [hP : P.Normal] : (zc P).Normal := by
  refine ⟨fun z hz g => mem_zc.2 ⟨hP.conj_mem z (zc_le P hz) g, fun x hx => ?_⟩⟩
  have hx' : g⁻¹ * x * g ∈ P := by
    have := hP.conj_mem x hx g⁻¹
    rwa [inv_inv] at this
  have := (mem_zc.1 hz).2 _ hx'
  calc x * (g * z * g⁻¹) = g * ((g⁻¹ * x * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * x * g)) * g⁻¹ := by rw [this]
    _ = g * z * g⁻¹ * x := by group

theorem tc_mul_left (x x' y : N) : tc (x * x') y = (x'⁻¹ * tc x y * x') * tc x' y := by
  unfold tc; group

theorem tc_mul_right (y x x' : N) : tc y (x * x') = tc y x' * (x'⁻¹ * tc y x * x') := by
  unfold tc; group

theorem conj_eq_mul_tc (w x : N) : x⁻¹ * w * x = w * tc w x := by
  unfold tc; group

theorem hall_witt (x y z : N) :
    tc (tc x y) (x⁻¹ * z * x) * tc (tc z x) (z⁻¹ * y * z) * tc (tc y z) (y⁻¹ * x * y) = 1 := by
  unfold tc; group

theorem tc_mem {P : Subgroup N} {x y : N} (hx : x ∈ P) (hy : y ∈ P) : tc x y ∈ P := by
  unfold tc
  exact P.mul_mem (P.mul_mem (P.mul_mem (P.inv_mem hx) (P.inv_mem hy)) hx) hy

theorem zc_comm {P : Subgroup N} {z x : N} (hz : z ∈ zc P) (hx : x ∈ P) : z * x = x * z :=
  ((mem_zc.1 hz).2 x hx).symm

theorem conj_zc {P : Subgroup N} {z x : N} (hz : z ∈ zc P) (hx : x ∈ P) : z⁻¹ * x * z = x := by
  rw [mul_assoc, ← zc_comm hz hx, ← mul_assoc, inv_mul_cancel, one_mul]

theorem tc_zc_left {P : Subgroup N} {z x : N} (hz : z ∈ zc P) (hx : x ∈ P) : tc z x = 1 :=
  tc_eq_one_iff.2 (zc_comm hz hx)

theorem tc_zc_right {P : Subgroup N} {z x : N} (hz : z ∈ zc P) (hx : x ∈ P) : tc x z = 1 :=
  tc_eq_one_iff.2 (zc_comm hz hx).symm

theorem tc_mul_zc_left {P : Subgroup N} {y z x : N} (hy : y ∈ P) (hz : z ∈ zc P) (hx : x ∈ P) :
    tc (y * z) x = tc y x := by
  rw [tc_mul_left, tc_zc_left hz hx, mul_one, conj_zc hz (tc_mem hy hx)]

theorem tc_mul_zc_right {P : Subgroup N} {y z x : N} (hy : y ∈ P) (hz : z ∈ zc P) (hx : x ∈ P) :
    tc y (x * z) = tc y x := by
  rw [tc_mul_right, tc_zc_right hz hy, one_mul, conj_zc hz (tc_mem hy hx)]

theorem tc_mul_left' (x x' y : N) : tc (x * x') y = tc x y * tc (tc x y) x' * tc x' y := by
  rw [tc_mul_left, conj_eq_mul_tc]

theorem cube_formula {x y c d e : N} (hc : c = tc y x) (hd : d = tc c x) (he : e = tc c y)
    (hdy : d * y = y * d) (hdc : d * c = c * d) (hey : e * y = y * e) (hec : e * c = c * e)
    (hde : d * e = e * d) (hc3 : c ^ 3 = 1) (he3 : e ^ 3 = 1) :
    (x * y) ^ 3 = x ^ 3 * y ^ 3 * d * e⁻¹ := by
  have R1 : y * x = x * y * c := by rw [hc]; unfold tc; group
  have R2 : c * x = x * c * d := by rw [hd]; unfold tc; group
  have R3 : c * y = y * c * e := by rw [he]; unfold tc; group
  have hc3' : c * c * c = 1 := by rw [← hc3, pow_succ, pow_two]
  have he3' : e * e * e = 1 := by rw [← he3, pow_succ, pow_two]
  have he' : e⁻¹ = e * e := inv_eq_of_mul_eq_one_right (by rw [← mul_assoc]; exact he3')
  have hede : e * e * d = d * (e * e) := by
    rw [mul_assoc, ← hde, ← mul_assoc, ← hde, mul_assoc]
  rw [pow_succ, pow_two, pow_succ x, pow_two x, pow_succ y, pow_two y, he']
  calc (x * y) * (x * y) * (x * y) = x * (y * x) * (y * x) * y := by group
    _ = x * (x * y * c) * (x * y * c) * y := by rw [R1]
    _ = x * x * y * (c * x) * y * c * y := by group
    _ = x * x * y * (x * c * d) * y * c * y := by rw [R2]
    _ = x * x * (y * x) * c * (d * y) * c * y := by group
    _ = x * x * (x * y * c) * c * (y * d) * c * y := by rw [R1, hdy]
    _ = x * x * x * y * c * (c * y) * (d * c) * y := by group
    _ = x * x * x * y * c * (y * c * e) * (c * d) * y := by rw [R3, hdc]
    _ = x * x * x * y * (c * y) * c * (e * c) * (d * y) := by group
    _ = x * x * x * y * (y * c * e) * c * (c * e) * (y * d) := by rw [R3, hec, hdy]
    _ = x * x * x * y * y * c * (e * c) * c * (e * y) * d := by group
    _ = x * x * x * y * y * c * (c * e) * c * (y * e) * d := by rw [hec, hey]
    _ = x * x * x * y * y * c * c * (e * c) * y * e * d := by group
    _ = x * x * x * y * y * c * c * (c * e) * y * e * d := by rw [hec]
    _ = x * x * x * y * y * (c * c * c) * (e * y) * e * d := by group
    _ = x * x * x * y * y * 1 * (y * e) * e * d := by rw [hc3', hey]
    _ = x * x * x * (y * y * y) * (e * e * d) := by group
    _ = x * x * x * (y * y * y) * d * (e * e) := by rw [hede]; group

section Hyp

variable {q : ℕ} {P R : Subgroup N} (h : ThompsonIConditions q P R)
include h

theorem commutator_le : ⁅P, P⁆ ≤ P := by
  have := h.normal
  exact Subgroup.commutator_le_left P P

theorem commutator_normal : (⁅P, P⁆ : Subgroup N).Normal := by
  have := h.normal
  exact Subgroup.commutator_normal P P

theorem zc_normal' : (zc P).Normal := by
  have := h.normal
  exact zc_normal P

theorem zc_le_commutator : zc P ≤ ⁅P, P⁆ := by
  have := commutator_normal h
  have e : zc P = ⁅(⁅P, P⁆ : Subgroup N), P⁆ := h.commutator_commutator.symm
  rw [e]
  exact Subgroup.commutator_le_left _ _

theorem tc_mem_zc {y x : N} (hy : y ∈ ⁅P, P⁆) (hx : x ∈ P) : tc y x ∈ zc P := by
  have := Subgroup.commutator_mem_commutator ((⁅P, P⁆ : Subgroup N).inv_mem hy) (P.inv_mem hx)
  rw [commutatorElement_def, inv_inv, inv_inv] at this
  have e : zc P = ⁅(⁅P, P⁆ : Subgroup N), P⁆ := h.commutator_commutator.symm
  rw [e]
  exact this

theorem commutator_comm {y y' : N} (hy : y ∈ ⁅P, P⁆) (hy' : y' ∈ ⁅P, P⁆) :
    y * y' = y' * y := by
  have := h.elementary_commutator
  have := mul_comm (⟨y, hy⟩ : (⁅P, P⁆ : Subgroup N)) ⟨y', hy'⟩
  exact congrArg Subtype.val this

theorem commutator_pow_three {y : N} (hy : y ∈ ⁅P, P⁆) : y ^ 3 = 1 := by
  have := h.elementary_commutator
  exact elemPow_eq_one_of_isElementaryAbelian (A := ⁅P, P⁆) y hy

theorem zc_pow_three {z : N} (hz : z ∈ zc P) : z ^ 3 = 1 :=
  commutator_pow_three h (zc_le_commutator h hz)

theorem card_zc : Nat.card (zc P) = q := by
  rw [zc, Subgroup.card_map_of_injective P.subtype_injective, h.card_center]

theorem tc_commutator {y x : N} (hy : y ∈ ⁅P, P⁆) (hx : x ∈ ⁅P, P⁆) : tc y x = 1 :=
  tc_eq_one_iff.2 (commutator_comm h hy hx)

theorem tc_mem_zc' {y x : N} (hx : x ∈ P) (hy : y ∈ ⁅P, P⁆) : tc x y ∈ zc P := by
  rw [← tc_inv]
  exact (zc P).inv_mem (tc_mem_zc h hy hx)

theorem tc_mul_left_of_mem {y y' x : N} (hy : y ∈ ⁅P, P⁆) (hy' : y' ∈ P) (hx : x ∈ P) :
    tc (y * y') x = tc y x * tc y' x := by
  rw [tc_mul_left', tc_zc_left (tc_mem_zc h hy hx) hy', mul_one]

theorem tc_mul_right_of_mem {x y y' : N} (hx : x ∈ ⁅P, P⁆) (hy : y ∈ P) (hy' : y' ∈ P) :
    tc x (y * y') = tc x y * tc x y' := by
  rw [tc_mul_right, conj_eq_mul_tc, tc_zc_left (tc_mem_zc h hx hy) hy', mul_one]
  exact zc_comm (tc_mem_zc h hx hy') (tc_mem (commutator_le h hx) hy)

theorem jacobi {x y z : N} (hx : x ∈ P) (hy : y ∈ P) (hz : z ∈ P) :
    tc (tc x y) z * tc (tc z x) y * tc (tc y z) x = 1 := by
  have key : ∀ {a b c : N}, a ∈ P → b ∈ P → c ∈ P → tc (tc a b) (a⁻¹ * c * a) = tc (tc a b) c := by
    intro a b c ha hb hc
    rw [conj_eq_mul_tc, tc_mul_right_of_mem h (tc_mem_commutator ha hb) hc (tc_mem hc ha),
      tc_commutator h (tc_mem_commutator ha hb) (tc_mem_commutator hc ha), mul_one]
  have := hall_witt x y z
  rwa [key hx hy hz, key hz hx hy, key hy hz hx] at this

theorem conj_mem_P {r x : N} (hx : x ∈ P) : r⁻¹ * x * r ∈ P := by
  have := h.normal.conj_mem x hx r⁻¹
  rwa [inv_inv] at this

theorem conj_mem_commutator {r x : N} (hx : x ∈ ⁅P, P⁆) : r⁻¹ * x * r ∈ ⁅P, P⁆ := by
  have := (commutator_normal h).conj_mem x hx r⁻¹
  rwa [inv_inv] at this

theorem conj_mem_zc {r x : N} (hx : x ∈ zc P) : r⁻¹ * x * r ∈ zc P := by
  have := (zc_normal' h).conj_mem x hx r⁻¹
  rwa [inv_inv] at this

theorem R_comm {r r' : N} (hr : r ∈ R) (hr' : r' ∈ R) : r * r' = r' * r := by
  have := h.isCyclic_R
  have : IsMulCommutative R := ⟨⟨fun a b => IsCyclic.commGroup.mul_comm a b⟩⟩
  exact congrArg Subtype.val (mul_comm (⟨r, hr⟩ : R) ⟨r', hr'⟩)

theorem fixed_P {r x : N} (hr : r ∈ R) (hr2 : r ^ 2 ≠ 1) (hx : x ∈ P) (hfix : r⁻¹ * x * r = x) :
    x = 1 := by
  have := h.centralizer_eq_bot r hr hr2
  have hmem : x ∈ P ⊓ Subgroup.centralizer {r} := ⟨hx, Subgroup.mem_centralizer_singleton_iff.2
    (calc x * r = r * (r⁻¹ * x * r) := by group
      _ = r * x := by rw [hfix])⟩
  rw [this] at hmem
  exact hmem

theorem invol_unique [Finite N] {J J' : N} (hJ : J ∈ R) (hJ2 : orderOf J = 2) (hJ' : J' ∈ R)
    (hJ'2 : orderOf J' = 2) : J = J' := by
  classical
  have := h.isCyclic_R
  let _ : Fintype R := Fintype.ofFinite R
  have h2 : 2 ∣ Fintype.card R := by
    rw [← hJ2, ← Subgroup.orderOf_mk J hJ]
    exact orderOf_dvd_card
  have hcard := IsCyclic.card_orderOf_eq_totient (α := R) h2
  rw [Nat.totient_two] at hcard
  have hJm : (⟨J, hJ⟩ : R) ∈ ({a | orderOf a = 2} : Finset R) := by
    simp [Subgroup.orderOf_mk, hJ2]
  have hJ'm : (⟨J', hJ'⟩ : R) ∈ ({a | orderOf a = 2} : Finset R) := by
    simp [Subgroup.orderOf_mk, hJ'2]
  have := Finset.card_le_one.1 hcard.le _ hJm _ hJ'm
  exact congrArg Subtype.val this

theorem exists_invol [Finite N] (hq : Odd q) (hq1 : 1 < q) : ∃ J ∈ R, orderOf J = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card R := by
    rw [h.card_R]
    obtain ⟨k, hk⟩ := hq
    exact ⟨k, by omega⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := R) 2 h2
  exact ⟨x.1, x.2, by rwa [Subgroup.orderOf_coe]⟩

end Hyp

section Invol

variable {q : ℕ} {P R : Subgroup N} (h : ThompsonIConditions q P R) {J : N} (hJ : J ∈ R)
  (hJ2 : orderOf J = 2)
include h hJ hJ2

omit h hJ in
theorem invol_mul_self : J * J = 1 := by
  rw [← pow_two, ← hJ2, pow_orderOf_eq_one]

omit h hJ in
theorem invol_inv : J⁻¹ = J := inv_eq_of_mul_eq_one_right (invol_mul_self hJ2)

theorem commutator_eq_sup : ⁅P, P⁆ = (P ⊓ Subgroup.centralizer {J}) ⊔ zc P :=
  (h.commutator_eq_prod J hJ hJ2).1

theorem P0_inf_zc : (P ⊓ Subgroup.centralizer {J}) ⊓ zc P = ⊥ :=
  (h.commutator_eq_prod J hJ hJ2).2

theorem P0_le : P ⊓ Subgroup.centralizer {J} ≤ ⁅P, P⁆ := by
  rw [commutator_eq_sup h hJ hJ2]
  exact le_sup_left

omit h hJ hJ2 in
theorem mem_P0 {c : N} : c ∈ P ⊓ Subgroup.centralizer {J} ↔ c ∈ P ∧ J⁻¹ * c * J = c := by
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  refine and_congr_right fun _ => ⟨fun hc => by rw [mul_assoc, hc]; group, fun hc => ?_⟩
  calc c * J = J * (J⁻¹ * c * J) := by group
    _ = J * c := by rw [hc]

theorem invol_inv_zc {z : N} (hz : z ∈ zc P) : J⁻¹ * z * J = z⁻¹ := by
  have hz' : J⁻¹ * z * J ∈ zc P := conj_mem_zc h hz
  have hw : z * (J⁻¹ * z * J) ∈ zc P := (zc P).mul_mem hz hz'
  have hJJ := invol_mul_self hJ2
  have hfix : J⁻¹ * (z * (J⁻¹ * z * J)) * J = z * (J⁻¹ * z * J) := by
    calc J⁻¹ * (z * (J⁻¹ * z * J)) * J = (J⁻¹ * z * J) * ((J * J)⁻¹ * z * (J * J)) := by group
      _ = (J⁻¹ * z * J) * z := by rw [hJJ]; group
      _ = z * (J⁻¹ * z * J) := zc_comm hz' (zc_le P hz)
  have h1 : z * (J⁻¹ * z * J) ∈ (P ⊓ Subgroup.centralizer {J}) ⊓ zc P :=
    ⟨(mem_P0).2 ⟨zc_le P hw, hfix⟩, hw⟩
  rw [P0_inf_zc h hJ hJ2, Subgroup.mem_bot] at h1
  exact eq_inv_of_mul_eq_one_right h1

theorem decomp {y : N} (hy : y ∈ ⁅P, P⁆) :
    ∃ c ∈ P ⊓ Subgroup.centralizer {J}, ∃ z ∈ zc P, c * z = y := by
  have := zc_normal' h
  rw [commutator_eq_sup h hJ hJ2] at hy
  exact Subgroup.mem_sup_of_normal_right.1 hy

theorem mem_zc_of_inverted {y : N} (hy : y ∈ ⁅P, P⁆) (hinv : J⁻¹ * y * J = y⁻¹) : y ∈ zc P := by
  obtain ⟨c, hc, z, hz, rfl⟩ := decomp h hJ hJ2 hy
  have hcJ := (mem_P0.1 hc).2
  have e1 : J⁻¹ * (c * z) * J = c * z⁻¹ := by
    rw [show J⁻¹ * (c * z) * J = (J⁻¹ * c * J) * (J⁻¹ * z * J) by group, hcJ,
      invol_inv_zc h hJ hJ2 hz]
  rw [e1] at hinv
  have hcP : c ∈ P := commutator_le h (P0_le h hJ hJ2 hc)
  have hc2 : c * c = 1 := by
    have h1 : c⁻¹ * z⁻¹ = z⁻¹ * c⁻¹ := by
      rw [← mul_inv_rev, ← mul_inv_rev, zc_comm hz hcP]
    have h2 : c * z⁻¹ = c⁻¹ * z⁻¹ := by rw [hinv, mul_inv_rev, h1]
    have h3 : c = c⁻¹ := mul_right_cancel h2
    calc c * c = c * c⁻¹ := by rw [← h3]
      _ = 1 := mul_inv_cancel c
  have hc3 := commutator_pow_three h (P0_le h hJ hJ2 hc)
  have hc1 : c = 1 := by
    calc c = c ^ 3 * (c * c)⁻¹ := by group
      _ = 1 := by rw [hc3, hc2]; group
  rw [hc1, one_mul]
  exact hz

theorem card_P0 [Finite N] : Nat.card (P ⊓ Subgroup.centralizer {J} : Subgroup N) = q := by
  have hq0 : 0 < q := by rw [← card_zc h]; exact Nat.card_pos
  let f : (P ⊓ Subgroup.centralizer {J} : Subgroup N) × zc P → (⁅P, P⁆ : Subgroup N) :=
    fun p => ⟨p.1.1 * p.2.1, (⁅P, P⁆ : Subgroup N).mul_mem (P0_le h hJ hJ2 p.1.2)
      (zc_le_commutator h p.2.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨⟨c, hc⟩, ⟨z, hz⟩⟩ ⟨⟨c', hc'⟩, ⟨z', hz'⟩⟩ he
      have he' : c * z = c' * z' := congrArg Subtype.val he
      have hw : c'⁻¹ * c ∈ (P ⊓ Subgroup.centralizer {J}) ⊓ zc P := by
        refine ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hc') hc, ?_⟩
        have : c'⁻¹ * c = z' * z⁻¹ := by
          calc c'⁻¹ * c = c'⁻¹ * (c * z) * z⁻¹ := by group
            _ = z' * z⁻¹ := by rw [he']; group
        rw [this]
        exact (zc P).mul_mem hz' ((zc P).inv_mem hz)
      rw [P0_inf_zc h hJ hJ2, Subgroup.mem_bot] at hw
      have hcc : c = c' := by
        calc c = c' * (c'⁻¹ * c) := by group
          _ = c' := by rw [hw, mul_one]
      subst hcc
      have hzz : z = z' := mul_left_cancel he'
      subst hzz
      rfl
    · rintro ⟨y, hy⟩
      obtain ⟨c, hc, z, hz, rfl⟩ := decomp h hJ hJ2 hy
      exact ⟨(⟨c, hc⟩, ⟨z, hz⟩), rfl⟩
  have := Nat.card_congr (Equiv.ofBijective f hf)
  rw [Nat.card_prod, card_zc h, h.card_commutator] at this
  exact Nat.eq_of_mul_eq_mul_right hq0 (by rw [this]; ring)

omit h hJ in
theorem invol_conj_inverted (p : N) :
    J⁻¹ * (p⁻¹ * (J⁻¹ * p * J)) * J = (p⁻¹ * (J⁻¹ * p * J))⁻¹ := by
  have hJ' := invol_inv hJ2
  have hJJ := invol_mul_self hJ2
  calc J⁻¹ * (p⁻¹ * (J⁻¹ * p * J)) * J = J⁻¹ * p⁻¹ * J⁻¹ * p * (J * J) := by group
    _ = J⁻¹ * p⁻¹ * J⁻¹ * p := by rw [hJJ, mul_one]
    _ = J⁻¹ * p⁻¹ * J * p := by rw [hJ']
    _ = (p⁻¹ * (J⁻¹ * p * J))⁻¹ := by group

theorem cube_mem_zc {x : N} (hinv : J⁻¹ * x * J = x⁻¹) (hx3 : x ^ 3 ∈ ⁅P, P⁆) :
    x ^ 3 ∈ zc P := by
  refine mem_zc_of_inverted h hJ hJ2 hx3 ?_
  have e : J⁻¹ * x ^ 3 * J = (J⁻¹ * x * J) ^ 3 := by
    simp only [pow_succ, pow_zero, one_mul]
    group
  rw [e, hinv, inv_pow]

theorem fixed_zc [Finite N] {r z : N} (hr : r ∈ R) (hr1 : r ≠ 1) (hz : z ∈ zc P)
    (hfix : r⁻¹ * z * r = z) : z = 1 := by
  by_cases hr2 : r ^ 2 = 1
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hr2' : orderOf r = 2 := orderOf_eq_prime hr2 hr1
    have hrJ := invol_unique h hr hr2' hJ hJ2
    subst hrJ
    rw [invol_inv_zc h hJ hJ2 hz] at hfix
    have hz3 := zc_pow_three h hz
    have hzz : z * z = 1 := by
      nth_rewrite 1 [← hfix]
      exact inv_mul_cancel z
    calc z = z ^ 3 * (z * z)⁻¹ := by group
      _ = 1 := by rw [hz3, hzz]; group
  · exact fixed_P h hr hr2 (zc_le P hz) hfix

theorem fixed_L1 [Finite N] {r x : N} (hr : r ∈ R) (hr1 : r ≠ 1) (hx : x ∈ P)
    (hfix : x⁻¹ * (r⁻¹ * x * r) ∈ ⁅P, P⁆) : x ∈ ⁅P, P⁆ := by
  by_cases hr2 : r ^ 2 = 1
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hr2' : orderOf r = 2 := orderOf_eq_prime hr2 hr1
    have hrJ := invol_unique h hr hr2' hJ hJ2
    subst hrJ
    set c := x⁻¹ * (r⁻¹ * x * r) with hc
    have hcz : c ∈ zc P := mem_zc_of_inverted h hJ hJ2 hfix (invol_conj_inverted hJ2 x)
    have hcP := zc_le P hcz
    have hxc : r⁻¹ * x * r = x * c := by rw [hc]; group
    have hc3 := zc_pow_three h hcz
    have hmem : x * (c * c) ∈ P ⊓ Subgroup.centralizer {r} := by
      refine mem_P0.2 ⟨P.mul_mem hx (P.mul_mem hcP hcP), ?_⟩
      have e : r⁻¹ * (x * (c * c)) * r = (r⁻¹ * x * r) * (r⁻¹ * c * r) * (r⁻¹ * c * r) := by
        group
      rw [e, hxc, invol_inv_zc h hJ hJ2 hcz]
      calc x * c * c⁻¹ * c⁻¹ = x * (c * c) * (c ^ 3)⁻¹ := by group
        _ = x * (c * c) := by rw [hc3, inv_one, mul_one]
    have := P0_le h hJ hJ2 hmem
    have hcc : c * c ∈ ⁅P, P⁆ :=
      (⁅P, P⁆ : Subgroup N).mul_mem (zc_le_commutator h hcz) (zc_le_commutator h hcz)
    have := (⁅P, P⁆ : Subgroup N).mul_mem this ((⁅P, P⁆ : Subgroup N).inv_mem hcc)
    rwa [mul_inv_cancel_right] at this
  ·
    have hinj : ∀ p p' : N, p ∈ P → p' ∈ P → p⁻¹ * (r⁻¹ * p * r) = p'⁻¹ * (r⁻¹ * p' * r) →
        p = p' := by
      intro p p' hp hp' he
      have hw : r⁻¹ * (p' * p⁻¹) * r = p' * p⁻¹ := by
        have e1 : r⁻¹ * p' * r = p' * p⁻¹ * (r⁻¹ * p * r) := by
          calc r⁻¹ * p' * r = p' * (p'⁻¹ * (r⁻¹ * p' * r)) := by group
            _ = p' * (p⁻¹ * (r⁻¹ * p * r)) := by rw [he]
            _ = p' * p⁻¹ * (r⁻¹ * p * r) := by group
        calc r⁻¹ * (p' * p⁻¹) * r = (r⁻¹ * p' * r) * (r⁻¹ * p * r)⁻¹ := by group
          _ = p' * p⁻¹ := by rw [e1]; group
      have := fixed_P h hr hr2 (P.mul_mem hp' (P.inv_mem hp)) hw
      calc p = (p' * p⁻¹)⁻¹ * p' := by group
        _ = p' := by rw [this, inv_one, one_mul]
    let f : (⁅P, P⁆ : Subgroup N) → (⁅P, P⁆ : Subgroup N) := fun p =>
      ⟨p.1⁻¹ * (r⁻¹ * p.1 * r), (⁅P, P⁆ : Subgroup N).mul_mem
        ((⁅P, P⁆ : Subgroup N).inv_mem p.2) (conj_mem_commutator h p.2)⟩
    have hf : Function.Injective f := fun p p' he =>
      Subtype.ext (hinj p p' (commutator_le h p.2) (commutator_le h p'.2) (congrArg Subtype.val he))
    obtain ⟨p, hp⟩ := (Finite.injective_iff_surjective.1 hf) ⟨_, hfix⟩
    have := hinj p x (commutator_le h p.2) hx (congrArg Subtype.val hp)
    rw [← this]
    exact p.2

end Invol

end CFSG.Walter.Ree.Thompson1
