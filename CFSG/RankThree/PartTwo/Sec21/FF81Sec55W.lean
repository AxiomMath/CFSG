module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36W

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

namespace S55

open S36 (hypF hypU hypA dot)

variable {G : Type} [Group G] [Finite G]

structure Coord (ε : (Fin 3 → ZMod 3) → G) (A : Subgroup G) : Prop where
  add : ∀ x y, ε (x + y) = ε x * ε y
  inj : Function.Injective ε
  mem : ∀ x, ε x ∈ A
  surj : ∀ y ∈ A, ∃ x, ε x = y

theorem three_nsmul_eq_zero : ∀ x : Fin 3 → ZMod 3, 3 • x = 0 := by decide

section Coord

variable {ε : (Fin 3 → ZMod 3) → G} {A : Subgroup G} (h : Coord ε A)
include h

theorem Coord.zero : ε 0 = 1 :=
  mul_left_cancel (a := ε 0) (by rw [← h.add, add_zero, mul_one])

theorem Coord.neg (x : Fin 3 → ZMod 3) : ε (-x) = (ε x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← h.add, neg_add_cancel, h.zero])

theorem Coord.nsmul (n : ℕ) (x : Fin 3 → ZMod 3) : ε (n • x) = ε x ^ n := by
  induction n with
  | zero => rw [zero_smul, pow_zero, h.zero]
  | succ n ih => rw [succ_nsmul, h.add, ih, pow_succ]

theorem Coord.smul (c : ZMod 3) (x : Fin 3 → ZMod 3) : ε (c • x) = ε x ^ c.val := by
  rw [← h.nsmul, ← Nat.cast_smul_eq_nsmul (ZMod 3), ZMod.natCast_zmod_val]

theorem Coord.eq_one_iff {x : Fin 3 → ZMod 3} : ε x = 1 ↔ x = 0 :=
  ⟨fun hx => h.inj (hx.trans h.zero.symm), fun hx => by rw [hx, h.zero]⟩

theorem Coord.cube (x : Fin 3 → ZMod 3) : ε x ^ 3 = 1 := by
  rw [← h.nsmul, three_nsmul_eq_zero, h.zero]

theorem Coord.orderOf {x : Fin 3 → ZMod 3} (hx : x ≠ 0) : orderOf (ε x) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact orderOf_eq_prime (h.cube x) (fun h1 => hx (h.eq_one_iff.mp h1))

theorem Coord.mem_zpowers {x z : Fin 3 → ZMod 3} :
    ε z ∈ Subgroup.zpowers (ε x) ↔ ∃ c : ZMod 3, z = c • x := by
  constructor
  · intro hz
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hz
    obtain ⟨n, hn⟩ := hz
    rw [← h.nsmul] at hn
    refine ⟨n, (h.inj hn).symm.trans ?_⟩
    rw [Nat.cast_smul_eq_nsmul]
  · rintro ⟨c, rfl⟩
    rw [h.smul]
    exact Subgroup.npow_mem_zpowers _ _

theorem Coord.card : Nat.card A = 27 := by
  classical
  have e : (Fin 3 → ZMod 3) ≃ A :=
    Equiv.ofBijective (fun x => ⟨ε x, h.mem x⟩)
      ⟨fun x y hxy => h.inj (congrArg Subtype.val hxy), fun y => by
        obtain ⟨x, hx⟩ := h.surj y.1 y.2
        exact ⟨x, Subtype.ext hx⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  rfl

end Coord

def hyp (ε : (Fin 3 → ZMod 3) → G) (i : Fin 13) : Subgroup G :=
  Subgroup.closure {ε (hypU i), ε (hypA i)}

def lv (i : Fin 13) : Fin 4 → (Fin 3 → ZMod 3) :=
  ![hypU i, hypA i, hypU i + hypA i, hypU i + (2 : ZMod 3) • hypA i]

theorem lv_ne_zero : ∀ i : Fin 13, ∀ j : Fin 4, lv i j ≠ 0 := by decide

theorem lv_dot : ∀ i : Fin 13, ∀ j : Fin 4, dot (hypF i) (lv i j) = 0 := by decide

set_option maxRecDepth 100000 in
theorem count_lines : ∀ i : Fin 13, ∀ z0 z1 z2 : ZMod 3, dot (hypF i) ![z0, z1, z2] = 0 →
    (∑ j : Fin 4, if ∃ c : ZMod 3, ![z0, z1, z2] = c • lv i j then 1 else 0) =
      (if ![z0, z1, z2] = 0 then 3 else 0) + 1 := by
  decide +kernel

section Hyp

variable {ε : (Fin 3 → ZMod 3) → G} {A : Subgroup G} (h : Coord ε A)
include h

theorem hyp_le (i : Fin 13) : hyp ε i ≤ A := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y (rfl | rfl) <;> exact h.mem _

theorem Coord.mem_hyp (i : Fin 13) (z : Fin 3 → ZMod 3) :
    ε z ∈ hyp ε i ↔ dot (hypF i) z = 0 := by
  constructor
  · intro hz
    suffices key : ∀ y ∈ hyp ε i, ∃ w, ε w = y ∧ dot (hypF i) w = 0 by
      obtain ⟨w, hw, hw0⟩ := key _ hz
      rwa [← h.inj hw]
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with rfl | rfl
        · exact ⟨_, rfl, (S36.hypUA_dot i).1⟩
        · exact ⟨_, rfl, (S36.hypUA_dot i).2⟩
    | one => exact ⟨0, h.zero, by simp [dot]⟩
    | mul _ _ _ _ ih₁ ih₂ =>
        obtain ⟨x, rfl, hx⟩ := ih₁
        obtain ⟨y, rfl, hy⟩ := ih₂
        exact ⟨x + y, h.add x y, by rw [S36.dot_add, hx, hy, add_zero]⟩
    | inv _ _ ih =>
        obtain ⟨x, rfl, hx⟩ := ih
        exact ⟨-x, h.neg x, by rw [S36.dot_neg, hx, neg_zero]⟩
  · intro hz
    rw [S36.vec3_eta z] at hz ⊢
    obtain ⟨c, d, hcd⟩ := S36.span_of_dot i _ _ _ hz
    rw [hcd, h.add, h.smul, h.smul]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem Coord.exists_of_mem_hyp {i : Fin 13} {y : G} (hy : y ∈ hyp ε i) :
    ∃ z, ε z = y ∧ dot (hypF i) z = 0 := by
  obtain ⟨z, rfl⟩ := h.surj y (hyp_le h i hy)
  exact ⟨z, rfl, (h.mem_hyp i z).1 hy⟩

theorem Coord.card_hyp (i : Fin 13) : Nat.card (hyp ε i) = 9 := by
  classical
  have e : {z : Fin 3 → ZMod 3 // dot (hypF i) z = 0} ≃ hyp ε i :=
    Equiv.ofBijective (fun z => ⟨ε z, (h.mem_hyp i z).2 z.2⟩)
      ⟨fun z w hzw => Subtype.ext (h.inj (congrArg Subtype.val hzw)), fun y => by
        obtain ⟨z, hz, hz0⟩ := h.exists_of_mem_hyp y.2
        exact ⟨⟨z, hz0⟩, Subtype.ext hz⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact S36.card_ker' i

theorem Coord.cenS_hyp {i : Fin 13} {p q : Fin 3 → ZMod 3} (hp : dot (hypF i) p = 0)
    (hq : dot (hypF i) q = 0)
    (hspan : ∀ z, dot (hypF i) z = 0 → ∃ c d : ZMod 3, z = c • p + d • q) {y : G} :
    y ∈ CenS (hyp ε i) ↔ y * ε p = ε p * y ∧ y * ε q = ε q * y := by
  constructor
  · intro hy
    exact ⟨(Subgroup.mem_centralizer_iff.mp hy _ ((h.mem_hyp i p).2 hp)).symm,
      (Subgroup.mem_centralizer_iff.mp hy _ ((h.mem_hyp i q).2 hq)).symm⟩
  · rintro ⟨h1, h2⟩
    refine Subgroup.mem_centralizer_iff.mpr fun a ha => ?_
    obtain ⟨z, rfl, hz⟩ := h.exists_of_mem_hyp ha
    obtain ⟨c, d, rfl⟩ := hspan z hz
    rw [h.add, h.smul, h.smul]
    exact ((((Commute.pow_left h1.symm _)).mul_left (Commute.pow_left h2.symm _))).eq

end Hyp

section Wiel

variable {ε : (Fin 3 → ZMod 3) → G} {A : Subgroup G} (h : Coord ε A)
include h

open _root_.Classical in
theorem card_mul_pow_twelve {S : Subgroup G} (hS : A ≤ Nor S) (hcop : Nat.Coprime (Nat.card S) 3)
    (hsolv : Group.IsSolvable S) :
    Nat.card S * Nat.card ↥(S ⊓ CenS A) ^ 12 = ∏ i : Fin 13, Nat.card ↥(S ⊓ CenS (hyp ε i)) := by
  let H : Fin 13 ⊕ Fin 2 → Subgroup G := Sum.elim (hyp ε) ![⊥, A]
  let m : Fin 13 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 1) ![0, 0]
  let n : Fin 13 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 0) ![9, 4]
  have hc27 : Nat.card A = 27 := h.card
  have hcop' : Nat.Coprime (Nat.card S) (Nat.card A) := by
    rw [hc27, show (27 : ℕ) = 3 ^ 3 by norm_num]; exact hcop.pow_right 3
  have hH : ∀ i, H i ≤ A := by
    rintro (i | i)
    · exact hyp_le h i
    · fin_cases i
      · exact bot_le
      · exact le_rfl
  have hcoeff : ∀ g ∈ A, (∑ i, if g ∈ H i then m i else 0) =
      ∑ i, if g ∈ H i then n i else 0 := by
    intro g hg
    obtain ⟨x, rfl⟩ := h.surj g hg
    simp only [Fintype.sum_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Subgroup.mem_bot,
      h.mem_hyp, h.eq_one_iff, hg, if_true, ite_self, Finset.sum_const_zero, add_zero, zero_add]
    rw [S36.vec3_eta x]
    exact S36.count1 _ _ _
  have h' := S36.wielandt_conj hS hcop' hsolv H hH m n hcoeff
  simp only [Fintype.prod_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Subgroup.card_bot, S36.cenS_bot,
    inf_top_eq, h.card_hyp, hc27, zero_mul, pow_zero, one_mul, mul_one,
    Finset.prod_const_one] at h'
  apply Nat.pow_left_injective (show 9 ≠ 0 by norm_num)
  simp only
  rw [← Finset.prod_pow, h']
  ring

open _root_.Classical in
theorem card_cen_mul_pow_three {S : Subgroup G} (hS : A ≤ Nor S)
    (hcop : Nat.Coprime (Nat.card S) 3) (hsolv : Group.IsSolvable S) {x : Fin 3 → ZMod 3}
    (hx : x ≠ 0) :
    Nat.card ↥(S ⊓ Cen (ε x)) * Nat.card ↥(S ⊓ CenS A) ^ 3 =
      ∏ i ∈ Finset.univ.filter (fun i => dot (hypF i) x = 0),
        Nat.card ↥(S ⊓ CenS (hyp ε i)) := by
  let H : Fin 13 ⊕ Fin 2 → Subgroup G := Sum.elim (hyp ε) ![Subgroup.zpowers (ε x), A]
  let m : Fin 13 ⊕ Fin 2 → ℕ := Sum.elim (fun i => if dot (hypF i) x = 0 then 1 else 0) ![0, 0]
  let n : Fin 13 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 0) ![3, 1]
  have hc27 : Nat.card A = 27 := h.card
  have hcop' : Nat.Coprime (Nat.card S) (Nat.card A) := by
    rw [hc27, show (27 : ℕ) = 3 ^ 3 by norm_num]; exact hcop.pow_right 3
  have hH : ∀ i, H i ≤ A := by
    rintro (i | i)
    · exact hyp_le h i
    · fin_cases i
      · exact Subgroup.zpowers_le.mpr (h.mem x)
      · exact le_rfl
  have hcoeff : ∀ g ∈ A, (∑ i, if g ∈ H i then m i else 0) =
      ∑ i, if g ∈ H i then n i else 0 := by
    intro g hg
    obtain ⟨z, rfl⟩ := h.surj g hg
    simp only [Fintype.sum_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, h.mem_zpowers,
      h.mem_hyp, hg, if_true, ite_self, Finset.sum_const_zero, add_zero, zero_add]
    rw [S36.vec3_eta x, S36.vec3_eta z]
    rw [S36.vec3_eta x] at hx
    exact S36.count2 _ _ _ _ _ _ hx
  have h' := S36.wielandt_conj hS hcop' hsolv H hH m n hcoeff
  simp only [Fintype.prod_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, S36.cenS_zpowers,
    h.card_hyp, hc27, Nat.card_zpowers, h.orderOf hx, zero_mul, pow_zero, one_mul,
    mul_one, Finset.prod_const_one] at h'
  apply Nat.pow_left_injective (show 9 ≠ 0 by norm_num)
  simp only
  rw [← Finset.prod_pow, Finset.prod_filter]
  have e : ∀ i : Fin 13, (if dot (hypF i) x = 0 then Nat.card ↥(S ⊓ CenS (hyp ε i)) ^ 9
      else 1) =
      Nat.card ↥(S ⊓ CenS (hyp ε i)) ^ ((if dot (hypF i) x = 0 then 1 else 0) * 9) := by
    intro i; split_ifs <;> simp
  rw [Finset.prod_congr rfl fun i _ => e i, h']
  ring

open _root_.Classical in
theorem card_mul_pow_three (i : Fin 13) {S : Subgroup G} (hS : hyp ε i ≤ Nor S)
    (hcop : Nat.Coprime (Nat.card S) 3) (hsolv : Group.IsSolvable S) :
    Nat.card S * Nat.card ↥(S ⊓ CenS (hyp ε i)) ^ 3 =
      ∏ j : Fin 4, Nat.card ↥(S ⊓ Cen (ε (lv i j))) := by
  let H : Fin 4 ⊕ Fin 2 → Subgroup G :=
    Sum.elim (fun j => Subgroup.zpowers (ε (lv i j))) ![⊥, hyp ε i]
  let m : Fin 4 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 1) ![0, 0]
  let n : Fin 4 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 0) ![3, 1]
  have hc9 : Nat.card (hyp ε i) = 9 := h.card_hyp i
  have hcop' : Nat.Coprime (Nat.card S) (Nat.card (hyp ε i)) := by
    rw [hc9, show (9 : ℕ) = 3 ^ 2 by norm_num]; exact hcop.pow_right 2
  have hH : ∀ k, H k ≤ hyp ε i := by
    rintro (j | j)
    · exact Subgroup.zpowers_le.mpr ((h.mem_hyp i _).2 (lv_dot i j))
    · fin_cases j
      · exact bot_le
      · exact le_rfl
  have hcoeff : ∀ g ∈ hyp ε i, (∑ k, if g ∈ H k then m k else 0) =
      ∑ k, if g ∈ H k then n k else 0 := by
    intro g hg
    obtain ⟨z, rfl, hz⟩ := h.exists_of_mem_hyp hg
    simp only [Fintype.sum_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Subgroup.mem_bot,
      h.mem_zpowers, h.eq_one_iff, hg, if_true, ite_self, Finset.sum_const_zero, add_zero,
      zero_add]
    rw [S36.vec3_eta z]
    rw [S36.vec3_eta z] at hz
    exact count_lines i _ _ _ hz
  have h' := S36.wielandt_conj hS hcop' hsolv H hH m n hcoeff
  simp only [Fintype.prod_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Subgroup.card_bot, S36.cenS_bot,
    S36.cenS_zpowers, inf_top_eq, hc9, Nat.card_zpowers, h.orderOf (lv_ne_zero i _), zero_mul,
    pow_zero, one_mul, mul_one, Finset.prod_const_one] at h'
  apply Nat.pow_left_injective (show 3 ≠ 0 by norm_num)
  simp only
  rw [← Finset.prod_pow, h']
  ring

theorem eq_of_lines (i : Fin 13) {S N : Subgroup G} (hNS : N ≤ S) (hS : hyp ε i ≤ Nor S)
    (hN : hyp ε i ≤ Nor N) (hcop : Nat.Coprime (Nat.card S) 3) (hsolv : Group.IsSolvable S)
    (hl : ∀ j, S ⊓ Cen (ε (lv i j)) ≤ N) : N = S := by
  have hcopN : Nat.Coprime (Nat.card N) 3 :=
    Nat.Coprime.coprime_dvd_left (Subgroup.card_dvd_of_le hNS) hcop
  have hsolvN : Group.IsSolvable N :=
    solvable_of_solvable_injective (f := Subgroup.inclusion hNS) (Subgroup.inclusion_injective hNS)
  have hline : ∀ j, N ⊓ Cen (ε (lv i j)) = S ⊓ Cen (ε (lv i j)) := fun j =>
    le_antisymm (inf_le_inf_right _ hNS) (le_inf (hl j) inf_le_right)
  have hE : N ⊓ CenS (hyp ε i) = S ⊓ CenS (hyp ε i) := by
    refine le_antisymm (inf_le_inf_right _ hNS) (le_inf ?_ inf_le_right)
    refine le_trans ?_ (hl 0)
    refine inf_le_inf_left _ fun y hy => ?_
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hy _ ((h.mem_hyp i _).2 (lv_dot i 0))).symm
  have h1 := card_mul_pow_three h i hN hcopN hsolvN
  have h2 := card_mul_pow_three h i hS hcop hsolv
  simp only [hline, hE] at h1
  rw [← h2] at h1
  have hpos : 0 < Nat.card ↥(S ⊓ CenS (hyp ε i)) ^ 3 := pow_pos Nat.card_pos _
  have hcard : Nat.card N = Nat.card S := Nat.eq_of_mul_eq_mul_right hpos h1
  exact Subgroup.eq_of_le_of_card_ge hNS hcard.ge

end Wiel

end S55

end CFSG.RankThree.PartTwo.Sec21.FF81
