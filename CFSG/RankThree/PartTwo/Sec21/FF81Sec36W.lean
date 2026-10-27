module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Geom
public import CFSG.LocalAnalysis.AGLEmbeddingD2.E9TwoGroup

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

namespace S36

variable {G : Type} [Group G] [Finite G]

open CFSG.AGLEmbeddingD2.E9TwoGroup CFSG.SignalizerFunctor.Helpers Classical in
theorem wielandt_conj {S A : Subgroup G} (hAS : A ≤ Nor S)
    (hcop : Nat.Coprime (Nat.card S) (Nat.card A)) (hsolv : Group.IsSolvable S) {ι : Type}
    [Fintype ι] (H : ι → Subgroup G) (hH : ∀ i, H i ≤ A) (m n : ι → ℕ)
    (hcoeff : ∀ g ∈ A, (∑ i, if g ∈ H i then m i else 0) = ∑ i, if g ∈ H i then n i else 0) :
    ∏ i, Nat.card ↥(S ⊓ CenS (H i)) ^ (m i * Nat.card (H i)) =
      ∏ i, Nat.card ↥(S ⊓ CenS (H i)) ^ (n i * Nat.card (H i)) := by
  let := conjugationAction A S hAS
  set B' : ι → Subgroup A := fun i => (H i).subgroupOf A with hB'
  have hmap : ∀ i, (B' i).map A.subtype = H i := fun i => by
    rw [hB', Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.mpr (hH i)
  have hcard : ∀ i, Nat.card (B' i) = Nat.card (H i) := fun i => by
    rw [← hmap i, Subgroup.card_map_of_injective A.subtype_injective]
  have hc : ∀ g : A, (∑ i, if g ∈ B' i then m i else 0) = ∑ i, if g ∈ B' i then n i else 0 := by
    intro g
    have h := hcoeff g g.2
    simpa only [hB', Subgroup.mem_subgroupOf] using h
  have h := CFSG.Wielandt.fixedPointSubgroup_product_card_eq_of_coeff_sum_eq hcop hsolv B' m n hc
  change (∏ i, fixCard (J := S) (B' i) ^ (m i * Nat.card (B' i))) =
    ∏ i, fixCard (J := S) (B' i) ^ (n i * Nat.card (B' i)) at h
  simp only [fixCard_conj_eq S A hAS, hmap, hcard] at h
  exact h

section Coord

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem ε3_eq (b₀ : G) (x : Fin 3 → ZMod 3) : ε3 b₁ b₂ b₃ x = ε4 b₀ b₁ b₂ b₃ (emb x) :=
  (ε4_emb b₀ _ _ _ x).symm

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.ε3_add (hB : FF81Basis b L B b₁ b₂ b₃) (x y : Fin 3 → ZMod 3) :
    ε3 b₁ b₂ b₃ (x + y) = ε3 b₁ b₂ b₃ x * ε3 b₁ b₂ b₃ y := by
  rw [ε3_eq b, ε3_eq b, ε3_eq b, emb_add, ε4_add hB.mono.1 hB.mono.2.1]

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.ε3_smul (hB : FF81Basis b L B b₁ b₂ b₃) (c : ZMod 3) (x : Fin 3 → ZMod 3) :
    ε3 b₁ b₂ b₃ (c • x) = ε3 b₁ b₂ b₃ x ^ c.val := by
  rw [ε3_eq b, ε3_eq b, emb_smul, ε4_smul hB.mono.1 hB.mono.2.1]

theorem ε3_zero : ε3 b₁ b₂ b₃ 0 = 1 := by simp [ε3]

theorem val_one3 : (1 : ZMod 3).val = 1 := rfl

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.ε3_inj (hB : FF81Basis b L B b₁ b₂ b₃) {x y : Fin 3 → ZMod 3}
    (h : ε3 b₁ b₂ b₃ x = ε3 b₁ b₂ b₃ y) : x = y := by
  rw [ε3_eq b, ε3_eq b] at h
  exact emb_inj (ε4_inj hB.mono.1 hB.mono.2.1 h)

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.ε3_eq_one (hB : FF81Basis b L B b₁ b₂ b₃) {x : Fin 3 → ZMod 3} :
    ε3 b₁ b₂ b₃ x = 1 ↔ x = 0 := by
  refine ⟨fun h => hB.ε3_inj (h.trans ε3_zero.symm), fun h => by rw [h, ε3_zero]⟩

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.ε3_neg (hB : FF81Basis b L B b₁ b₂ b₃) (x : Fin 3 → ZMod 3) :
    ε3 b₁ b₂ b₃ (-x) = (ε3 b₁ b₂ b₃ x)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← hB.ε3_add, neg_add_cancel, ε3_zero])

theorem ε3_mem (x : Fin 3 → ZMod 3) : ε3 b₁ b₂ b₃ x ∈ Subgroup.closure {b₁, b₂, b₃} := by
  have h : ∀ y ∈ ({b₁, b₂, b₃} : Set G), y ∈ Subgroup.closure ({b₁, b₂, b₃} : Set G) :=
    fun y hy => Subgroup.subset_closure hy
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ (h _ (by simp)) _)
    (Subgroup.pow_mem _ (h _ (by simp)) _)) (Subgroup.pow_mem _ (h _ (by simp)) _)

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.exists_ε3 (hB : FF81Basis b L B b₁ b₂ b₃) {y : G}
    (hy : y ∈ Subgroup.closure {b₁, b₂, b₃}) : ∃ x, ε3 b₁ b₂ b₃ x = y := by
  induction hy using Subgroup.closure_induction with
  | mem z hz =>
      rcases hz with rfl | rfl | rfl
      · exact ⟨![1, 0, 0], by simp [ε3, val_one3]⟩
      · exact ⟨![0, 1, 0], by simp [ε3, val_one3]⟩
      · exact ⟨![0, 0, 1], by simp [ε3, val_one3]⟩
  | one => exact ⟨0, ε3_zero⟩
  | mul _ _ _ _ ih₁ ih₂ =>
      obtain ⟨x, rfl⟩ := ih₁
      obtain ⟨y, rfl⟩ := ih₂
      exact ⟨x + y, hB.ε3_add x y⟩
  | inv _ _ ih =>
      obtain ⟨x, rfl⟩ := ih
      exact ⟨-x, hB.ε3_neg x⟩

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.ε3_pow (hB : FF81Basis b L B b₁ b₂ b₃) (x : Fin 3 → ZMod 3) (n : ℕ) :
    ε3 b₁ b₂ b₃ x ^ n = ε3 b₁ b₂ b₃ ((n : ZMod 3) • x) := by
  rw [hB.ε3_smul, ZMod.val_natCast]
  have h3 : ε3 b₁ b₂ b₃ x ^ 3 = 1 := by
    haveI := hB.elem.1
    exact CFSG.elemPow_eq_one_of_isElementaryAbelian _ (ε3_mem x)
  conv_lhs => rw [← Nat.mod_add_div n 3, pow_add, pow_mul, h3, one_pow, mul_one]

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.orderOf_ε3 (hB : FF81Basis b L B b₁ b₂ b₃) {x : Fin 3 → ZMod 3} (hx : x ≠ 0) :
    orderOf (ε3 b₁ b₂ b₃ x) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine orderOf_eq_prime ?_ (fun h => hx (hB.ε3_eq_one.mp h))
  rw [hB.ε3_pow, ZMod.natCast_self, zero_smul, ε3_zero]

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.mem_zpowers_ε3 (hB : FF81Basis b L B b₁ b₂ b₃) {x z : Fin 3 → ZMod 3} :
    ε3 b₁ b₂ b₃ z ∈ Subgroup.zpowers (ε3 b₁ b₂ b₃ x) ↔ ∃ c : ZMod 3, z = c • x := by
  constructor
  · intro h
    rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at h
    obtain ⟨n, hn⟩ := h
    rw [hB.ε3_pow] at hn
    exact ⟨n, (hB.ε3_inj hn).symm⟩
  · rintro ⟨c, rfl⟩
    rw [hB.ε3_smul]
    exact Subgroup.npow_mem_zpowers _ _

end Coord

def hypF : Fin 13 → (Fin 3 → ZMod 3) :=
  ![![1, 0, 0], ![0, 1, 0], ![0, 0, 1], ![1, 1, 0], ![1, 2, 0], ![1, 0, 1], ![1, 0, 2],
    ![0, 1, 1], ![0, 1, 2], ![1, 1, 1], ![1, 1, 2], ![1, 2, 1], ![1, 2, 2]]

def dot (f x : Fin 3 → ZMod 3) : ZMod 3 := f 0 * x 0 + f 1 * x 1 + f 2 * x 2

theorem dot_add (f x y : Fin 3 → ZMod 3) : dot f (x + y) = dot f x + dot f y := by
  simp only [dot, Pi.add_apply]; ring

theorem dot_neg (f x : Fin 3 → ZMod 3) : dot f (-x) = -dot f x := by
  simp only [dot, Pi.neg_apply]; ring

theorem hypUA_dot : ∀ i : Fin 13, dot (hypF i) (hypU i) = 0 ∧ dot (hypF i) (hypA i) = 0 := by
  decide

theorem span_of_dot : ∀ i : Fin 13, ∀ z0 z1 z2 : ZMod 3, dot (hypF i) ![z0, z1, z2] = 0 →
    ∃ c d : ZMod 3, ![z0, z1, z2] = c • hypU i + d • hypA i := by
  decide +kernel

def hyp (b₁ b₂ b₃ : G) (i : Fin 13) : Subgroup G :=
  Subgroup.closure {ε3 b₁ b₂ b₃ (hypU i), ε3 b₁ b₂ b₃ (hypA i)}

section Hyp

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem hyp_le (i : Fin 13) : hyp b₁ b₂ b₃ i ≤ Subgroup.closure {b₁, b₂, b₃} := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y (rfl | rfl) <;> exact ε3_mem _

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.mem_hyp (hB : FF81Basis b L B b₁ b₂ b₃) (i : Fin 13) (z : Fin 3 → ZMod 3) :
    ε3 b₁ b₂ b₃ z ∈ hyp b₁ b₂ b₃ i ↔ dot (hypF i) z = 0 := by
  constructor
  · intro h
    suffices key : ∀ y ∈ hyp b₁ b₂ b₃ i, ∃ w, ε3 b₁ b₂ b₃ w = y ∧ dot (hypF i) w = 0 by
      obtain ⟨w, hw, hw0⟩ := key _ h
      rwa [← hB.ε3_inj hw]
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
        rcases hy with rfl | rfl
        · exact ⟨_, rfl, (hypUA_dot i).1⟩
        · exact ⟨_, rfl, (hypUA_dot i).2⟩
    | one => exact ⟨0, ε3_zero, by simp [dot]⟩
    | mul _ _ _ _ ih₁ ih₂ =>
        obtain ⟨x, rfl, hx⟩ := ih₁
        obtain ⟨y, rfl, hy⟩ := ih₂
        exact ⟨x + y, hB.ε3_add x y, by rw [dot_add, hx, hy, add_zero]⟩
    | inv _ _ ih =>
        obtain ⟨x, rfl, hx⟩ := ih
        exact ⟨-x, hB.ε3_neg x, by rw [dot_neg, hx, neg_zero]⟩
  · intro h
    rw [vec3_eta z] at h ⊢
    obtain ⟨c, d, hcd⟩ := span_of_dot i _ _ _ h
    rw [hcd, hB.ε3_add, hB.ε3_smul, hB.ε3_smul]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)
      (Subgroup.pow_mem _ (Subgroup.subset_closure (by simp)) _)

theorem card_ker' : ∀ i : Fin 13, Fintype.card {z : Fin 3 → ZMod 3 // dot (hypF i) z = 0} = 9 := by
  decide

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.card_hyp (hB : FF81Basis b L B b₁ b₂ b₃) (i : Fin 13) :
    Nat.card (hyp b₁ b₂ b₃ i) = 9 := by
  classical
  have e : {z : Fin 3 → ZMod 3 // dot (hypF i) z = 0} ≃ hyp b₁ b₂ b₃ i :=
    Equiv.ofBijective (fun z => ⟨ε3 b₁ b₂ b₃ z, (hB.mem_hyp i z).2 z.2⟩)
      ⟨fun z w h => Subtype.ext (hB.ε3_inj (congrArg Subtype.val h)), fun y => by
        obtain ⟨z, hz⟩ := hB.exists_ε3 (hyp_le i y.2)
        exact ⟨⟨z, (hB.mem_hyp i z).1 (hz ▸ y.2)⟩, Subtype.ext hz⟩⟩
  rw [← Nat.card_congr e, Nat.card_eq_fintype_card]
  exact card_ker' i

end Hyp

theorem count1 : ∀ x0 x1 x2 : ZMod 3,
    (∑ i : Fin 13, if dot (hypF i) ![x0, x1, x2] = 0 then 1 else 0) =
      (if ![x0, x1, x2] = 0 then 9 else 0) + 4 := by
  decide +kernel

theorem count2 : ∀ x0 x1 x2 z0 z1 z2 : ZMod 3, ![x0, x1, x2] ≠ 0 →
    (∑ i : Fin 13, if dot (hypF i) ![z0, z1, z2] = 0 then
      (if dot (hypF i) ![x0, x1, x2] = 0 then 1 else 0) else 0) =
      (if ∃ c : ZMod 3, ![z0, z1, z2] = c • ![x0, x1, x2] then 3 else 0) + 1 := by
  decide +kernel

theorem cenS_bot : CenS (⊥ : Subgroup G) = ⊤ := by
  ext y
  simp only [Subgroup.mem_top, iff_true, Subgroup.mem_centralizer_iff, SetLike.mem_coe,
    Subgroup.mem_bot, forall_eq, mul_one, one_mul]

theorem cenS_zpowers (y : G) : CenS (Subgroup.zpowers y) = Cen y := by
  rw [CenS, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

section Wiel

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem card_B₁ (hB : FF81Basis b L B b₁ b₂ b₃) :
    Nat.card (Subgroup.closure ({b₁, b₂, b₃} : Set G)) = 27 := by
  rw [hB.elem.2]; norm_num

open _root_.Classical in
theorem card_mul_pow_twelve (hB : FF81Basis b L B b₁ b₂ b₃) {S : Subgroup G}
    (hS : Subgroup.closure {b₁, b₂, b₃} ≤ Nor S) (hcop : Nat.Coprime (Nat.card S) 3)
    (hsolv : Group.IsSolvable S) :
    Nat.card S * Nat.card ↥(S ⊓ CenS (Subgroup.closure {b₁, b₂, b₃})) ^ 12 =
      ∏ i : Fin 13, Nat.card ↥(S ⊓ CenS (hyp b₁ b₂ b₃ i)) := by
  set B₁ : Subgroup G := Subgroup.closure {b₁, b₂, b₃} with hB₁
  let H : Fin 13 ⊕ Fin 2 → Subgroup G := Sum.elim (hyp b₁ b₂ b₃) ![⊥, B₁]
  let m : Fin 13 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 1) ![0, 0]
  let n : Fin 13 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 0) ![9, 4]
  have hc27 : Nat.card B₁ = 27 := card_B₁ hB
  have hcop' : Nat.Coprime (Nat.card S) (Nat.card B₁) := by
    rw [hc27, show (27 : ℕ) = 3 ^ 3 by norm_num]; exact hcop.pow_right 3
  have hH : ∀ i, H i ≤ B₁ := by
    rintro (i | i)
    · exact hyp_le i
    · fin_cases i
      · exact bot_le
      · exact le_rfl
  have hcoeff : ∀ g ∈ B₁, (∑ i, if g ∈ H i then m i else 0) =
      ∑ i, if g ∈ H i then n i else 0 := by
    intro g hg
    obtain ⟨x, rfl⟩ := hB.exists_ε3 hg
    simp only [Fintype.sum_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Subgroup.mem_bot,
      hB.mem_hyp, hB.ε3_eq_one, hg, if_true, ite_self, Finset.sum_const_zero, add_zero, zero_add]
    rw [vec3_eta x]
    exact count1 _ _ _
  have h := wielandt_conj hS hcop' hsolv H hH m n hcoeff
  simp only [Fintype.prod_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Subgroup.card_bot, cenS_bot,
    inf_top_eq, hB.card_hyp, hc27, zero_mul, pow_zero, one_mul, mul_one,
    Finset.prod_const_one] at h
  apply Nat.pow_left_injective (show 9 ≠ 0 by norm_num)
  simp only
  rw [← Finset.prod_pow, h]
  ring

open _root_.Classical in
theorem card_cen_mul_pow_three (hB : FF81Basis b L B b₁ b₂ b₃) {S : Subgroup G}
    (hS : Subgroup.closure {b₁, b₂, b₃} ≤ Nor S) (hcop : Nat.Coprime (Nat.card S) 3)
    (hsolv : Group.IsSolvable S) {x : Fin 3 → ZMod 3} (hx : x ≠ 0) :
    Nat.card ↥(S ⊓ Cen (ε3 b₁ b₂ b₃ x)) *
        Nat.card ↥(S ⊓ CenS (Subgroup.closure {b₁, b₂, b₃})) ^ 3 =
      ∏ i ∈ Finset.univ.filter (fun i => dot (hypF i) x = 0),
        Nat.card ↥(S ⊓ CenS (hyp b₁ b₂ b₃ i)) := by
  set B₁ : Subgroup G := Subgroup.closure {b₁, b₂, b₃} with hB₁
  let H : Fin 13 ⊕ Fin 2 → Subgroup G :=
    Sum.elim (hyp b₁ b₂ b₃) ![Subgroup.zpowers (ε3 b₁ b₂ b₃ x), B₁]
  let m : Fin 13 ⊕ Fin 2 → ℕ := Sum.elim (fun i => if dot (hypF i) x = 0 then 1 else 0) ![0, 0]
  let n : Fin 13 ⊕ Fin 2 → ℕ := Sum.elim (fun _ => 0) ![3, 1]
  have hc27 : Nat.card B₁ = 27 := card_B₁ hB
  have hcop' : Nat.Coprime (Nat.card S) (Nat.card B₁) := by
    rw [hc27, show (27 : ℕ) = 3 ^ 3 by norm_num]; exact hcop.pow_right 3
  have hH : ∀ i, H i ≤ B₁ := by
    rintro (i | i)
    · exact hyp_le i
    · fin_cases i
      · exact Subgroup.zpowers_le.mpr (ε3_mem x)
      · exact le_rfl
  have hcoeff : ∀ g ∈ B₁, (∑ i, if g ∈ H i then m i else 0) =
      ∑ i, if g ∈ H i then n i else 0 := by
    intro g hg
    obtain ⟨z, rfl⟩ := hB.exists_ε3 hg
    simp only [Fintype.sum_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, hB.mem_zpowers_ε3,
      hB.mem_hyp, hg, if_true, ite_self, Finset.sum_const_zero, add_zero, zero_add]
    rw [vec3_eta x, vec3_eta z]
    rw [vec3_eta x] at hx
    exact count2 _ _ _ _ _ _ hx
  have h := wielandt_conj hS hcop' hsolv H hH m n hcoeff
  simp only [Fintype.prod_sum_type, H, m, n, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, cenS_zpowers,
    hB.card_hyp, hc27, Nat.card_zpowers, hB.orderOf_ε3 hx, zero_mul, pow_zero, one_mul,
    mul_one, Finset.prod_const_one] at h
  apply Nat.pow_left_injective (show 9 ≠ 0 by norm_num)
  simp only
  rw [← Finset.prod_pow, Finset.prod_filter]
  have e : ∀ i : Fin 13, (if dot (hypF i) x = 0 then Nat.card ↥(S ⊓ CenS (hyp b₁ b₂ b₃ i)) ^ 9
      else 1) =
      Nat.card ↥(S ⊓ CenS (hyp b₁ b₂ b₃ i)) ^ ((if dot (hypF i) x = 0 then 1 else 0) * 9) := by
    intro i; split_ifs <;> simp
  rw [Finset.prod_congr rfl fun i _ => e i, h]
  ring

end Wiel

end S36

end CFSG.RankThree.PartTwo.Sec21.FF81
