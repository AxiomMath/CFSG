module

public import CFSG.Quasithin.H13.L32NMat8
public import Certificates.Certificate7242
public import Mathlib.Data.LawfulXor.Basic
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Quasithin.H13.G9MCert

open Mat8Cert

theorem g9mCheck_eq : g9mCheck = true :=
  Certificates.certificate7242

theorem valid8_of_validB {x : List ℕ} (h : validB x = true) : Valid8 x := by
  simp only [validB, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at h
  exact h

theorem mem_all4 {a b c d : ℕ} (ha : a < 16) (hb : b < 16) (hc : c < 16) (hd : d < 16) :
    [a, b, c, d] ∈ all4 := by
  simp only [all4, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨a, ha, b, hb, c, hc, d, hd, rfl⟩

theorem mem_invs {x : List ℕ} (hx : x ∈ all4) (h : mul8 (blk x) (blk x) = one8) : x ∈ invs :=
  List.mem_filter.mpr ⟨hx, by rw [h]; rfl⟩

theorem mem_ords5 {y : List ℕ} (hy : y ∈ all4) (h5 : pow8 (blk y) 5 = one8)
    (h1 : blk y ≠ one8) : y ∈ ords5 :=
  List.mem_filter.mpr ⟨hy, by simp [h5, h1]⟩

theorem mv8_s0c_lt : ∀ c < 256, mv8 s0c c = c → c < 16 := by decide +kernel

theorem mv8_s1c_eq : ∀ c < 16, mv8 s1c c = 16 * c := by decide +kernel

theorem mv8_cols (l0 l1 l2 l3 l4 l5 l6 l7 : ℕ) :
    mv8 [l0, l1, l2, l3, l4, l5, l6, l7] 1 = l0 ∧ mv8 [l0, l1, l2, l3, l4, l5, l6, l7] 2 = l1 ∧
    mv8 [l0, l1, l2, l3, l4, l5, l6, l7] 4 = l2 ∧ mv8 [l0, l1, l2, l3, l4, l5, l6, l7] 8 = l3 ∧
    mv8 [l0, l1, l2, l3, l4, l5, l6, l7] 16 = l4 ∧ mv8 [l0, l1, l2, l3, l4, l5, l6, l7] 32 = l5 ∧
    mv8 [l0, l1, l2, l3, l4, l5, l6, l7] 64 = l6 ∧
    mv8 [l0, l1, l2, l3, l4, l5, l6, l7] 128 = l7 := by
  simp [mv8, bt, Nat.testBit]

theorem blk_of_comm {L : List ℕ} (hL : Valid8 L) (h0 : mul8 L s0c = mul8 s0c L)
    (h1 : mul8 L s1c = mul8 s1c L) : ∃ xs ∈ all4, L = blk xs := by
  obtain ⟨hlen, hlt⟩ := hL
  match L, hlen, hlt, h0, h1 with
  | [l0, l1, l2, l3, l4, l5, l6, l7], _, hlt, h0, h1 =>
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7⟩ := mv8_cols l0 l1 l2 l3 l4 l5 l6 l7
    simp only [mul8, s0c, s1c, List.map_cons, List.map_nil, List.cons.injEq, and_true] at h0 h1
    rw [c0, c1, c2, c3] at h0
    rw [c4, c5, c6, c7] at h1
    obtain ⟨e0, e1, e2, e3, -, -, -, -⟩ := h0
    obtain ⟨f4, f5, f6, f7, -, -, -, -⟩ := h1
    have hb : ∀ c ∈ [l0, l1, l2, l3, l4, l5, l6, l7], c < 256 := hlt
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hb
    obtain ⟨b0, b1, b2, b3, -, -, -, -⟩ := hb
    have k0 := mv8_s0c_lt l0 b0 e0.symm
    have k1 := mv8_s0c_lt l1 b1 e1.symm
    have k2 := mv8_s0c_lt l2 b2 e2.symm
    have k3 := mv8_s0c_lt l3 b3 e3.symm
    refine ⟨[l0, l1, l2, l3], mem_all4 k0 k1 k2 k3, ?_⟩
    have g : ∀ c < 16, mv8 [16, 32, 64, 128, 1, 2, 4, 8] c = 16 * c := mv8_s1c_eq
    rw [f4, f5, f6, f7, g l0 k0, g l1 k1, g l2 k2, g l3 k3]
    rfl

theorem check_parts :
    normCheck = true ∧ s5Check = true ∧ a5Check = true := by
  have h := g9mCheck_eq
  simp only [g9mCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem verifyY_spec {y d di : List ℕ} (h : verifyY y d di = true) :
    Valid8 (blk d) ∧ Valid8 (blk di) ∧ mul8 (blk d) (blk di) = one8 ∧
      mul8 (blk di) (blk d) = one8 ∧ mul8 (blk y) (blk d) = mul8 (blk d) (blk y0) ∧
      mul8 (blk d) s0c = mul8 s0c (blk d) ∧ mul8 (blk d) s1c = mul8 s1c (blk d) := by
  simp only [verifyY, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨valid8_of_validB h1, valid8_of_validB h2, h3, h4, h5, h6, h7⟩

theorem verifyC_spec {x y c ic xm ym : List ℕ} (h : verifyC x y c ic xm ym = true) :
    Valid8 (blk c) ∧ Valid8 (blk ic) ∧ mul8 (blk c) (blk ic) = one8 ∧
      mul8 (blk ic) (blk c) = one8 ∧ mul8 (blk x) (blk c) = mul8 (blk c) (blk xm) ∧
      mul8 (blk y) (blk c) = mul8 (blk c) (blk ym) ∧ mul8 (blk c) s0c = mul8 s0c (blk c) ∧
      mul8 (blk c) s1c = mul8 s1c (blk c) := by
  simp only [verifyC, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  exact ⟨valid8_of_validB h1, valid8_of_validB h2, h3, h4, h5, h6, h7, h8⟩

theorem norm_spec {y : List ℕ} (hy : y ∈ ords5) :
    ∃ d di, verifyY y d di = true := by
  have h := List.all_eq_true.mp check_parts.1 y hy
  cases hd : inv4 (spinY y) with
  | none => simp only [hd] at h; exact absurd h (by decide)
  | some di => simp only [hd] at h; exact ⟨_, di, h⟩

theorem findConj_spec {x y : List ℕ} {ms : List Model} {r : List ℕ × List ℕ × List ℕ × List ℕ}
    (h : findConj x y ms = some r) : ∃ m ∈ ms, verifyC x y r.1 r.2.1 m.1 m.2.1 = true := by
  unfold findConj at h
  obtain ⟨m, hm, h⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨i, -, h⟩ := List.exists_of_findSome?_eq_some h
  refine ⟨m, hm, ?_⟩
  unfold tryC at h
  split at h
  · split at h
    · split at h
      · rename_i hv
        cases h
        exact hv
      · cases h
    · cases h
  · cases h

theorem s5_spec {x : List ℕ} (hx : x ∈ invs)
    (hr : relS5 (blk x) (blk y0) = true) :
    ∃ c ic, ∃ m ∈ modelsS5, verifyC x y0 c ic m.1 m.2.1 = true := by
  have h := List.all_eq_true.mp check_parts.2.1 x hx
  rw [hr, Bool.not_true, Bool.false_or, Option.isSome_iff_exists] at h
  obtain ⟨r, hr'⟩ := h
  obtain ⟨m, hm, hv⟩ := findConj_spec hr'
  exact ⟨r.1, r.2.1, m, hm, hv⟩

theorem a5_spec {x : List ℕ} (hx : x ∈ invs) (h1 : x ≠ one4)
    (hr : relA5 (blk x) (blk y0) = true) :
    ∃ c ic, ∃ m ∈ modelsA5, verifyC x y0 c ic m.1 m.2.1 = true := by
  have h := List.all_eq_true.mp check_parts.2.2 x hx
  have h1' : (x == one4) = false := by simpa using h1
  rw [h1', hr, Bool.not_true, Bool.false_or, Bool.false_or, Option.isSome_iff_exists] at h
  obtain ⟨r, hr'⟩ := h
  obtain ⟨m, hm, hv⟩ := findConj_spec hr'
  exact ⟨r.1, r.2.1, m, hm, hv⟩

end CFSG.Quasithin.H13.G9MCert
