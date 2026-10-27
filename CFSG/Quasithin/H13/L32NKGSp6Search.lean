module

public import CFSG.Quasithin.H13.L32NKGG22
public import Certificates.Data.CFSGNative.KGroups.Sp6G22

public section

namespace CFSG.Quasithin.H13.KGSp6

open CFSG.KGroups.Sp6

theorem mulVecC_eq : mulVecC = KGCert.mulVecC := rfl

theorem mulC_eq : mulC = KGCert.mulC := rfl

theorem oneC_eq : oneC = KGCert.oneC := rfl

theorem b2z_bf (x y : ℕ) :
    KGCert.b2z (bf x y) =
      dotProduct (KGCert.vec6 x) (KGCert.g22Form.mulVec (KGCert.vec6 y)) := by
  simp only [bf, KGCert.b2z_xor, KGCert.b2z_and, Matrix.mulVec, dotProduct, Fin.sum_univ_six,
    KGCert.vec6, KGCert.g22Form]
  simp
  ring

theorem bf_comm_bits : ∀ a0 a1 a2 a3 a4 a5 b0 b1 b2 b3 b4 b5 : Bool,
    ((a0 && b3) ^^ (a3 && b0) ^^ (a1 && b4) ^^ (a4 && b1) ^^ (a2 && b5) ^^ (a5 && b2)) =
    ((b0 && a3) ^^ (b3 && a0) ^^ (b1 && a4) ^^ (b4 && a1) ^^ (b2 && a5) ^^ (b5 && a2)) := by
  decide +kernel

theorem bf_self_bits : ∀ a0 a1 a2 a3 a4 a5 : Bool,
    ((a0 && a3) ^^ (a3 && a0) ^^ (a1 && a4) ^^ (a4 && a1) ^^ (a2 && a5) ^^ (a5 && a2)) =
    false := by
  decide +kernel

theorem bf_comm (x y : ℕ) : bf x y = bf y x :=
  bf_comm_bits _ _ _ _ _ _ _ _ _ _ _ _

theorem bf_self (x : ℕ) : bf x x = false :=
  bf_self_bits _ _ _ _ _ _

theorem bf_zero_right (x : ℕ) : bf x 0 = false := by
  simp [bf]

theorem bf_zero_left (x : ℕ) : bf 0 x = false := by
  rw [bf_comm]
  exact bf_zero_right x

@[expose] def jb (i j : Fin 6) : Bool := decide (i.val + 3 = j.val ∨ j.val + 3 = i.val)

theorem jb_symm (i j : Fin 6) : jb i j = jb j i := by
  simp only [jb, or_comm]

theorem jb_self (i : Fin 6) : jb i i = false := by
  simp [jb]

@[expose] def Cols (x : List ℕ) : Prop :=
  ∀ i j : Fin 6, bf (x.getD i 0) (x.getD j 0) = jb i j

theorem cols_of_upper (c : Fin 6 → ℕ) (h : ∀ i j : Fin 6, i < j → bf (c i) (c j) = jb i j) :
    ∀ i j : Fin 6, bf (c i) (c j) = jb i j := by
  intro i j
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h i j hij
  · rw [bf_self, jb_self]
  · rw [bf_comm, h j i hji, jb_symm]

theorem cols_of_cands {c0 c1 c2 c3 c4 c5 : ℕ} (h1 : cand1 c0 c1 = true)
    (h2 : cand2 c0 c1 c2 = true) (h3 : cand3 c0 c1 c2 c3 = true)
    (h4 : cand4 c0 c1 c2 c3 c4 = true) (h5 : cand5 c0 c1 c2 c3 c4 c5 = true) :
    Cols [c0, c1, c2, c3, c4, c5] := by
  simp only [cand1, cand2, cand3, cand4, cand5, Bool.and_eq_true, bne_iff_ne, ne_eq,
    Bool.not_eq_true'] at h1 h2 h3 h4 h5
  obtain ⟨-, a01⟩ := h1
  obtain ⟨⟨-, a02⟩, a12⟩ := h2
  obtain ⟨⟨⟨-, a03⟩, a13⟩, a23⟩ := h3
  obtain ⟨⟨⟨⟨-, a04⟩, a14⟩, a24⟩, a34⟩ := h4
  obtain ⟨⟨⟨⟨⟨-, a05⟩, a15⟩, a25⟩, a35⟩, a45⟩ := h5
  refine cols_of_upper (fun i => [c0, c1, c2, c3, c4, c5].getD i 0) ?_
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | simp [jb, *]

theorem cands_of_cols {c0 c1 c2 c3 c4 c5 : ℕ} (h : Cols [c0, c1, c2, c3, c4, c5]) :
    cand0 c0 = true ∧ cand1 c0 c1 = true ∧ cand2 c0 c1 c2 = true ∧ cand3 c0 c1 c2 c3 = true ∧
    cand4 c0 c1 c2 c3 c4 = true ∧ cand5 c0 c1 c2 c3 c4 c5 = true := by
  have f01 : bf c0 c1 = false := by simpa [jb] using h 0 1
  have f02 : bf c0 c2 = false := by simpa [jb] using h 0 2
  have f12 : bf c1 c2 = false := by simpa [jb] using h 1 2
  have f03 : bf c0 c3 = true := by simpa [jb] using h 0 3
  have f13 : bf c1 c3 = false := by simpa [jb] using h 1 3
  have f23 : bf c2 c3 = false := by simpa [jb] using h 2 3
  have f04 : bf c0 c4 = false := by simpa [jb] using h 0 4
  have f14 : bf c1 c4 = true := by simpa [jb] using h 1 4
  have f24 : bf c2 c4 = false := by simpa [jb] using h 2 4
  have f34 : bf c3 c4 = false := by simpa [jb] using h 3 4
  have f05 : bf c0 c5 = false := by simpa [jb] using h 0 5
  have f15 : bf c1 c5 = false := by simpa [jb] using h 1 5
  have f25 : bf c2 c5 = true := by simpa [jb] using h 2 5
  have f35 : bf c3 c5 = false := by simpa [jb] using h 3 5
  have f45 : bf c4 c5 = false := by simpa [jb] using h 4 5
  have n0 : c0 ≠ 0 := fun e => by rw [e, bf_zero_left] at f03; exact absurd f03 (by decide)
  have n1 : c1 ≠ 0 := fun e => by rw [e, bf_zero_left] at f14; exact absurd f14 (by decide)
  have n2 : c2 ≠ 0 := fun e => by rw [e, bf_zero_left] at f25; exact absurd f25 (by decide)
  have n3 : c3 ≠ 0 := fun e => by rw [e, bf_zero_right] at f03; exact absurd f03 (by decide)
  have n4 : c4 ≠ 0 := fun e => by rw [e, bf_zero_right] at f14; exact absurd f14 (by decide)
  have n5 : c5 ≠ 0 := fun e => by rw [e, bf_zero_right] at f25; exact absurd f25 (by decide)
  simp [cand0, cand1, cand2, cand3, cand4, cand5, *]

@[expose] def spLeaves (r : ℕ) : List (List ℕ) :=
  ((List.range r).filter cand0).flatMap fun c0 =>
   ((List.range r).filter (cand1 c0)).flatMap fun c1 =>
    ((List.range r).filter (cand2 c0 c1)).flatMap fun c2 =>
     ((List.range r).filter (cand3 c0 c1 c2)).flatMap fun c3 =>
      ((List.range r).filter (cand4 c0 c1 c2 c3)).flatMap fun c4 =>
       ((List.range r).filter (cand5 c0 c1 c2 c3 c4)).map fun c5 => [c0, c1, c2, c3, c4, c5]

theorem mem_spLeaves {r : ℕ} {x : List ℕ} : x ∈ spLeaves r ↔ ∃ c0 c1 c2 c3 c4 c5 : ℕ,
    x = [c0, c1, c2, c3, c4, c5] ∧ c0 < r ∧ cand0 c0 = true ∧ c1 < r ∧ cand1 c0 c1 = true ∧
    c2 < r ∧ cand2 c0 c1 c2 = true ∧ c3 < r ∧ cand3 c0 c1 c2 c3 = true ∧ c4 < r ∧
    cand4 c0 c1 c2 c3 c4 = true ∧ c5 < r ∧ cand5 c0 c1 c2 c3 c4 c5 = true := by
  simp only [spLeaves, List.mem_flatMap, List.mem_filter, List.mem_range, List.mem_map]
  constructor
  · rintro ⟨c0, ⟨h0, h0'⟩, c1, ⟨h1, h1'⟩, c2, ⟨h2, h2'⟩, c3, ⟨h3, h3'⟩, c4, ⟨h4, h4'⟩, c5,
      ⟨h5, h5'⟩, rfl⟩
    exact ⟨c0, c1, c2, c3, c4, c5, rfl, h0, h0', h1, h1', h2, h2', h3, h3', h4, h4', h5, h5'⟩
  · rintro ⟨c0, c1, c2, c3, c4, c5, rfl, h0, h0', h1, h1', h2, h2', h3, h3', h4, h4', h5, h5'⟩
    exact ⟨c0, ⟨h0, h0'⟩, c1, ⟨h1, h1'⟩, c2, ⟨h2, h2'⟩, c3, ⟨h3, h3'⟩, c4, ⟨h4, h4'⟩, c5,
      ⟨h5, h5'⟩, rfl⟩

theorem mem_spLeaves_cols {x : List ℕ} : x ∈ spLeaves 64 ↔ KGCert.ValidC x ∧ Cols x := by
  rw [mem_spLeaves]
  constructor
  · rintro ⟨c0, c1, c2, c3, c4, c5, rfl, h0, -, h1, h1', h2, h2', h3, h3', h4, h4', h5, h5'⟩
    refine ⟨⟨rfl, ?_⟩, cols_of_cands h1' h2' h3' h4' h5'⟩
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    omega
  · rintro ⟨⟨hlen, hlt⟩, hc⟩
    rcases x with _ | ⟨c0, _ | ⟨c1, _ | ⟨c2, _ | ⟨c3, _ | ⟨c4, _ | ⟨c5, _ | ⟨c6, l⟩⟩⟩⟩⟩⟩⟩ <;>
      simp at hlen
    obtain ⟨k0, k1, k2, k3, k4, k5⟩ := cands_of_cols hc
    simp only [List.mem_cons, forall_eq_or_imp, List.not_mem_nil, false_imp_iff,
      implies_true, and_true] at hlt
    exact ⟨c0, c1, c2, c3, c4, c5, rfl, hlt.1, k0, hlt.2.1, k1, hlt.2.2.1, k2, hlt.2.2.2.1, k3,
      hlt.2.2.2.2.1, k4, hlt.2.2.2.2.2, k5⟩

theorem entry_eq (x : List ℕ) (i j : Fin 6) :
    ((KGCert.decodeC x).transpose * KGCert.g22Form * KGCert.decodeC x) i j =
      KGCert.b2z (bf (x.getD i 0) (x.getD j 0)) := by
  rw [b2z_bf]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, dotProduct, Matrix.mulVec,
    KGCert.decodeC, Matrix.of_apply, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [Finset.sum_comm]

theorem g22Form_eq (i j : Fin 6) : KGCert.g22Form i j = KGCert.b2z (jb i j) := by
  fin_cases i <;> fin_cases j <;> decide

theorem cols_iff {x : List ℕ} :
    Cols x ↔ (KGCert.decodeC x).transpose * KGCert.g22Form * KGCert.decodeC x =
      KGCert.g22Form := by
  constructor
  · intro h
    ext i j
    rw [entry_eq, g22Form_eq, h i j]
  · intro h i j
    apply KGCert.b2z_inj
    rw [← entry_eq, h, g22Form_eq]

theorem mem_spLeaves_iff {x : List ℕ} : x ∈ spLeaves 64 ↔ KGCert.ValidC x ∧
    (KGCert.decodeC x).transpose * KGCert.g22Form * KGCert.decodeC x = KGCert.g22Form := by
  rw [mem_spLeaves_cols, cols_iff]

end CFSG.Quasithin.H13.KGSp6
