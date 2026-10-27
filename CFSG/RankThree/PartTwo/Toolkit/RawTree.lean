module

public import CFSG.RankThree.PartTwo.Toolkit.RawCode

public section

namespace CFSG.RankThree.PartTwo.Toolkit.Raw

@[expose] def codeMask (l : List ℕ) : ℕ := l.foldl (fun m c => m ||| 1 <<< c) 0

theorem testBit_foldl_mask (l : List ℕ) (m c : ℕ) :
    (l.foldl (fun m c => m ||| 1 <<< c) m).testBit c = true ↔ m.testBit c = true ∨ c ∈ l := by
  induction l generalizing m with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, Nat.testBit_lor, Nat.one_shiftLeft, Nat.testBit_two_pow,
      List.mem_cons]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    tauto

theorem testBit_codeMask {l : List ℕ} {c : ℕ} : (codeMask l).testBit c = true ↔ c ∈ l := by
  rw [codeMask, testBit_foldl_mask]
  simp

@[expose] def pk (w X k : ℕ) : ℕ := (X >>> (w * k)) % 2 ^ w

@[expose] def treeOKP (gs : List ℕ) (C P L n : ℕ) : Bool :=
  decide (0 < n) && pk 20 C 0 == 6643 &&
    (List.range n).all fun k => k == 0 ||
      (decide (pk 16 P k < k) && decide (pk 4 L k < gs.length) &&
        pk 20 C k == nmul (gs.getD (pk 4 L k) 6643) (pk 20 C (pk 16 P k)))

section Sound

variable {G : Type*} [Group G] (f : G → R9) (hmul : ∀ x y, f (x * y) = rmul (f x) (f y))
  (hone : f 1 = rone)
include hmul hone

theorem treeOKP_mem (gs : List G) {C P L n : ℕ}
    (hT : treeOKP (gs.map fun x => code (f x)) C P L n = true) :
    ∀ k < n, ∃ x ∈ Subgroup.closure {y | y ∈ gs}, code (f x) = pk 20 C k := by
  simp only [treeOKP, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at hT
  obtain ⟨⟨_, hroot⟩, hstep⟩ := hT
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases hstep k hk with h0 | ⟨⟨hp, hj⟩, hx⟩
    · subst h0
      exact ⟨1, Subgroup.one_mem _, by rw [hone, hroot, code_rone]⟩
    · obtain ⟨x', hx'mem, hx'⟩ := ih _ hp (lt_trans hp hk)
      rw [List.length_map] at hj
      refine ⟨gs[pk 4 L k] * x', Subgroup.mul_mem _ (Subgroup.subset_closure ?_) hx'mem, ?_⟩
      · exact List.getElem_mem hj
      · rw [hmul, hx, ← hx', ← nmul_code,
          List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj), List.getElem_map]

end Sound

@[expose] def treeMask (C n : ℕ) : ℕ := codeMask ((List.range n).map (pk 20 C))

@[expose] def slCovered (M : ℕ) : Bool :=
  (List.range 19683).all fun c => ndet c != 1 || M.testBit c

@[expose] def slCoverP (gs : List ℕ) (C P L n : ℕ) : Bool :=
  treeOKP gs C P L n && slCovered (treeMask C n)

theorem exists_of_slCoverP {gs : List ℕ} {C P L n : ℕ} (h : slCoverP gs C P L n = true)
    {r : R9} (hr : rdet r = 1) : ∃ k < n, pk 20 C k = code r := by
  simp only [slCoverP, slCovered, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq] at h
  rcases h.2 (code r) (code_lt r) with h1 | h1
  · rw [ndet_code, hr] at h1
    exact absurd rfl h1
  · rw [treeMask, testBit_codeMask, List.mem_map] at h1
    obtain ⟨k, hk, hkr⟩ := h1
    exact ⟨k, List.mem_range.1 hk, hkr⟩

theorem statedSL_le_closureP (gs : List (GL (Fin 3) (ZMod 3))) (C P L n : ℕ)
    (h : slCoverP (gs.map fun x : GL (Fin 3) (ZMod 3) =>
      code (ofMat (x : Matrix (Fin 3) (Fin 3) (ZMod 3)))) C P L n = true) :
    CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ Subgroup.closure {y | y ∈ gs} := by
  have hmul : ∀ x y : GL (Fin 3) (ZMod 3), ofMat ((x * y : GL (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) = rmul (ofMat x) (ofMat y) := fun x y => by
    rw [Units.val_mul, ofMat_mul]
  have hone : ofMat ((1 : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = rone := by
    rw [Units.val_one, ofMat_one]
  have htree : treeOKP (gs.map fun x : GL (Fin 3) (ZMod 3) =>
      code (ofMat (x : Matrix (Fin 3) (Fin 3) (ZMod 3)))) C P L n = true := by
    simp only [slCoverP, Bool.and_eq_true] at h
    exact h.1
  rw [CFSG.Assembly.LowTwoRank.StatedSL, Subgroup.closure_le]
  intro x hx
  obtain ⟨k, hk, hkx⟩ := exists_of_slCoverP h (r := ofMat x) (by rw [rdet_ofMat]; exact hx)
  obtain ⟨y, hy, hyx⟩ := treeOKP_mem (fun x : GL (Fin 3) (ZMod 3) =>
    ofMat (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) hmul hone gs htree k hk
  have : y = x := Units.ext (ofMat_injective (code_injective (hyx.trans hkx)))
  rw [← this]
  exact hy

end CFSG.RankThree.PartTwo.Toolkit.Raw

end
