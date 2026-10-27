module

public import CFSG.GH74.M12.HypModel

public section

namespace CFSG.RankThree.PartTwo.Toolkit.M12

open CFSG.GH74.M12.Hyp CFSG.Blueprint

@[expose] def trW : List (List (List Int)) := [
  [
    [],
    [2, 1],
    [-2, 1],
    [1],
    [-2, 1, -2, 1, -2, 1],
    [-2, 1, -2, 1],
    [2, 1, -2, 1],
    [2],
    [-2],
    [1, -2, 1],
    [2, 1, -2, 1, -2, 1],
    [1, -2, 1, -2, 1]
  ],
  [
    [],
    [1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2],
    [2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1],
    [2, 1, -2, 1, -2, 1, 2, 1],
    [-2, 1, 2],
    [-2, 1, -2, 1, -2, 1, -2, 1, 2, 1],
    [2, 1, -2],
    [1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1],
    [2, 1, 2, 1, 2, 1, -2, 1, 2, 1],
    [-2, 1, 2, 1, -2, 1, 2, 1],
    [1, -2, 1, 2, 1]
  ],
  [
    [],
    [2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2],
    [-2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1],
    [1, 2, 1, -2, 1, 2, 1, -2, 1],
    [1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2],
    [-2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1],
    [2, 1, 2, 1, -2, 1, -2],
    [1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2],
    [2, 1, -2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, -2]
  ],
  [
    [],
    [-2, 1, -2, 1, 2, 1, 2],
    [-2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2],
    [-2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2],
    [2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2],
    [2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2],
    [2, 1, 2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2],
    [-2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2]
  ],
  [
    [],
    [2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2,
     1, 2, 1, 2],
    [1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1],
    [1, 2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2],
    [2, 1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, -2, 1,
     2, 1, 2],
    [1, -2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1],
    [-2, 1, -2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1,
     -2, 1, 2, 1, -2],
    [-2, 1, 2, 1, -2, 1, 2, 1, 2, 1, 2, 1, -2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1]
  ]]

@[expose] def trT : List (List (List ℕ)) := trW.map fun l => l.map wordT

@[expose] def wrd (i k : ℕ) : List Int := (trW.getD i []).getD k []

@[expose] def tab (i k : ℕ) : List ℕ := (trT.getD i []).getD k tid

theorem tab_eq (i k : ℕ) : tab i k = wordT (wrd i k) := by
  unfold tab wrd trT
  rw [show ([] : List (List ℕ)) = List.map wordT [] from rfl, List.getD_map,
    show tid = wordT [] from rfl, List.getD_map]

theorem tab_fix : ∀ i < 5, ∀ k < 12 - i, ∀ m < i, (tab i k).getD m 0 = m := by
  decide +kernel

theorem tab_move : ∀ i < 5, ∀ k < 12 - i, (tab i k).getD i 0 = i + k := by
  decide +kernel

@[expose] def trP (i k : ℕ) : Equiv.Perm (Fin 12) := wordP (wrd i k)

theorem tbl_trP (i k : ℕ) : tbl (trP i k) = tab i k := by
  rw [trP, tbl_wordP, tab_eq]

theorem trP_mem (i k : ℕ) : trP i k ∈ NativeSporadic.M12 := wordP_mem _

theorem trP_apply_of_lt {i k : ℕ} (hi : i < 5) (hk : k < 12 - i) {m : Fin 12} (hm : m.val < i) :
    trP i k m = m := by
  apply Fin.ext
  rw [← tbl_getD, tbl_trP, tab_fix i hi k hk m hm]

theorem trP_apply_base {i k : ℕ} (hi : i < 5) (hk : k < 12 - i) :
    (trP i k ⟨i, by omega⟩).val = i + k := by
  rw [← tbl_getD, tbl_trP]
  exact tab_move i hi k hk

theorem step {i : ℕ} (hi : i < 5) {g : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12)
    (hfix : ∀ m : Fin 12, m.val < i → g m = m) :
    ∃ k < 12 - i, (trP i k)⁻¹ * g ∈ NativeSporadic.M12 ∧
      ∀ m : Fin 12, m.val < i + 1 → ((trP i k)⁻¹ * g) m = m := by
  set j := (g ⟨i, by omega⟩).val with hj
  have hij : i ≤ j := by
    by_contra h
    push Not at h
    have h1 : g ⟨j, by omega⟩ = ⟨j, by omega⟩ := hfix _ h
    have h2 : g ⟨i, by omega⟩ = ⟨j, by omega⟩ := Fin.ext hj.symm
    have := g.injective (h1.trans h2.symm)
    simp only [Fin.mk.injEq] at this
    omega
  have hjlt : j < 12 := (g ⟨i, by omega⟩).isLt
  refine ⟨j - i, by omega, NativeSporadic.M12.mul_mem (NativeSporadic.M12.inv_mem
    (trP_mem _ _)) hg, fun m hm => ?_⟩
  rw [Equiv.Perm.coe_mul, Function.comp_apply, Equiv.Perm.inv_eq_iff_eq]
  rcases Nat.lt_or_ge m.val i with h | h
  · rw [hfix m h, trP_apply_of_lt hi (by omega) h]
  · have hm' : m = ⟨i, by omega⟩ := Fin.ext (show m.val = i by omega)
    rw [hm']
    apply Fin.ext
    rw [trP_apply_base hi (by omega), ← hj]
    omega

abbrev Idx : Type := ℕ × ℕ × ℕ × ℕ × ℕ

@[expose] def prodT (k : Idx) : List ℕ :=
  tmul (tab 0 k.1) (tmul (tab 1 k.2.1) (tmul (tab 2 k.2.2.1) (tmul (tab 3 k.2.2.2.1)
    (tab 4 k.2.2.2.2))))

@[expose] def prodP (k : Idx) : Equiv.Perm (Fin 12) :=
  trP 0 k.1 * (trP 1 k.2.1 * (trP 2 k.2.2.1 * (trP 3 k.2.2.2.1 * trP 4 k.2.2.2.2)))

theorem tbl_prodP (k : Idx) : tbl (prodP k) = prodT k := by
  simp only [prodP, prodT, tbl_mul, tbl_trP]

theorem prodP_mem (k : Idx) : prodP k ∈ NativeSporadic.M12 := by
  unfold prodP
  exact NativeSporadic.M12.mul_mem (trP_mem _ _) (NativeSporadic.M12.mul_mem (trP_mem _ _)
    (NativeSporadic.M12.mul_mem (trP_mem _ _) (NativeSporadic.M12.mul_mem (trP_mem _ _)
      (trP_mem _ _))))

@[expose] def allIdx : List Idx :=
  (List.range 12).flatMap fun a => (List.range 11).flatMap fun b => (List.range 10).flatMap
    fun c => (List.range 9).flatMap fun d => (List.range 8).map fun e => (a, b, c, d, e)

theorem mem_allIdx {a b c d e : ℕ} (ha : a < 12) (hb : b < 11) (hc : c < 10) (hd : d < 9)
    (he : e < 8) : (a, b, c, d, e) ∈ allIdx := by
  simp only [allIdx, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨a, ha, b, hb, c, hc, d, hd, e, he, rfl⟩

theorem exists_eq_prodP {g : Equiv.Perm (Fin 12)} (hg : g ∈ NativeSporadic.M12) :
    ∃ k ∈ allIdx, g = prodP k := by
  obtain ⟨a, ha, hg₁, hf₁⟩ := step (i := 0) (by norm_num) hg (fun m hm => absurd hm (by omega))
  obtain ⟨b, hb, hg₂, hf₂⟩ := step (i := 1) (by norm_num) hg₁ hf₁
  obtain ⟨c, hc, hg₃, hf₃⟩ := step (i := 2) (by norm_num) hg₂ hf₂
  obtain ⟨d, hd, hg₄, hf₄⟩ := step (i := 3) (by norm_num) hg₃ hf₃
  obtain ⟨e, he, hg₅, hf₅⟩ := step (i := 4) (by norm_num) hg₄ hf₄
  have h1 := congrArg Subtype.val (m12_fix5 ⟨_, hg₅⟩ fun m hm => hf₅ m hm)
  simp only [OneMemClass.coe_one] at h1
  refine ⟨(a, b, c, d, e), mem_allIdx (by omega) (by omega) (by omega) (by omega) (by omega), ?_⟩
  have h2 := (inv_mul_eq_one.1 h1).symm
  rw [inv_mul_eq_iff_eq_mul, inv_mul_eq_iff_eq_mul, inv_mul_eq_iff_eq_mul,
    inv_mul_eq_iff_eq_mul] at h2
  exact h2

end CFSG.RankThree.PartTwo.Toolkit.M12
