module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.PartTwo.Toolkit.Raw

structure R9 where
  a : ZMod 3
  b : ZMod 3
  c : ZMod 3
  d : ZMod 3
  e : ZMod 3
  f : ZMod 3
  g : ZMod 3
  h : ZMod 3
  i : ZMod 3
  deriving Inhabited

@[expose] def R9.beq (x y : R9) : Bool :=
  x.a == y.a && x.b == y.b && x.c == y.c && x.d == y.d && x.e == y.e && x.f == y.f &&
    x.g == y.g && x.h == y.h && x.i == y.i

theorem R9.beq_iff {x y : R9} : x.beq y = true ↔ x = y := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := x
  obtain ⟨a', b', c', d', e', f', g', h', i'⟩ := y
  simp only [R9.beq, Bool.and_eq_true, beq_iff_eq, R9.mk.injEq]
  tauto

instance : DecidableEq R9 := fun _ _ => decidable_of_iff _ R9.beq_iff

@[expose] def rmul (x y : R9) : R9 :=
  ⟨x.a*y.a+x.b*y.d+x.c*y.g, x.a*y.b+x.b*y.e+x.c*y.h, x.a*y.c+x.b*y.f+x.c*y.i,
   x.d*y.a+x.e*y.d+x.f*y.g, x.d*y.b+x.e*y.e+x.f*y.h, x.d*y.c+x.e*y.f+x.f*y.i,
   x.g*y.a+x.h*y.d+x.i*y.g, x.g*y.b+x.h*y.e+x.i*y.h, x.g*y.c+x.h*y.f+x.i*y.i⟩

@[expose] def rone : R9 := ⟨1, 0, 0, 0, 1, 0, 0, 0, 1⟩

@[expose] def rdet (x : R9) : ZMod 3 :=
  x.a*x.e*x.i - x.a*x.f*x.h - x.b*x.d*x.i + x.b*x.f*x.g + x.c*x.d*x.h - x.c*x.e*x.g

@[expose] def ofMat (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) : R9 :=
  ⟨M 0 0, M 0 1, M 0 2, M 1 0, M 1 1, M 1 2, M 2 0, M 2 1, M 2 2⟩

theorem ofMat_mul (M N : Matrix (Fin 3) (Fin 3) (ZMod 3)) :
    ofMat (M * N) = rmul (ofMat M) (ofMat N) := by
  simp [ofMat, rmul, Matrix.mul_apply, Fin.sum_univ_three]

theorem ofMat_one : ofMat 1 = rone := by
  simp [ofMat, rone]

theorem ofMat_injective : Function.Injective ofMat := by
  intro M N h
  simp only [ofMat, R9.mk.injEq] at h
  obtain ⟨h00, h01, h02, h10, h11, h12, h20, h21, h22⟩ := h
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

theorem rdet_ofMat (M : Matrix (Fin 3) (Fin 3) (ZMod 3)) : rdet (ofMat M) = M.det := by
  rw [Matrix.det_fin_three]
  simp only [rdet, ofMat]

@[expose] def code (x : R9) : ℕ :=
  x.a.val + 3 * (x.b.val + 3 * (x.c.val + 3 * (x.d.val + 3 * (x.e.val + 3 * (x.f.val +
    3 * (x.g.val + 3 * (x.h.val + 3 * x.i.val)))))))

theorem val_lt_three (z : ZMod 3) : z.val < 3 := ZMod.val_lt z

theorem code_lt (x : R9) : code x < 19683 := by
  have := val_lt_three x.a; have := val_lt_three x.b; have := val_lt_three x.c
  have := val_lt_three x.d; have := val_lt_three x.e; have := val_lt_three x.f
  have := val_lt_three x.g; have := val_lt_three x.h; have := val_lt_three x.i
  unfold code
  omega

theorem code_injective : Function.Injective code := by
  rintro ⟨a, b, c, d, e, f, g, h, i⟩ ⟨a', b', c', d', e', f', g', h', i'⟩ hx
  have := val_lt_three a; have := val_lt_three b; have := val_lt_three c
  have := val_lt_three d; have := val_lt_three e; have := val_lt_three f
  have := val_lt_three g; have := val_lt_three h; have := val_lt_three i
  have := val_lt_three a'; have := val_lt_three b'; have := val_lt_three c'
  have := val_lt_three d'; have := val_lt_three e'; have := val_lt_three f'
  have := val_lt_three g'; have := val_lt_three h'; have := val_lt_three i'
  simp only [code] at hx
  simp only [R9.mk.injEq]
  refine ⟨ZMod.val_injective _ ?_, ZMod.val_injective _ ?_, ZMod.val_injective _ ?_,
    ZMod.val_injective _ ?_, ZMod.val_injective _ ?_, ZMod.val_injective _ ?_,
    ZMod.val_injective _ ?_, ZMod.val_injective _ ?_, ZMod.val_injective _ ?_⟩ <;> omega

@[expose] def vals : List (ZMod 3) := [0, 1, 2]

@[expose] def allR9 : List R9 :=
  vals.flatMap fun a => vals.flatMap fun b => vals.flatMap fun c =>
  vals.flatMap fun d => vals.flatMap fun e => vals.flatMap fun f =>
  vals.flatMap fun g => vals.flatMap fun h => vals.map fun i => ⟨a, b, c, d, e, f, g, h, i⟩

theorem mem_allR9 (r : R9) : r ∈ allR9 := by
  obtain ⟨a, b, c, d, e, f, g, h, i⟩ := r
  have hv : ∀ z : ZMod 3, z ∈ vals := by decide
  simp only [allR9, List.mem_flatMap, List.mem_map]
  exact ⟨a, hv a, b, hv b, c, hv c, d, hv d, e, hv e, f, hv f, g, hv g, h, hv h, i, hv i, rfl⟩

abbrev Tree : Type := Array (R9 × ℕ × ℕ)

@[expose] def bfs (gs : List R9) : Tree := Id.run do
  let gens := gs.toArray
  let mut seen : Array Bool := Array.replicate 19683 false
  let mut out : Tree := #[(rone, 0, 0)]
  seen := seen.set! (code rone) true
  let mut idx := 0
  for _ in [0:19683] do
    if idx < out.size then
      let x := out[idx]!.1
      for k in [0:gens.size] do
        let y := rmul gens[k]! x
        if !seen[code y]! then
          seen := seen.set! (code y) true
          out := out.push (y, idx, k)
      idx := idx + 1
  return out

@[expose] def treeOK (gs : List R9) (T : Tree) : Bool :=
  decide (0 < T.size) && T[0]!.1 == rone &&
    (List.range T.size).all fun k => k == 0 ||
      (decide (T[k]!.2.1 < k) && decide (T[k]!.2.2 < gs.length) &&
        T[k]!.1 == rmul (gs.getD T[k]!.2.2 rone) T[T[k]!.2.1]!.1)

section Sound

variable {G : Type*} [Group G] (f : G → R9) (hmul : ∀ x y, f (x * y) = rmul (f x) (f y))
  (hone : f 1 = rone)
include hmul hone

theorem tree_mem (gs : List G) {T : Tree} (hT : treeOK (gs.map f) T = true) :
    ∀ k < T.size, ∃ x ∈ Subgroup.closure {y | y ∈ gs}, f x = T[k]!.1 := by
  simp only [treeOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range, Bool.or_eq_true] at hT
  obtain ⟨⟨_, hroot⟩, hstep⟩ := hT
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases hstep k hk with h0 | ⟨⟨hp, hj⟩, hx⟩
    · subst h0
      exact ⟨1, Subgroup.one_mem _, by rw [hone, hroot]⟩
    · obtain ⟨x', hx'mem, hx'⟩ := ih _ hp (lt_trans hp hk)
      rw [List.length_map] at hj
      refine ⟨gs[T[k]!.2.2] * x', Subgroup.mul_mem _ (Subgroup.subset_closure ?_) hx'mem, ?_⟩
      · exact List.getElem_mem hj
      · rw [hmul, hx', hx, List.getD_eq_getElem _ _ (by rw [List.length_map]; exact hj),
          List.getElem_map]

end Sound

@[expose] def slCodes : List ℕ :=
  ((allR9.filter fun r => rdet r == 1).map code).mergeSort fun m n => m ≤ n

@[expose] def slCover (gs : List R9) : Bool :=
  let T := bfs gs
  treeOK gs T && ((T.toList.map fun e => code e.1).mergeSort fun m n => m ≤ n) == slCodes

theorem exists_of_slCover {gs : List R9} (h : slCover gs = true) {r : R9} (hr : rdet r = 1) :
    ∃ k < (bfs gs).size, (bfs gs)[k]!.1 = r := by
  simp only [slCover, Bool.and_eq_true, beq_iff_eq] at h
  have hc : code r ∈ slCodes := by
    rw [slCodes, List.mem_mergeSort, List.mem_map]
    exact ⟨r, List.mem_filter.2 ⟨mem_allR9 r, by simp [hr]⟩, rfl⟩
  rw [← h.2, List.mem_mergeSort, List.mem_map] at hc
  obtain ⟨e, he, hec⟩ := hc
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 he
  rw [Array.length_toList] at hk
  refine ⟨k, hk, code_injective ?_⟩
  rw [← hec, Array.getElem_toList, getElem!_pos (bfs gs) k hk]

theorem treeOK_of_slCover {gs : List R9} (h : slCover gs = true) : treeOK gs (bfs gs) = true := by
  simp only [slCover, Bool.and_eq_true] at h
  exact h.1

theorem statedSL_le_closure (gs : List (GL (Fin 3) (ZMod 3)))
    (h : slCover (gs.map fun x : GL (Fin 3) (ZMod 3) =>
      ofMat (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) = true) :
    CFSG.Assembly.LowTwoRank.StatedSL 3 (ZMod 3) ≤ Subgroup.closure {y | y ∈ gs} := by
  have hmul : ∀ x y : GL (Fin 3) (ZMod 3), ofMat ((x * y : GL (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) = rmul (ofMat x) (ofMat y) := fun x y => by
    rw [Units.val_mul, ofMat_mul]
  have hone : ofMat ((1 : GL (Fin 3) (ZMod 3)) : Matrix (Fin 3) (Fin 3) (ZMod 3)) = rone := by
    rw [Units.val_one, ofMat_one]
  rw [CFSG.Assembly.LowTwoRank.StatedSL, Subgroup.closure_le]
  intro x hx
  obtain ⟨k, hk, hkx⟩ := exists_of_slCover h (r := ofMat x) (by rw [rdet_ofMat]; exact hx)
  obtain ⟨y, hy, hyx⟩ := tree_mem (fun x : GL (Fin 3) (ZMod 3) =>
    ofMat (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) hmul hone gs (treeOK_of_slCover h) k hk
  have : y = x := Units.ext (ofMat_injective (hyx.trans hkx))
  rw [← this]
  exact hy

theorem closure_eq_top_SL (gs : List (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)))
    (h : slCover (gs.map fun x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) =>
      ofMat (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) = true) :
    Subgroup.closure {y | y ∈ gs} = ⊤ := by
  have hmul : ∀ x y : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3),
      ofMat ((x * y : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :
        Matrix (Fin 3) (Fin 3) (ZMod 3)) = rmul (ofMat x) (ofMat y) := fun x y => by
    rw [Matrix.SpecialLinearGroup.coe_mul, ofMat_mul]
  have hone : ofMat ((1 : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) :
      Matrix (Fin 3) (Fin 3) (ZMod 3)) = rone := by
    rw [Matrix.SpecialLinearGroup.coe_one, ofMat_one]
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk, hkx⟩ := exists_of_slCover h (r := ofMat x) (by rw [rdet_ofMat]; exact x.2)
  obtain ⟨y, hy, hyx⟩ := tree_mem (fun x : Matrix.SpecialLinearGroup (Fin 3) (ZMod 3) =>
    ofMat (x : Matrix (Fin 3) (Fin 3) (ZMod 3))) hmul hone gs (treeOK_of_slCover h) k hk
  have : y = x := Subtype.ext (ofMat_injective (hyx.trans hkx))
  rw [← this]
  exact hy

end CFSG.RankThree.PartTwo.Toolkit.Raw
