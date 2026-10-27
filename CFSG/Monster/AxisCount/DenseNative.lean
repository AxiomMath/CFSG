module

public import Certificates.Data.CFSGNative.MonsterAxis.Dense
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Abs
public import Mathlib.Tactic.NormNum.DivMod
public import Mathlib.Tactic.NormNum.OfScientific
public import Mathlib.Tactic.Ring.RingNF

public section

namespace CFSG.Monster.AxisCount.Native

open CFSG.Monster.B.Rep4371.Native (sumRange)

theorem getElem!_eq_getD' (D : Array Int) (k : Nat) : D[k]! = D.getD k 0 := by
  rw [Array.getElem!_eq_getD]
  rfl

theorem getElem!_eq_getD_gen {α : Type} [Inhabited α] (D : Array α) (k : Nat) :
    D[k]! = D.getD k default := by
  rw [Array.getElem!_eq_getD]

theorem getD_ofFn {α : Type} {n : Nat} (f : Fin n → α) (i : Nat) (hi : i < n) (d : α) :
    (Array.ofFn f).getD i d = f ⟨i, hi⟩ := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
  simp [hi]

theorem getD_modify (xs : Array Int) (i j : Nat) (f : Int → Int) (hi : i < xs.size) :
    (xs.modify i f).getD j 0 = if i = j then f (xs.getD i 0) else xs.getD j 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : i = j
  · subst h
    simp [Array.getD_eq_getD_getElem?, hi]
  · simp [h, Array.getD_eq_getD_getElem?]

theorem sumRange_eq (f : Nat → Int) (n : Nat) : sumRange f n = ∑ k ∈ Finset.range n, f k := by
  induction n with
  | zero => simp [sumRange]
  | succ n ih => rw [sumRange, ih, Finset.sum_range_succ]

theorem inner_fold (n : Nat) (x : Int) (q : Nat) (hq : q < n) (L : List (Nat × Int)) :
    ∀ out : Array Int, out.size = n →
      (L.foldl (fun out' t => if t.1 < n then out'.modify t.1 (fun y => y + t.2 * x) else out')
        out).size = n ∧
      (L.foldl (fun out' t => if t.1 < n then out'.modify t.1 (fun y => y + t.2 * x) else out')
        out).getD q 0 = out.getD q 0 + (L.map fun t => if t.1 = q then t.2 * x else 0).sum := by
  induction L with
  | nil => intro out h; exact ⟨h, by simp⟩
  | cons t L ih =>
    intro out h
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    have hs : (if t.1 < n then out.modify t.1 (fun y => y + t.2 * x) else out).size = n := by
      split_ifs <;> simp [h]
    obtain ⟨h1, h2⟩ := ih _ hs
    refine ⟨h1, ?_⟩
    rw [h2]
    by_cases ht : t.1 < n
    · rw [ite_eq_left ht, getD_modify _ _ _ _ (by omega)]
      by_cases htq : t.1 = q
      · subst htq
        simp only [ite_true]
        ring
      · simp only [htq, ite_false]
        ring
    · have htq : t.1 ≠ q := by omega
      simp only [ite_eq_right ht, htq, ite_false]
      ring

theorem outer_fold (off n : Nat) (T : Nat → List (Nat × Int)) (D : Array Int) (q : Nat)
    (hq : q < n) :
    ∀ (m : Nat) (out : Array Int), out.size = n →
      ((List.range m).foldl (fun out p =>
          if D[off + p]! == 0 then out
          else (T p).foldl (fun out' t =>
            if t.1 < n then out'.modify t.1 (fun y => y + t.2 * D[off + p]!) else out') out)
        out).size = n ∧
      ((List.range m).foldl (fun out p =>
          if D[off + p]! == 0 then out
          else (T p).foldl (fun out' t =>
            if t.1 < n then out'.modify t.1 (fun y => y + t.2 * D[off + p]!) else out') out)
        out).getD q 0 = out.getD q 0 +
          ∑ p ∈ Finset.range m,
            ((T p).map fun t => if t.1 = q then t.2 * D.getD (off + p) 0 else 0).sum := by
  intro m
  induction m with
  | zero => intro out h; exact ⟨h, by simp⟩
  | succ m ih =>
    intro out h
    obtain ⟨h1, h2⟩ := ih out h
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Finset.sum_range_succ]
    by_cases hx : D[off + m]! = 0
    · have hx' : D.getD (off + m) 0 = 0 := by rw [← getElem!_eq_getD']; exact hx
      simp only [hx, beq_self_eq_true, ite_true]
      refine ⟨h1, ?_⟩
      rw [h2]
      have : ((T m).map fun t => if t.1 = q then t.2 * D.getD (off + m) 0 else 0).sum = 0 := by
        rw [hx']
        induction (T m) with
        | nil => rfl
        | cons t L ihL => simp_all
      rw [this, add_zero]
    · have hb : (D[off + m]! == 0) = false := by simpa using hx
      simp only [hb, Bool.false_eq_true, ite_false]
      obtain ⟨h3, h4⟩ := inner_fold n D[off + m]! q hq (T m) _ h1
      refine ⟨h3, ?_⟩
      rw [h4, h2, getElem!_eq_getD', add_assoc]

theorem scatterAt_size (off n : Nat) (T : Nat → List (Nat × Int)) (D : Array Int) :
    (scatterAt off n T D).size = n := by
  by_cases hn : n = 0
  · subst hn
    simp [scatterAt]
  · have := (outer_fold off n T D 0 (by omega) n (Array.replicate n 0) (by simp)).1
    exact this

theorem scatterAt_getD (off n : Nat) (T : Nat → List (Nat × Int)) (D : Array Int) (q : Nat)
    (hq : q < n) :
    (scatterAt off n T D).getD q 0 =
      ∑ p ∈ Finset.range n,
        ((T p).map fun t => if t.1 = q then t.2 * D.getD (off + p) 0 else 0).sum := by
  have h := (outer_fold off n T D q hq n (Array.replicate n 0) (by simp)).2
  unfold scatterAt
  simpa [Array.getD_eq_getD_getElem?, Array.getElem?_replicate, hq] using h

theorem mmA_size (P Q : Array Int) : (mmA P Q).size = 576 := by simp [mmA]

theorem trA_size (P : Array Int) : (trA P).size = 576 := by simp [trA]

theorem mmA_getD (P Q : Array Int) (i j : Nat) (hi : i < 24) (hj : j < 24) :
    (mmA P Q).getD (i * 24 + j) 0 =
      ∑ k ∈ Finset.range 24, P.getD (i * 24 + k) 0 * Q.getD (k * 24 + j) 0 := by
  have h : i * 24 + j < 576 := by omega
  have e1 : (i * 24 + j) / 24 = i := by omega
  have e2 : (i * 24 + j) % 24 = j := by omega
  unfold mmA
  rw [getD_ofFn _ _ h, sumRange_eq]
  simp only [e1, e2, getElem!_eq_getD']

theorem trA_getD (P : Array Int) (i j : Nat) (hi : i < 24) (hj : j < 24) :
    (trA P).getD (i * 24 + j) 0 = P.getD (j * 24 + i) 0 := by
  have h : i * 24 + j < 576 := by omega
  have e1 : (i * 24 + j) / 24 = i := by omega
  have e2 : (i * 24 + j) % 24 = j := by omega
  unfold trA
  rw [getD_ofFn _ _ h]
  simp only [e1, e2, getElem!_eq_getD']

theorem aFull_getD (D : Array Int) (i j : Nat) (hi : i < 24) (hj : j < 24) :
    (aFull D).getD (i * 24 + j) 0 = D.getD (aIdx i j) 0 := by
  have h : i * 24 + j < 576 := by omega
  have e1 : (i * 24 + j) / 24 = i := by omega
  have e2 : (i * 24 + j) % 24 = j := by omega
  unfold aFull
  rw [getD_ofFn _ _ h]
  simp only [e1, e2, getElem!_eq_getD']

theorem aIdx_comm (i j : Nat) : aIdx i j = aIdx j i := by
  unfold aIdx
  by_cases h : i = j
  · subst h; rfl
  · have h' : j ≠ i := fun e => h e.symm
    rw [ite_eq_right h, ite_eq_right h', min_comm, max_comm]

theorem latA_aIdx_aux (G D : Array Int) (i j : Nat) (hi : i < 24) (hj : j < 24) :
    (mmA (trA G) (mmA (aFull D) G)).getD (i * 24 + j) 0 =
      ∑ k ∈ Finset.range 24, ∑ l ∈ Finset.range 24,
        G.getD (k * 24 + i) 0 * D.getD (aIdx k l) 0 * G.getD (l * 24 + j) 0 := by
  rw [mmA_getD _ _ i j hi hj]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k < 24 := Finset.mem_range.1 hk
  rw [trA_getD _ _ _ hi hk', mmA_getD _ _ k j hk' hj, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l < 24 := Finset.mem_range.1 hl
  rw [aFull_getD _ _ _ hk' hl']
  ring

theorem wMul_size (G D : Array Int) : (wMul G D).size = 98304 := by simp [wMul]

theorem wMul_getD (G D : Array Int) (r j : Nat) (hr : r < 4096) (hj : j < 24) :
    (wMul G D).getD (r * 24 + j) 0 =
      ∑ k ∈ Finset.range 24, D.getD (98580 + r * 24 + k) 0 * G.getD (k * 24 + j) 0 := by
  have h : r * 24 + j < 98304 := by omega
  have e1 : (r * 24 + j) / 24 = r := by omega
  have e2 : (r * 24 + j) % 24 = j := by omega
  unfold wMul
  rw [getD_ofFn _ _ h, sumRange_eq]
  simp only [e1, e2, getElem!_eq_getD']

theorem scale_size (f : Nat) (A : Array Int) : (scale f A).size = A.size := by simp [scale]

theorem scale_getD (f : Nat) (A : Array Int) (k : Nat) (hk : k < A.size) :
    (scale f A).getD k 0 = A.getD k 0 * 2 ^ f := by
  simp [scale, Array.getD_eq_getD_getElem?, hk]

theorem latA_size (G D : Array Int) : (latA G D).size = 300 := by simp [latA]

theorem getD_append3 (A X W : Array Int) (hA : A.size = 300) (hX : X.size = 98280) (k : Nat) :
    (A ++ X ++ W).getD k 0 =
      if k < 300 then A.getD k 0
      else if k < 98580 then X.getD (k - 300) 0 else W.getD (k - 98580) 0 := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append, Array.getElem?_append]
  simp only [Array.size_append, hA, hX]
  by_cases h1 : k < 300
  · have : k < 300 + 98280 := by omega
    simp [h1, this, Array.getD_eq_getD_getElem?]
  · by_cases h2 : k < 98580
    · have : k < 300 + 98280 := by omega
      simp [h1, h2, Array.getD_eq_getD_getElem?]
    · simp [h1, h2, Array.getD_eq_getD_getElem?]

theorem applyGD_e (c : Ctx) (g : GD) (v : DVec) : (applyGD c g v).e = v.e + g.eNew := rfl

theorem applyGD_getD (c : Ctx) (g : GD) (v : DVec) (k : Nat) :
    (applyGD c g v).D.getD k 0 =
      if k < 300 then (latA g.G v.D).getD k 0 * 2 ^ (g.eNew - 2 * g.latS)
      else if k < 98580 then
        (scatterAt 300 98280 (g.xT c) v.D).getD (k - 300) 0 * 2 ^ g.eNew
      else (scatterAt 0 98304 g.wT (wMul g.G v.D)).getD (k - 98580) 0 *
        2 ^ (g.eNew - g.latS - g.rowS) := by
  show (scale _ (latA g.G v.D) ++ scale _ (scatterAt 300 98280 (g.xT c) v.D) ++
    scale _ (scatterAt 0 98304 g.wT (wMul g.G v.D))).getD k 0 = _
  rw [getD_append3 _ _ _ (by rw [scale_size, latA_size]) (by rw [scale_size, scatterAt_size])]
  by_cases h1 : k < 300
  · rw [ite_eq_left h1, ite_eq_left h1, scale_getD _ _ _ (by rw [latA_size]; exact h1)]
  · by_cases h2 : k < 98580
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2,
        scale_getD _ _ _ (by rw [scatterAt_size]; omega)]
    · by_cases h3 : k - 98580 < 98304
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2,
          scale_getD _ _ _ (by rw [scatterAt_size]; exact h3)]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2]
        have : ¬ k - 98580 < (scale (g.eNew - g.latS - g.rowS)
            (scatterAt 0 98304 g.wT (wMul g.G v.D))).size := by
          rw [scale_size, scatterAt_size]; exact h3
        simp [scale, Array.getD_eq_getD_getElem?, scatterAt_size, h3]

end CFSG.Monster.AxisCount.Native
