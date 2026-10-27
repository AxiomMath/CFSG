module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFamJ4M2Om
public import Certificates.Data.CFSGNative.J4ZCent.Check

public section

namespace CFSG.Quasithin.J4ZCent

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.Native CFSG.Sporadic.J4.ZCent
open CFSG.Sporadic.J4.QT (Mx)
open scoped commutatorElement

@[expose] def letterOf {G : Type*} [Group G] (gens : ℕ → G) (l : ℤ) : G :=
  if 0 < l then gens (l.toNat - 1) else (gens ((-l).toNat - 1))⁻¹

@[expose] def evalW {G : Type*} [Group G] (gens : ℕ → G) (w : List ℤ) : G :=
  (w.map (letterOf gens)).prod

section Words

variable {G : Type*} [Group G] (gens : ℕ → G)

theorem evalW_nil : evalW gens [] = 1 := rfl

theorem evalW_cons (l : ℤ) (w : List ℤ) : evalW gens (l :: w) = letterOf gens l * evalW gens w := by
  simp [evalW]

theorem evalW_append (w w' : List ℤ) : evalW gens (w ++ w') = evalW gens w * evalW gens w' := by
  simp [evalW]

theorem letterOf_neg {l : ℤ} (hl : l ≠ 0) : letterOf gens (-l) = (letterOf gens l)⁻¹ := by
  rcases lt_or_gt_of_ne hl with h | h
  · have h1 : ¬ 0 < l := by omega
    have h2 : 0 < -l := by omega
    unfold letterOf
    simp only [h1, h2, ↓reduceIte, inv_inv]
  · have h1 : ¬ 0 < -l := by omega
    unfold letterOf
    simp only [h, h1, ↓reduceIte, neg_neg]

theorem evalW_invW {w : List ℤ} (hw : ∀ l ∈ w, l ≠ 0) : evalW gens (invW w) = (evalW gens w)⁻¹ := by
  induction w with
  | nil => simp [invW, evalW]
  | cons l w ih =>
    have hl : l ≠ 0 := hw l List.mem_cons_self
    have hw' : ∀ l' ∈ w, l' ≠ 0 := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have h1 : invW (l :: w) = invW w ++ [-l] := by simp [invW]
    rw [h1, evalW_append, ih hw', evalW_cons gens (-l) [], letterOf_neg gens hl, evalW_cons,
      mul_inv_rev]
    simp [evalW_nil]

theorem evalW_commW {x y : List ℤ} (hx : ∀ l ∈ x, l ≠ 0) (hy : ∀ l ∈ y, l ≠ 0) :
    evalW gens (commW x y) = ⁅evalW gens x, evalW gens y⁆ := by
  rw [commW, evalW_append, evalW_append, evalW_append, evalW_invW gens hx, evalW_invW gens hy,
    commutatorElement_def]

@[expose] def WordOK (k : ℕ) (w : List ℤ) : Prop := ∀ l ∈ w, l ≠ 0 ∧ l.natAbs ≤ k

theorem WordOK.ne_zero {k : ℕ} {w : List ℤ} (h : WordOK k w) : ∀ l ∈ w, l ≠ 0 :=
  fun l hl => (h l hl).1

theorem letterOf_mem {H : Subgroup G} {k : ℕ} (hH : ∀ n < k, gens n ∈ H) {l : ℤ} (hl : l ≠ 0)
    (hk : l.natAbs ≤ k) : letterOf gens l ∈ H := by
  unfold letterOf
  split_ifs with h
  · exact hH _ (by omega)
  · exact Subgroup.inv_mem _ (hH _ (by omega))

theorem mem_of_evalW {H : Subgroup G} {k : ℕ} (hH : ∀ n < k, gens n ∈ H) {w : List ℤ}
    (hw : WordOK k w) : evalW gens w ∈ H := by
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons l w ih =>
    rw [evalW_cons]
    exact Subgroup.mul_mem _ (letterOf_mem gens hH (hw l List.mem_cons_self).1
      (hw l List.mem_cons_self).2)
      (ih fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))

theorem WordOK.invW {k : ℕ} {w : List ℤ} (h : WordOK k w) : WordOK k (invW w) := by
  intro l hl
  simp only [CFSG.Sporadic.J4.ZCent.invW, List.mem_map, List.mem_reverse] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  have := h l' hl'
  exact ⟨by omega, by simpa using this.2⟩

theorem WordOK.append {k : ℕ} {w w' : List ℤ} (h : WordOK k w) (h' : WordOK k w') :
    WordOK k (w ++ w') := by
  intro l hl
  rcases List.mem_append.1 hl with hl | hl
  · exact h l hl
  · exact h' l hl

theorem WordOK.commW {k : ℕ} {x y : List ℤ} (hx : WordOK k x) (hy : WordOK k y) :
    WordOK k (commW x y) :=
  ((hx.append hy).append hx.invW).append hy.invW

theorem evalW_perfWord_mem {H : Subgroup G} {k : ℕ} (hH : ∀ n < k, gens n ∈ H) :
    ∀ l : List (List ℤ × List ℤ), (∀ p ∈ l, WordOK k p.1 ∧ WordOK k p.2) →
      evalW gens (perfWord l) ∈ ⁅H, H⁆ := by
  intro l
  induction l with
  | nil => intro _; simp [perfWord, evalW_nil]
  | cons p l ih =>
    intro hl
    have hp := hl p List.mem_cons_self
    have h1 : perfWord (p :: l) = commW p.1 p.2 ++ perfWord l := by simp [perfWord]
    rw [h1, evalW_append, evalW_commW gens hp.1.ne_zero hp.2.ne_zero]
    refine Subgroup.mul_mem _ ?_ (ih fun q hq => hl q (List.mem_cons_of_mem _ hq))
    exact Subgroup.commutator_mem_commutator (mem_of_evalW gens hH hp.1)
      (mem_of_evalW gens hH hp.2)

end Words

section Matrices

theorem wfR_mulT {X Y : Array V2} (hX : wfR X = true) (hY : wfR Y = true) :
    wfR (mulT X (frTable Y)) = true :=
  CFSG.Sporadic.J4.QT2A.wfR_mulRows hX hY

theorem wfR_idRows : wfR idRows = true := CFSG.Sporadic.J4.QT2A.wfR_idRows

theorem wfR_invRows (X : Array V2) : wfR (invRows X) = true := CFSG.Quasithin.J4M2.Om.wfR_invRows X

theorem rowsMatrix_mulT (X Y : Array V2) :
    rowsMatrix (mulT X (frTable Y)) = rowsMatrix X * rowsMatrix Y := rowsMatrix_mulRows X Y

theorem getElem!_map_frTable {m : Array (Array V2)} {n : ℕ} (hn : n < m.size) :
    (m.map frTable)[n]! = frTable m[n]! := by
  rw [getElem!_pos (m.map frTable) n (by simpa using hn), getElem!_pos m n hn]
  simp

theorem rowsMatrix_foldl_wordT {gens : ℕ → J} {m mi : Array (Array V2)}
    (hm : ∀ n < m.size, Mx (gens n) = rowsMatrix m[n]!)
    (hmi : ∀ n < m.size, Mx (gens n)⁻¹ = rowsMatrix mi[n]!)
    (hmw : ∀ n < m.size, wfR m[n]! = true) (hmiw : ∀ n < m.size, wfR mi[n]! = true)
    (hs : mi.size = m.size) :
    ∀ (w : List ℤ), WordOK m.size w → ∀ (acc : Array V2) (x : J), wfR acc = true →
      rowsMatrix acc = Mx x →
      wfR (w.foldl (fun (acc : Array V2) (l : ℤ) =>
        mulT acc (if 0 < l then (m.map frTable)[l.toNat - 1]!
          else (mi.map frTable)[(-l).toNat - 1]!)) acc) = true ∧
      rowsMatrix (w.foldl (fun (acc : Array V2) (l : ℤ) =>
        mulT acc (if 0 < l then (m.map frTable)[l.toNat - 1]!
          else (mi.map frTable)[(-l).toNat - 1]!)) acc) = Mx (x * evalW gens w) := by
  intro w
  induction w with
  | nil =>
    intro _ acc x hacc hmat
    simp only [List.foldl_nil, evalW_nil, mul_one]
    exact ⟨hacc, hmat⟩
  | cons l w ih =>
    intro hw acc x hacc hmat
    have hl := hw l List.mem_cons_self
    have hw' : WordOK m.size w := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    simp only [List.foldl_cons, evalW_cons]
    by_cases h : 0 < l
    · have hn : l.toNat - 1 < m.size := by omega
      simp only [h, ↓reduceIte, getElem!_map_frTable hn]
      have := ih hw' (mulT acc (frTable m[l.toNat - 1]!)) (x * gens (l.toNat - 1))
        (wfR_mulT hacc (hmw _ hn))
        (by rw [rowsMatrix_mulT, hmat, ← hm _ hn, map_mul])
      simpa [letterOf, h, mul_assoc] using this
    · have hn : (-l).toNat - 1 < mi.size := by omega
      have hn' : (-l).toNat - 1 < m.size := by omega
      simp only [h, ↓reduceIte, getElem!_map_frTable hn]
      have := ih hw' (mulT acc (frTable mi[(-l).toNat - 1]!)) (x * (gens ((-l).toNat - 1))⁻¹)
        (wfR_mulT hacc (hmiw _ hn'))
        (by rw [rowsMatrix_mulT, hmat, ← hmi _ hn', map_mul])
      simpa [letterOf, h, mul_assoc] using this

theorem rowsMatrix_wordT {gens : ℕ → J} {m mi : Array (Array V2)}
    (hm : ∀ n < m.size, Mx (gens n) = rowsMatrix m[n]!)
    (hmi : ∀ n < m.size, Mx (gens n)⁻¹ = rowsMatrix mi[n]!)
    (hmw : ∀ n < m.size, wfR m[n]! = true) (hmiw : ∀ n < m.size, wfR mi[n]! = true)
    (hs : mi.size = m.size) {w : List ℤ} (hw : WordOK m.size w) :
    wfR (wordT (m.map frTable) (mi.map frTable) w) = true ∧
      rowsMatrix (wordT (m.map frTable) (mi.map frTable) w) = Mx (evalW gens w) := by
  have := rowsMatrix_foldl_wordT hm hmi hmw hmiw hs w hw idRows 1 wfR_idRows
    (by rw [rowsMatrix_idRows, map_one])
  simpa [wordT] using this

end Matrices

end CFSG.Quasithin.J4ZCent
