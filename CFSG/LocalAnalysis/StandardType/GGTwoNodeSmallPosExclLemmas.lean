module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallSem
public import CFSG.Sporadic.HNSchreier.Algebra
public import CFSG.Sporadic.He.Setup
public import Certificates.Data.CFSGNative.TwoNodeSmall.CorePos

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def pxe_A (p n : ℕ) : Matrix (Fin n) (Fin n) (ZMod p) :=
  fun i j => (CartanMatrix.A n i j : ZMod p)

lemma pxe_ker4 (a : Fin 4 → ZMod 5) (ha : (pxe_A 5 4).mulVec a = 0) :
    ∃ m : ZMod 5, a = fun i : Fin 4 => m * (((i : ℕ) + 1 : ℕ) : ZMod 5) := by
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  simp [pxe_A, Matrix.mulVec, dotProduct, Fin.sum_univ_four, CartanMatrix.A] at h0 h1 h2
  refine ⟨a 0, ?_⟩
  have ha1 : a 1 = 2 * a 0 := by linear_combination -h0
  have ha2 : a 2 = 3 * a 0 := by
    rw [ha1] at h1
    linear_combination -h1
  have ha3 : a 3 = 4 * a 0 := by
    rw [ha1, ha2] at h2
    linear_combination -h2
  funext i
  fin_cases i
  · simp
  · simpa [mul_comm] using ha1
  · simpa [mul_comm] using ha2
  · simpa [mul_comm] using ha3

lemma pxe_ker6 (a : Fin 6 → ZMod 7) (ha : (pxe_A 7 6).mulVec a = 0) :
    ∃ m : ZMod 7, a = fun i : Fin 6 => m * (((i : ℕ) + 1 : ℕ) : ZMod 7) := by
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  have h2 := congrFun ha 2
  have h3 := congrFun ha 3
  have h4 := congrFun ha 4
  simp [pxe_A, Matrix.mulVec, dotProduct, Fin.sum_univ_six, CartanMatrix.A] at h0 h1 h2 h3 h4
  refine ⟨a 0, ?_⟩
  have ha1 : a 1 = 2 * a 0 := by linear_combination -h0
  have ha2 : a 2 = 3 * a 0 := by
    rw [ha1] at h1
    linear_combination -h1
  have ha3 : a 3 = 4 * a 0 := by
    rw [ha1, ha2] at h2
    linear_combination -h2
  have ha4 : a 4 = 5 * a 0 := by
    rw [ha2, ha3] at h3
    linear_combination -h3
  have ha5 : a 5 = 6 * a 0 := by
    rw [ha3, ha4] at h4
    linear_combination -h4
  funext i
  fin_cases i
  · simp
  · simpa [mul_comm] using ha1
  · simpa [mul_comm] using ha2
  · simpa [mul_comm] using ha3
  · simpa [mul_comm] using ha4
  · simpa [mul_comm] using ha5

lemma pxe_ker_cartan (p n : ℕ) (hp : p = 5 ∨ p = 7) (hn : n = p - 1)
    (a : Fin n → ZMod p) (ha : (pxe_A p n).mulVec a = 0) :
    ∃ m : ZMod p, a = fun i : Fin n => m * (((i : ℕ) + 1 : ℕ) : ZMod p) := by
  rcases hp with rfl | rfl
  · have hn' : n = 4 := by omega
    subst hn'
    exact pxe_ker4 a ha
  · have hn' : n = 6 := by omega
    subst hn'
    exact pxe_ker6 a ha

lemma pxe_symm (p n : ℕ) (i j : Fin n) :
    pxe_A p n i j = pxe_A p n j i := by
  have h : CartanMatrix.A n i j = CartanMatrix.A n j i := by
    simp only [CartanMatrix.A, Matrix.of_apply]
    by_cases hij : i = j
    · subst hij; simp
    · have hji : ¬ (j = i) := fun hh => hij hh.symm
      rw [if_neg hij, if_neg hji]
      by_cases h1 : i.val + 1 = j.val ∨ j.val + 1 = i.val
      · have h2 : j.val + 1 = i.val ∨ i.val + 1 = j.val := h1.symm
        rw [if_pos h1, if_pos h2]
      · have h2 : ¬ (j.val + 1 = i.val ∨ i.val + 1 = j.val) := fun hh => h1 hh.symm
        rw [if_neg h1, if_neg h2]
  exact congrArg (fun z : ℤ => (z : ZMod p)) h

lemma pxe_zA (p n : ℕ) (hp : p = 5 ∨ p = 7) (hn : n = p - 1) :
    (pxe_A p n).mulVec (fun i : Fin n => (((i : ℕ) + 1 : ℕ) : ZMod p)) = 0 := by
  rcases hp with rfl | rfl
  · have hn' : n = 4 := by omega
    subst hn'
    decide
  · have hn' : n = 6 := by omega
    subst hn'
    decide

lemma pxe_noPreimage (p n : ℕ) (hp : p = 5 ∨ p = 7) (hn : n = p - 1)
    (m : Fin n → ZMod p) :
    (pxe_A p n).mulVec m ≠ Pi.single (⟨0, by omega⟩ : Fin n) (1 : ZMod p) := by
  intro h
  have hz := pxe_zA p n hp hn
  have hswap : (∑ i : Fin n, (((i : ℕ) + 1 : ℕ) : ZMod p) * ((pxe_A p n).mulVec m) i)
      = ∑ j : Fin n, ((pxe_A p n).mulVec (fun i : Fin n => (((i : ℕ) + 1 : ℕ) : ZMod p))) j * m j := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    rw [pxe_symm p n j i]
    ring
  have hzero : (∑ i : Fin n, (((i : ℕ) + 1 : ℕ) : ZMod p) * ((pxe_A p n).mulVec m) i) = 0 := by
    rw [hswap, hz]
    simp
  rw [h] at hzero
  have hsingle : (∑ i : Fin n, (((i : ℕ) + 1 : ℕ) : ZMod p)
      * (Pi.single (⟨0, by omega⟩ : Fin n) (1 : ZMod p) : Fin n → ZMod p) i) = 1 := by
    rw [Finset.sum_eq_single (⟨0, by omega⟩ : Fin n)]
    · simp
    · intro b _ hb; simp [Pi.single_eq_of_ne hb]
    · intro hh; exact absurd (Finset.mem_univ _) hh
  rw [hsingle] at hzero
  haveI : Fact p.Prime := by
    rcases hp with hp5 | hp7
    · rw [hp5]; exact ⟨by norm_num⟩
    · rw [hp7]; exact ⟨by norm_num⟩
  exact one_ne_zero hzero

lemma pxe_mem_allVecsP (p : ℕ) : ∀ (n : ℕ) (v : Vec),
    v ∈ allVecsP p n ↔ v.length = n ∧ ∀ x ∈ v, x < p
  | 0, v => by
      simp only [allVecsP, List.mem_singleton]
      constructor
      · rintro rfl; simp
      · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.1 h
  | n + 1, v => by
      constructor
      · intro hv
        simp only [allVecsP, List.mem_flatMap, List.mem_map, List.mem_range] at hv
        rcases hv with ⟨w, hw, a, ha, rfl⟩
        rw [pxe_mem_allVecsP p n] at hw
        refine ⟨by simp [hw.1], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact ha
        · exact hw.2 x hx
      · rintro ⟨hlen, hlt⟩
        cases v with
        | nil => simp at hlen
        | cons a v' =>
          simp only [allVecsP, List.mem_flatMap, List.mem_map, List.mem_range]
          refine ⟨v', ?_, a, hlt a (by simp), rfl⟩
          rw [pxe_mem_allVecsP p n]
          exact ⟨by simpa using hlen, fun x hx => hlt x (by simp [hx])⟩

lemma pxe_getD_map_range' {α : Type} (f : ℕ → α) (d : α) {n : ℕ} (i : Fin n) :
    ((List.range n).map f).getD i.val d = f i.val := by
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

lemma pxe_getD_append_last {α : Type} {l : List α} {z : α} {d : α} {n : ℕ}
    (h : n = l.length) : (l ++ [z]).getD n d = z := by
  subst h
  rw [List.getD_append_right l [z] d l.length (by simp)]
  simp

lemma pxe_vec_unitP (P : Pt) (i : Fin P.D) :
    P.vec (unitP P.D i.val) = (Pi.single i (1 : ZMod P.p) : Fin P.D → ZMod P.p) := by
  funext j
  simp only [Pt.vec, unitP]
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp only [List.getElem_map, List.getElem_range]
  by_cases h : j = i
  · subst h; simp
  · rw [Pi.single_eq_of_ne h, if_neg (fun hh => h (Fin.ext hh))]
    simp

lemma pxe_foldl_add (l : List ℕ) : l.foldl (· + ·) 0 = l.sum := by
  have h : ∀ a : ℕ, l.foldl (· + ·) a = a + l.sum := by
    induction l with
    | nil => intro a; simp
    | cons x xs ih => intro a; rw [List.foldl_cons, List.sum_cons, ih (a + x), Nat.add_assoc]
  simpa using h 0

lemma pxe_sum_range_cast (p n : ℕ) (f : ℕ → ℕ) :
    ((((List.range n).map f).sum : ℕ) : ZMod p) = ∑ i : Fin n, ((f i.val : ℕ) : ZMod p) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
        Nat.cast_add, ih, Fin.sum_univ_castSucc]
      simp [Fin.val_last]

lemma pxe_cast_mod (p : ℕ) (x : ℕ) : (((x % p : ℕ)) : ZMod p) = (x : ZMod p) := by
  rw [ZMod.natCast_mod]

lemma pxe_dotP_cast (p n : ℕ) (a b : Vec) (ha : a.length = n) (hb : b.length = n) :
    ((dotP p a b : ℕ) : ZMod p) =
      ∑ i : Fin n, ((a.getD i.val 0 : ℕ) : ZMod p) * ((b.getD i.val 0 : ℕ) : ZMod p) := by
  unfold dotP
  rw [show max a.length b.length = n by omega]
  rw [pxe_foldl_add, pxe_cast_mod]
  rw [pxe_sum_range_cast]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring
lemma pxe_cartanRowP_eq (p : ℕ) (hp : p = 5 ∨ p = 7) (i j : Fin (p - 1)) :
    (((cartanRowP p p i.val).getD j.val 0 : ℕ) : ZMod p) = (CartanMatrix.A (p - 1) i j : ZMod p) := by
  rcases hp with rfl | rfl <;> fin_cases i <;> fin_cases j <;> decide

end CFSG.TwoNodeSmall
