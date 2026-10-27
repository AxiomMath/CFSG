module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosExclLemmas

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

lemma pxe_nat_eq_of_cast_eq (p a b : ℕ) (hb : b < p)
    (h : (a : ZMod p) = (b : ZMod p)) : a % p = b := by
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt hb] at hv

lemma pxe_sum_single {p n : ℕ} (a : Fin n → ZMod p) :
    (∑ i : Fin n, a i • (Pi.single i (1 : ZMod p) : Fin n → ZMod p)) = a := by
  funext j
  rw [Finset.sum_apply]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; rw [Pi.single_eq_of_ne (Ne.symm hi), mul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj

lemma pxe_getD_map_range_lit {α : Type} (f : ℕ → α) (d z : α) {n : ℕ} (i : Fin n) :
    (((List.range n).map f) ++ [z]).getD i.val d = f i.val := by
  rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
  rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
  simp

lemma pxe_sum_fin_last {M : Type*} [AddCommMonoid M] (p : ℕ) (hp1 : 1 ≤ p)
    (f : Fin p → M) :
    (∑ j : Fin p, f j) = (∑ k : Fin (p - 1), f ⟨k.val, by omega⟩) + f ⟨p - 1, by omega⟩ := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  rw [Fin.sum_univ_castSucc]
  rfl

lemma pxe_alpha_sum (p : ℕ) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : Fin (p - 1) → V) (α : Fin (p - 1) → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (CartanMatrix.A (p - 1) i j : ZMod p))
    (cc : Fin (p - 1) → ZMod p) (j : Fin (p - 1)) :
    α j (∑ i, cc i • h i) = (pxe_A p (p - 1)).mulVec cc j := by
  have h1 : α j (∑ i, cc i • h i)
      = ∑ i, cc i * (CartanMatrix.A (p - 1) j i : ZMod p) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, hpair j i, smul_eq_mul]
  rw [h1]
  simp only [pxe_A, Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma pxe_cvec_getD (p : ℕ) (cc : Fin (p - 1) → ZMod p) (i : Fin (p - 1)) :
    (List.ofFn (fun i : Fin (p - 1) => (cc i).val)).getD i.val 0 = (cc i).val := by
  rw [List.getD_eq_getElem _ _ (by simp [List.length_ofFn])]
  simp [List.get_ofFn]

lemma pxe_outs_len (p s : ℕ) (hp : p = 5 ∨ p = 7) (hs : s ≤ 2) :
    ((List.range (p - 1)).filter (fun k => !(s ≤ k && k < s + (p - 3)))).length = 2 := by
  rcases hp with rfl | rfl <;> interval_cases s <;> decide

lemma pxe_vv_out (p s : ℕ) (hp : p = 5 ∨ p = 7) (hs : s ≤ 2) (g : ℕ → ℕ) :
    let outs := (List.range (p - 1)).filter (fun k => !(s ≤ k && k < s + (p - 3)))
    let fr := outs.map g
    ∀ k, k < p - 1 → ¬ (s ≤ k ∧ k < s + (p - 3)) →
      (if outs.head? = some k then fr.getD 0 0 else fr.getD 1 0) = g k := by
  rcases hp with rfl | rfl <;> interval_cases s <;>
    (dsimp only; intro k hk hout; interval_cases k <;>
      simp_all [List.filter, List.filter_cons, List.filter_nil, List.range, List.range.loop,
        List.map, Option.map, Option.getD, List.getD, List.head?])

lemma pxe_pi_single_embed (p : ℕ) (hp1 : 1 ≤ p) (a : Fin (p - 1) → ZMod p) :
    (∑ i : Fin (p - 1),
        a i • (Pi.single (⟨i.val, by omega⟩ : Fin p) (1 : ZMod p) : Fin p → ZMod p))
      = fun j : Fin p => if h : j.val < p - 1 then a ⟨j.val, h⟩ else 0 := by
  funext j
  rw [Finset.sum_apply]
  by_cases hj : j.val < p - 1
  · rw [dif_pos hj, Finset.sum_eq_single ⟨j.val, hj⟩]
    · simp
    · intro i _ hi
      rw [Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
      intro hh
      exact hi (Fin.ext (by simpa using (congrArg Fin.val hh).symm))
    · intro hh; exact absurd (Finset.mem_univ _) hh
  · rw [dif_neg hj]
    apply Finset.sum_eq_zero
    intro i _
    rw [Pi.smul_apply, Pi.single_eq_of_ne, smul_zero]
    intro hh
    have hv := congrArg Fin.val hh
    simp only [Fin.val_mk] at hv
    omega

lemma pxe_opt_lt1 (p N : ℕ) (hp : p = 5 ∨ p = 7) (hN : N = p) (o : ℕ × ℕ × ℕ)
    (ho : o ∈ posOpts p N) : o.2.1 < p := by
  subst N
  rcases hp with rfl | rfl <;> revert o <;> decide

end CFSG.TwoNodeSmall
