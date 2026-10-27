module
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeAMono
@[expose] public section
namespace CFSG.StandardType

theorem ggCartanE₈_ker_zero : ∀ c : Fin 8 → ZMod 3,
    (∀ j, ∑ k, (CartanMatrix.E₈ j k : ZMod 3) * c k = 0) → c = 0 := by
  intro c h
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h7 := h 7
  simp [CartanMatrix.E₈, CartanMatrix.E_eight_eq, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6 h7
  funext k
  simp only [Pi.zero_apply]
  fin_cases k <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
  · linear_combination 4 * h0 + 5 * h1 + 7 * h2 + 10 * h3 + 8 * h4 + 6 * h5 + 4 * h6 + 2 * h7
  · linear_combination 5 * h0 + 8 * h1 + 10 * h2 + 15 * h3 + 12 * h4 + 9 * h5 + 6 * h6 + 3 * h7
  · linear_combination 7 * h0 + 10 * h1 + 14 * h2 + 20 * h3 + 16 * h4 + 12 * h5 + 8 * h6 + 4 * h7
  · linear_combination 10 * h0 + 15 * h1 + 20 * h2 + 30 * h3 + 24 * h4 + 18 * h5 + 12 * h6 + 6 * h7
  · linear_combination 8 * h0 + 12 * h1 + 16 * h2 + 24 * h3 + 20 * h4 + 15 * h5 + 10 * h6 + 5 * h7
  · linear_combination 6 * h0 + 9 * h1 + 12 * h2 + 18 * h3 + 15 * h4 + 12 * h5 + 8 * h6 + 4 * h7
  · linear_combination 4 * h0 + 6 * h1 + 8 * h2 + 12 * h3 + 10 * h4 + 8 * h5 + 6 * h6 + 3 * h7
  · linear_combination 2 * h0 + 3 * h1 + 4 * h2 + 6 * h3 + 5 * h4 + 4 * h5 + 3 * h6 + 2 * h7

theorem ggCartanE₆_ker_coord (c : Fin 6 → ZMod 3)
    (h : ∀ j, ∑ k, (CartanMatrix.E₆ j k : ZMod 3) * c k = 0) :
    ∀ k, c k = (![1, 0, 2, 0, 1, 2] : Fin 6 → ZMod 3) k * c 0 := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  simp [CartanMatrix.E₆, CartanMatrix.E_six_eq, Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
  have e1 : c 1 = 0 * c 0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char)) 2 * h1 + 1 * h4 + 2 * h5
  have e2 : c 2 = 2 * c 0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char)) 2 * h2 + 1 * h4 + 2 * h5
  have e3 : c 3 = 0 * c 0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char)) 2 * h4 + 1 * h5
  have e4 : c 4 = 1 * c 0 := by
    linear_combination (norm := ring_nf) 1 * h1 + 1 * h2 + 2 * h3 + 2 * h4 + 1 * h5
  have e5 : c 5 = 2 * c 0 := by
    linear_combination (norm := (ring_nf; reduce_mod_char))
      2 * h1 + 2 * h2 + 1 * h3 + 1 * h4 + 1 * h5
  intro k
  fin_cases k
  · simp
  · simpa using e1
  · simpa using e2
  · simpa using e3
  · simpa using e4
  · simpa using e5

theorem ggCartanE₆_ker_le_one : ∀ c d : Fin 6 → ZMod 3,
    (∀ j, ∑ k, (CartanMatrix.E₆ j k : ZMod 3) * c k = 0) →
    (∀ j, ∑ k, (CartanMatrix.E₆ j k : ZMod 3) * d k = 0) → c ≠ 0 → ∃ l : ZMod 3, d = l • c := by
  intro c d hc hd hc0
  have ec := ggCartanE₆_ker_coord c hc
  have ed := ggCartanE₆_ker_coord d hd
  have h0 : c 0 ≠ 0 := by
    intro h0
    apply hc0
    funext k
    rw [ec k, h0, mul_zero, Pi.zero_apply]
  refine ⟨d 0 / c 0, ?_⟩
  funext k
  rw [Pi.smul_apply, smul_eq_mul, ec k, ed k]
  field_simp

theorem cartanA_row {p N : ℕ} (c : Fin N → ZMod p) (j : Fin N) :
    ∑ k, (CartanMatrix.A N j k : ZMod p) * c k =
      2 * (fun m => if hm : m < N then c ⟨m, hm⟩ else 0) j.val
        - (fun m => if hm : m < N then c ⟨m, hm⟩ else 0) (j.val + 1)
        - (if j.val = 0 then 0
            else (fun m => if hm : m < N then c ⟨m, hm⟩ else 0) (j.val - 1)) := by
  set c' : ℕ → ZMod p := fun m => if hm : m < N then c ⟨m, hm⟩ else 0 with hc'
  have hpick : ∀ m, ∑ k : Fin N, (if k.val = m then c k else 0) = c' m := by
    intro m
    by_cases hm : m < N
    · rw [Finset.sum_eq_single ⟨m, hm⟩]
      · simp [hc', hm]
      · intro b _ hb
        rw [if_neg]
        intro hbm
        exact hb (Fin.ext hbm)
      · simp
    · rw [Finset.sum_eq_zero]
      · simp [hc', hm]
      · intro b _
        rw [if_neg]
        omega
  have hterm : ∀ k : Fin N, (CartanMatrix.A N j k : ZMod p) * c k =
      2 * (if k.val = j.val then c k else 0) - (if k.val = j.val + 1 then c k else 0)
        - (if j.val = 0 then 0 else (if k.val = j.val - 1 then c k else 0)) := by
    intro k
    simp only [CartanMatrix.A, Matrix.of_apply]
    by_cases hjk : j = k
    · subst hjk
      by_cases hj0 : (j : ℕ) = 0
      · simp [hj0]
      · have hne : ¬ ((j : ℕ) = (j : ℕ) - 1) := by omega
        simp [hj0, hne]
    · have hv : k.val ≠ j.val := fun e => hjk (Fin.ext e.symm)
      rw [if_neg hjk, if_neg hv]
      by_cases h1 : j.val + 1 = k.val ∨ k.val + 1 = j.val
      · rw [if_pos h1]
        rcases h1 with h1 | h1
        · rw [if_pos h1.symm]
          by_cases hj0 : j.val = 0
          · rw [if_pos hj0]; push_cast; ring
          · rw [if_neg hj0, if_neg (by omega)]; push_cast; ring
        · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; push_cast; ring
      · rw [if_neg h1]
        by_cases hj0 : j.val = 0
        · rw [if_pos hj0, if_neg (by omega)]; simp
        · rw [if_neg hj0, if_neg (by omega), if_neg (by omega)]; simp
  rw [Finset.sum_congr rfl (fun k _ => hterm k), Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, hpick, hpick]
  by_cases hj0 : j.val = 0
  · simp [hj0]
  · simp only [if_neg hj0]
    rw [hpick]

theorem cartanA_ker_coord {p N : ℕ} (c : Fin N → ZMod p)
    (h : ∀ j, ∑ k, (CartanMatrix.A N j k : ZMod p) * c k = 0) :
    ∀ i (hi : i < N), c ⟨i, hi⟩ = ((i : ZMod p) + 1) *
      (fun m => if hm : m < N then c ⟨m, hm⟩ else 0) 0 := by
  set c' : ℕ → ZMod p := fun m => if hm : m < N then c ⟨m, hm⟩ else 0 with hc'
  have hrow : ∀ j (hj : j < N), 2 * c' j - c' (j + 1) - (if j = 0 then 0 else c' (j - 1)) = 0 := by
    intro j hj
    have := h ⟨j, hj⟩
    rw [cartanA_row] at this
    exact this
  have key : ∀ i, (i < N → c' i = ((i : ZMod p) + 1) * c' 0) ∧
      (i + 1 < N → c' (i + 1) = ((i : ZMod p) + 2) * c' 0) := by
    intro i
    induction i with
    | zero =>
      refine ⟨fun _ => by simp, fun h1 => ?_⟩
      have := hrow 0 (by omega)
      rw [if_pos rfl] at this
      push_cast
      linear_combination -this
    | succ i ih =>
      refine ⟨fun hi => ?_, fun hi => ?_⟩
      · rw [ih.2 hi]; push_cast; ring
      · have := hrow (i + 1) (by omega)
        simp only [Nat.add_sub_cancel, if_neg (Nat.succ_ne_zero i)] at this
        rw [ih.1 (by omega), ih.2 (by omega)] at this
        push_cast
        linear_combination -this
  intro i hi
  have := (key i).1 hi
  simp only [hc', dif_pos hi] at this
  exact this

theorem ggCartanA_ker_le_one {p N : ℕ} [Fact p.Prime] : ∀ c d : Fin N → ZMod p,
    (∀ j, ∑ k, (CartanMatrix.A N j k : ZMod p) * c k = 0) →
    (∀ j, ∑ k, (CartanMatrix.A N j k : ZMod p) * d k = 0) → c ≠ 0 → ∃ l : ZMod p, d = l • c := by
  intro c d hc hd hc0
  have ec := cartanA_ker_coord c hc
  have ed := cartanA_ker_coord d hd
  set c0 := (fun m => if hm : m < N then c ⟨m, hm⟩ else 0) 0 with hc0'
  set d0 := (fun m => if hm : m < N then d ⟨m, hm⟩ else 0) 0 with hd0'
  have h0 : c0 ≠ 0 := by
    intro h0
    apply hc0
    funext k
    rw [Pi.zero_apply, ec k.val k.isLt, h0, mul_zero]
  refine ⟨d0 / c0, ?_⟩
  funext k
  rw [Pi.smul_apply, smul_eq_mul, ec k.val k.isLt, ed k.val k.isLt]
  field_simp

end CFSG.StandardType
