module

public import Certificates.Data.GH74.LyThreeB
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Intervals

public section

namespace CFSG.Sporadic.Ly

theorem countIn_fold (lo : ℕ) (f : ℕ → Bool) (m : ℕ) :
    Nat.fold m (fun k _ acc => if f (lo + k) then acc + 1 else acc) 0 =
      ((Finset.Ico lo (lo + m)).filter (fun i => f i = true)).card := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hlo : lo + (m + 1) = lo + m + 1 := rfl
    rw [Nat.fold_succ, ih, Finset.card_filter, Finset.card_filter, hlo,
      Finset.sum_Ico_succ_top (Nat.le_add_right lo m)]
    by_cases h : f (lo + m) = true <;> simp [h]

theorem countIn_eq (lo hi : ℕ) (f : ℕ → Bool) :
    ThreeB.countIn lo hi f = ((Finset.Ico lo hi).filter (fun i => f i = true)).card := by
  unfold ThreeB.countIn
  rw [countIn_fold]
  rcases le_total lo hi with h | h
  · rw [Nat.add_sub_cancel' h]
  · rw [Nat.sub_eq_zero_of_le h]
    simp [Finset.Ico_eq_empty_of_le h]

theorem foldl_range_add (g : ℕ → ℕ) (N : ℕ) :
    (List.range N).foldl (fun a j => a + g j) 0 = ∑ j ∈ Finset.range N, g j := by
  induction N with
  | zero => simp
  | succ N ih => rw [List.range_succ, List.foldl_append, ih, Finset.sum_range_succ]; rfl

theorem countBlocks_eq (n b : ℕ) (f : ℕ → Bool) :
    ThreeB.countBlocks n b f =
      ∑ j ∈ Finset.range ((n + b - 1) / b), ThreeB.countIn (j * b) (min n ((j + 1) * b)) f := by
  unfold ThreeB.countBlocks
  rw [List.foldl_map]
  exact foldl_range_add (fun j => ThreeB.countIn (j * b) (min n ((j + 1) * b)) f) _

theorem ncard_le_card_range {n : ℕ} (f : ℕ → Bool) :
    {p : Fin n | f p.val = true}.ncard ≤ ((Finset.range n).filter (fun i => f i = true)).card := by
  rw [← Set.ncard_coe_finset]
  refine Set.ncard_le_ncard_of_injOn Fin.val (fun p hp => ?_) Fin.val_injective.injOn
    (Finset.finite_toSet _)
  simp only [Set.mem_ofPred_eq] at hp
  simp only [Finset.coe_filter, Finset.mem_range, Set.mem_ofPred_eq]
  exact ⟨p.isLt, hp⟩

theorem card_filter_range_le {n b : ℕ} (hb : 0 < b) (f : ℕ → Bool) :
    ((Finset.range n).filter (fun i => f i = true)).card ≤
      ∑ j ∈ Finset.range ((n + b - 1) / b),
        ((Finset.Ico (j * b) (min n ((j + 1) * b))).filter (fun i => f i = true)).card := by
  refine le_trans (Finset.card_le_card ?_) Finset.card_biUnion_le
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_filter, Finset.mem_Ico]
  have h1 := Nat.div_mul_le_self i b
  have h2 := Nat.lt_div_mul_add (a := i) hb
  have h3 : (i / b + 1) * b = i / b * b + b := by rw [Nat.add_mul, Nat.one_mul]
  refine ⟨i / b, ?_, ⟨h1, ?_⟩, hi.2⟩
  · apply Nat.lt_of_succ_le
    rw [Nat.succ_eq_add_one, Nat.le_div_iff_mul_le hb, h3]
    omega
  · rw [h3]
    omega

theorem ncard_le_countBlocks {n b : ℕ} (hb : 0 < b) (f : ℕ → Bool) :
    {p : Fin n | f p.val = true}.ncard ≤ ThreeB.countBlocks n b f := by
  rw [countBlocks_eq]
  simp only [countIn_eq]
  exact (ncard_le_card_range f).trans (card_filter_range_le hb f)

end CFSG.Sporadic.Ly
