module

public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.Model
public import CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition.FusionData

public section

namespace CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition

open CFSG.Sporadic.Th

noncomputable def ev (w : List ℤ) : J3Model := wordG letG w

theorem ev_nil : ev [] = 1 := by
  simp [ev, wordG]

theorem ev_cons (l : ℤ) (w : List ℤ) : ev (l :: w) = letG l * ev w := by
  simp [ev, wordG]

theorem ev_append (v w : List ℤ) : ev (v ++ w) = ev v * ev w := by
  simp [ev, wordG, List.map_append, List.prod_append]

theorem letG_neg_succ {k : ℕ} (hk : k < 7) : letG (-((k : ℤ) + 1)) = (letG ((k : ℤ) + 1))⁻¹ := by
  have h1 := lift_letter ⟨k, hk⟩ true
  have h2 := lift_letter ⟨k, hk⟩ false
  simp only [ite_true, Bool.false_eq_true, ite_false] at h1 h2
  rw [← h1, ← h2, ← map_inv, FreeGroup.inv_mk]
  rfl

theorem letG_neg {l : ℤ} (hl : 1 ≤ l.natAbs ∧ l.natAbs ≤ 7) : letG (-l) = (letG l)⁻¹ := by
  rcases lt_or_gt_of_ne (show l ≠ 0 by omega) with h | h
  · obtain ⟨k, hk, hkl⟩ : ∃ k : ℕ, k < 7 ∧ -l = (k : ℤ) + 1 := ⟨(-l - 1).toNat, by omega, by omega⟩
    have := letG_neg_succ hk
    rw [← hkl, neg_neg] at this
    rw [this, inv_inv]
  · obtain ⟨k, hk, hkl⟩ : ∃ k : ℕ, k < 7 ∧ l = (k : ℤ) + 1 := ⟨(l - 1).toNat, by omega, by omega⟩
    rw [hkl]
    exact letG_neg_succ hk

theorem ev_invWordZ {w : List ℤ} (hw : ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 7) :
    ev (invWordZ w) = (ev w)⁻¹ := by
  induction w with
  | nil => simp [ev, wordG, invWordZ]
  | cons l w ih =>
    have ih := ih (fun l' hl' => hw l' (List.mem_cons_of_mem _ hl'))
    have e : invWordZ (l :: w) = invWordZ w ++ [-l] := by simp [invWordZ]
    rw [e, ev_append, ih]
    have : ev [-l] = (letG l)⁻¹ := by simp [ev, wordG, letG_neg (hw l List.mem_cons_self)]
    rw [this, show ev (l :: w) = letG l * ev w by simp [ev, wordG], mul_inv_rev]

theorem invWordZ_letters {w : List ℤ} (hw : ∀ l ∈ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 7) :
    ∀ l ∈ invWordZ w, 1 ≤ l.natAbs ∧ l.natAbs ≤ 7 := by
  intro l hl
  simp only [invWordZ, List.mem_reverse, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  simpa using hw l' hl'

theorem letG_four : letG 4 = uJ 3 := by
  have h := lift_letter (3 : Fin 7) true
  have e : FreeGroup.lift uJ (FreeGroup.mk [((3 : Fin 7), true)]) = uJ 3 := by
    exact FreeGroup.lift_apply_of (f := uJ) (x := (3 : Fin 7)) ▸ rfl
  rw [e] at h
  rw [h]
  norm_num

theorem ev_four : ev [4] = uJ 3 := by
  simp [ev, wordG, letG_four]

theorem ev_pathWord (p : List ℕ) : ev (pathWord p) = (p.map fun j => ev (fusGl.getD j [])).prod := by
  induction p with
  | nil => simp [ev, wordG, pathWord]
  | cons j p ih =>
    have : pathWord (j :: p) = fusGl.getD j [] ++ pathWord p := by simp [pathWord]
    rw [this, ev_append, ih]
    simp

end CFSG.Quasithin.Recognition.Kleidman.AmalgamPresentationRecognition
